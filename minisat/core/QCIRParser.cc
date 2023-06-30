#include "QCIRParser.h"

#include <fstream>
#include <sstream>
#include <iostream>
#include <assert.h>
#include <algorithm>

using std::make_tuple;

std::string str_tolower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(), 
                   [](unsigned char c){ return std::tolower(c); }
                  );
    return s;
}

QCIRParser::QCIRParser() {};

QCIRParser::QCIRParser(const string& filename) {
  std::ifstream file(filename.c_str());
  string line;
  while (std::getline(file, line)) {
    line = str_tolower(line);
    line.erase(remove_if(line.begin(), line.end(), [] (char c) { return isspace(int(c)); }), line.end()); // Remove whitespaces.
    if (line.length() == 0 || line.front() == '#') {
      continue;
    } else if (startsWith(line, QBFParser::FORALL_STRING) || startsWith(line, QBFParser::EXISTS_STRING)) {
      readQuantifierBlock(line);
    } else if (startsWith(line, QBFParser::OUTPUT_STRING)) {
      readOutput(line);
    } else {
      readGate(line);
    }
  }
  assert(output_id.size());
  assert(id_to_alias.find(output_id) != id_to_alias.end());
  std::cout << "Done parsing " << gates.size() << " gates." << std::endl;

  /* Remove redundant gates (optional). */
  std::cerr << "Removed " << removeRedundant() << " redundant gates." << std::endl;
  getGatePolarities(polarities, output_negated ? GatePolarity::Negative : GatePolarity::Positive);
}

void QCIRParser::readQuantifierBlock(const string& line) {
  quantifier_blocks.emplace_back();
  assert(line.back() == ')');
  auto opening_pos = line.find('(');
  assert(opening_pos != string::npos);
  auto quantifier_string = line.substr(0, opening_pos);
  VariableType type = (quantifier_string == QBFParser::EXISTS_STRING) ? VariableType::Existential : VariableType::Universal;
  auto variables_string = line.substr(opening_pos + 1, line.size() - opening_pos  - 2);
  for (auto& v: split(variables_string, ',')) {
    addVariable(v, type);
  }
}

void QCIRParser::readGate(const string& line) {
  assert(line.back() == ')');
  auto equals_pos = line.find('=');
  assert(equals_pos != string::npos);
  auto opening_pos = line.find('(');
  assert(opening_pos != string::npos);
  auto gate_type_string = line.substr(equals_pos + 1, opening_pos - equals_pos - 1);
  auto gate_id = line.substr(0, equals_pos);
  assert(gate_type_string == QBFParser::AND_STRING || gate_type_string == QBFParser::OR_STRING);
  GateType gate_type = (gate_type_string == QBFParser::AND_STRING) ? GateType::And : GateType::Or;
  auto gate_inputs_string = line.substr(opening_pos + 1, line.length() - opening_pos - 2);
  auto input_literals = split(gate_inputs_string, ',');
  addGate(gate_id, gate_type, input_literals);
}

void QCIRParser::readOutput(const string& line) {
  assert(line.back() == ')');
  auto opening_pos = line.find('(');
  assert(opening_pos == QBFParser::OUTPUT_STRING.size());
  auto output_lit_str = line.substr(opening_pos + 1, line.length() - opening_pos - 2);
  output_negated = (output_lit_str.front() == '-');
  output_id = output_negated ? output_lit_str.substr(1) : output_lit_str;
}

void QCIRParser::initSolver(Minisat::Solver& solver) {
  std::unordered_map<int, Minisat::Var> alias_to_solver_internal;
  for (int i = 1; i < variable_gate_boundary; i++) {
    const Gate& g = gates[i];
    bool is_existential = (g.gate_type == GateType::Existential);
    auto solver_var = solver.newVar(i);
    alias_to_solver_internal[i] = solver_var;
    solver.setVarType(solver_var, is_existential, g.variable_depth);
  }
  for (unsigned int i = 0; i < quantifier_blocks.size(); i++) {
    Minisat::vec<Minisat::Var> block;
    for (auto v: quantifier_blocks[i]) {
      block.push(alias_to_solver_internal[v]);
    }
    assert(block.size());
    bool is_existential = (gates[quantifier_blocks[i][0]].gate_type == GateType::Existential);
    solver.addQuantifierBlock(block, is_existential);
  }
  std::unordered_map<int, Minisat::Var> gate_alias_to_tseitin_universal;
  std::unordered_map<int, Minisat::Var> gate_alias_to_tseitin_existential;
  Minisat::vec<Minisat::Var> tseitin_block_universal;
  Minisat::vec<Minisat::Var> tseitin_block_existential;

  // Create innermost quantifier blocks for Tseitin variables.
  for (unsigned int i = variable_gate_boundary; i < gates.size(); i++) {
    auto tseitin_var_universal = solver.newVar(i*2+1, Minisat::l_Undef, false);
    gate_alias_to_tseitin_universal[i] = tseitin_var_universal;
    tseitin_block_universal.push(tseitin_var_universal);
    auto tseitin_var_existential = solver.newVar(i*2, Minisat::l_Undef, false);
    gate_alias_to_tseitin_existential[i] = tseitin_var_existential;
    tseitin_block_existential.push(tseitin_var_existential);
    solver.setVarType(tseitin_var_universal, false, quantifier_blocks.size());
    solver.setVarType(tseitin_var_existential, true, quantifier_blocks.size() + 1);
  }
  solver.addQuantifierBlock(tseitin_block_universal, false);
  solver.addQuantifierBlock(tseitin_block_existential, true);
  gate_alias_to_tseitin_existential.insert(alias_to_solver_internal.begin(), alias_to_solver_internal.end());
  gate_alias_to_tseitin_universal.insert(alias_to_solver_internal.begin(), alias_to_solver_internal.end());

  auto clauses_pre = getClausalEncoding(false);
  auto terms_pre = getClausalEncoding(true);

  mapFormula(clauses_pre, gate_alias_to_tseitin_existential, false);
  mapFormula(terms_pre, gate_alias_to_tseitin_universal, true);

  Preprocessor pre(clauses_pre, terms_pre);

  pre.preprocess();
  auto [clauses, terms] = pre.getClausesTerms();

  if (clauses.empty()) {
    terms.emplace_back();
  } else if (terms.empty()) {
    clauses.emplace_back();
  }

  for (auto& clause: clauses) {
    Minisat::vec<Minisat::Lit> minisat_clause;
    for (auto l: clause) {
      int v = abs(l) / 2 - 1;
      bool negated = (l < 0);
      minisat_clause.push(Minisat::mkLit(v, negated));
    }
    solver.addClauseInternal(minisat_clause);
  }

  for (auto& term: terms) {
    Minisat::vec<Minisat::Lit> minisat_term;
    for (auto l: term) {
      int v = abs(l) / 2 - 1;
      bool negated = (l < 0);
      minisat_term.push(Minisat::mkLit(v, negated));
    }
    solver.addTerm(minisat_term);
  }
}

string QCIRParser::getOriginalName(int alias) const {
  return gates.at(alias).gate_id;
}

std::vector<std::vector<int>> QCIRParser::getClausalEncoding(bool get_terms) {
  std::vector<std::vector<int>> clauses;
  for (unsigned int i = variable_gate_boundary; i < gates.size(); i++) {
    auto& gate = gates[i];
    if (gate.gate_type == GateType::And || gate.gate_type == GateType::Or) {
      auto gate_clauses = getClausalEncoding(i, get_terms);
      clauses.insert(clauses.end(), gate_clauses.begin(), gate_clauses.end());
    }
  }
  // Output term.
  auto output_alias = id_to_alias[output_id];
  clauses.push_back( {output_negated ? -output_alias : output_alias});
  return clauses;
}

std::vector<std::vector<int>> QCIRParser::getClausalEncoding(int gate_alias, bool get_terms) {
  std::vector<std::vector<int>> clauses;
  auto& gate = gates[gate_alias];
  assert(gate.gate_type == GateType::And || gate.gate_type == GateType::Or);
  bool modifier = get_terms ^ gate.gate_type == GateType::Or;
  int sign = modifier ? -1: 1;
  std::vector<int> small_clause, long_clause;
  small_clause.push_back(-gate_alias * sign);
  long_clause.push_back(gate_alias * sign);
  for (unsigned int j = 0; j < gate.nr_inputs; j++) {
    int l = gate.gate_inputs[j];
    small_clause.push_back(l * sign);
    if (polarities[gate_alias] != (modifier ? GatePolarity::Positive : GatePolarity::Negative)) {
      clauses.push_back(small_clause);
    }
    small_clause.pop_back(); // Remove l.
    long_clause.push_back(-l * sign);
  }
  if (polarities[gate_alias] != (modifier ? GatePolarity::Negative : GatePolarity::Positive)) {
    clauses.push_back(long_clause);
  }
  return clauses;
}

 void QCIRParser::mapFormula(std::vector<std::vector<int>>& formula, const std::unordered_map<int, Minisat::Var>& var_map, bool ctype) {
   for (auto& c: formula) {
     for (auto& l: c) {
       auto v = abs(l);
       bool is_universal = (v < variable_gate_boundary && gates[v].gate_type == GateType::Universal) || (variable_gate_boundary <= v && ctype);
       int w = (var_map.at(v) + 1) * 2 + is_universal;
       l = (l > 0) ? w: -w;
     }
   }
 }
