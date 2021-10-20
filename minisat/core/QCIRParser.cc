#include "QCIRParser.h"

#include <fstream>
#include <sstream>
#include <iostream>
#include <assert.h>
#include <algorithm>

using std::make_tuple;

QCIRParser::QCIRParser() {};

QCIRParser::QCIRParser(const string& filename) {
  std::ifstream file(filename.c_str());
  string line;
  while (std::getline(file, line)) {
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
  std::cerr << "Done parsing " << gates.size() << " gates." << std::endl;

  /* Remove redundant gates (optional). */
  std::cerr << "Removed " << removeRedundant() << " redundant gates." << std::endl;
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
  output_id = line.substr(opening_pos + 1, line.length() - opening_pos - 2);
}

void QCIRParser::initSolver(Minisat::Solver& solver) {
  removeRedundant();
  std::unordered_map<int, Minisat::Var> alias_to_solver_internal;
  for (unsigned i = 1; i < variable_gate_boundary; i++) {
    Gate& g = gates[i];
    bool is_existential = (g.gate_type == GateType::Existential);
    auto solver_var = solver.newVar(i);
    alias_to_solver_internal[i] = solver_var;
    solver.setVarType(solver_var, is_existential, g.variable_depth);
  }
  for (unsigned i = 0; i < quantifier_blocks.size(); i++) {
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
  for (unsigned i = variable_gate_boundary; i < gates.size(); i++) {
    auto& gate = gates[i];
    auto tseitin_var_universal = solver.newVar(i*2+1);
    gate_alias_to_tseitin_universal[i] = tseitin_var_universal;
    tseitin_block_universal.push(tseitin_var_universal);
    auto tseitin_var_existential = solver.newVar(i*2);
    gate_alias_to_tseitin_existential[i] = tseitin_var_existential;
    tseitin_block_existential.push(tseitin_var_existential);
    solver.setVarType(tseitin_var_universal, false, quantifier_blocks.size());
    solver.setVarType(tseitin_var_existential, true, quantifier_blocks.size() + 1);
  }
  solver.addQuantifierBlock(tseitin_block_universal, false);
  solver.addQuantifierBlock(tseitin_block_existential, true);
  gate_alias_to_tseitin_existential.insert(alias_to_solver_internal.begin(), alias_to_solver_internal.end());
  gate_alias_to_tseitin_universal.insert(alias_to_solver_internal.begin(), alias_to_solver_internal.end());
  // TODO: Compute gate polarities for Plaisted-Greenbaum encoding.
  for (unsigned i = variable_gate_boundary; i < gates.size(); i++) {
    auto& gate = gates[i];
    if (gate.gate_type == GateType::And) {
      // Clauses.
      Minisat::vec<Minisat::Lit> small_clause;
      Minisat::vec<Minisat::Lit> long_clause;
      small_clause.push(~Minisat::mkLit(gate_alias_to_tseitin_existential[i], false));
      long_clause.push(Minisat::mkLit(gate_alias_to_tseitin_existential[i], false));
      for (int j = 0; j < gate.nr_inputs; j++) {
        int l = gate.gate_inputs[j];
        int v = abs(l);
        bool negated = (l < 0);
        small_clause.push(Minisat::mkLit(gate_alias_to_tseitin_existential[v], negated));
        solver.addClauseInternal(small_clause);
        small_clause.pop();
        long_clause.push(~Minisat::mkLit(gate_alias_to_tseitin_existential[v], negated));
      }
      solver.addClauseInternal(long_clause);
      // Terms.
      Minisat::vec<Minisat::Lit> small_term;
      Minisat::vec<Minisat::Lit> long_term;
      small_term.push(Minisat::mkLit(gate_alias_to_tseitin_universal[i], false));
      long_term.push(~Minisat::mkLit(gate_alias_to_tseitin_universal[i], false));
      for (int j = 0; j < gate.nr_inputs; j++) {
        int l = gate.gate_inputs[j];
        int v = abs(l);
        bool negated = (l < 0);
        small_term.push(~Minisat::mkLit(gate_alias_to_tseitin_universal[v], negated));
        solver.addTerm(small_term);
        small_term.pop();
        long_term.push(Minisat::mkLit(gate_alias_to_tseitin_universal[v], negated));
      }
      solver.addTerm(long_term);
    } else {
      assert(gate.gate_type == GateType::Or);
      // Clauses.
      Minisat::vec<Minisat::Lit> small_clause;
      Minisat::vec<Minisat::Lit> long_clause;
      small_clause.push(Minisat::mkLit(gate_alias_to_tseitin_existential[i], false));
      long_clause.push(~Minisat::mkLit(gate_alias_to_tseitin_existential[i], false));
      for (int j = 0; j < gate.nr_inputs; j++) {
        int l = gate.gate_inputs[j];
        int v = abs(l);
        bool negated = (l < 0);
        small_clause.push(~Minisat::mkLit(gate_alias_to_tseitin_existential[v], negated));
        solver.addClauseInternal(small_clause);
        small_clause.pop();
        long_clause.push(Minisat::mkLit(gate_alias_to_tseitin_existential[v], negated));
      }
      solver.addClauseInternal(long_clause);
      // Terms.
      Minisat::vec<Minisat::Lit> small_term;
      Minisat::vec<Minisat::Lit> long_term;
      small_term.push(~Minisat::mkLit(gate_alias_to_tseitin_universal[i], false));
      long_term.push(Minisat::mkLit(gate_alias_to_tseitin_universal[i], false));
      for (int j = 0; j < gate.nr_inputs; j++) {
        int l = gate.gate_inputs[j];
        int v = abs(l);
        bool negated = (l < 0);
        small_term.push(Minisat::mkLit(gate_alias_to_tseitin_universal[v], negated));
        solver.addTerm(small_term);
        small_term.pop();
        long_term.push(~Minisat::mkLit(gate_alias_to_tseitin_universal[v], negated));
      }
      solver.addTerm(long_term);
    }
  }
  // Output term.
  auto output_alias = id_to_alias[output_id];
  Minisat::vec<Minisat::Lit> ps;
  ps.push(Minisat::mkLit(gate_alias_to_tseitin_universal[output_alias], false));
  solver.addTerm(ps);
  // Output clause.
  ps.clear();
  ps.push(Minisat::mkLit(gate_alias_to_tseitin_existential[output_alias], false));
  solver.addClauseInternal(ps);
}
