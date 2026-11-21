#include "QCIRParser.h"

#include <fstream>
#include <sstream>
#include <iostream>
#include <assert.h>
#include <algorithm>
#include <cstdlib>
#include <utility>

using std::make_tuple;

std::string str_tolower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(), 
                   [](unsigned char c){ return std::tolower(c); }
                  );
    return s;
}

QCIRParser::QCIRParser() {};

[[noreturn]] static void parseError(const string& message) {
  std::cerr << "QCIR parse error: " << message << std::endl;
  exit(1);
}

// Splits "keyword(arg1,arg2,...)" (without whitespace) into the part before the opening
// parenthesis and the argument string.
static void splitCall(const string& line, string& head, string& arguments) {
  auto opening_pos = line.find('(');
  if (opening_pos == string::npos || line.back() != ')') {
    parseError("malformed line '" + line + "'");
  }
  head = line.substr(0, opening_pos);
  arguments = line.substr(opening_pos + 1, line.size() - opening_pos - 2);
}

static string negateLiteral(const string& literal) {
  return literal.front() == '-' ? literal.substr(1) : "-" + literal;
}

QCIRParser::QCIRParser(const string& filename) {
  std::ifstream file(filename.c_str());
  if (!file) {
    parseError("could not open file '" + filename + "'");
  }
  string line, head, arguments;
  while (std::getline(file, line)) {
    line.erase(remove_if(line.begin(), line.end(), [] (char c) { return isspace(int(c)); }), line.end()); // Remove whitespaces.
    if (line.length() == 0 || line.front() == '#') {
      continue;
    }
    splitCall(line, head, arguments);
    auto equals_pos = head.find('=');
    if (equals_pos != string::npos) {
      readGate(head.substr(0, equals_pos), str_tolower(head.substr(equals_pos + 1)), arguments);
    } else {
      // Keywords are case-insensitive, identifiers are not.
      head = str_tolower(head);
      if (head == QBFParser::FORALL_STRING) {
        readQuantifierBlock(VariableType::Universal, arguments);
      } else if (head == QBFParser::EXISTS_STRING || head == "free") {
        // Free variables are treated as outermost existential variables.
        readQuantifierBlock(VariableType::Existential, arguments);
      } else if (head == QBFParser::OUTPUT_STRING) {
        readOutput(arguments);
      } else {
        parseError("malformed line '" + line + "'");
      }
    }
  }
  if (output_id.empty() || id_to_alias.find(output_id) == id_to_alias.end()) {
    parseError("missing or undefined output gate");
  }
  for (unsigned int i = 1; i < gates.size(); i++) {
    if (gates[i].gate_type == GateType::None) {
      parseError("'" + gates[i].gate_id + "' is neither a quantified variable nor a gate");
    }
  }
  std::cerr << "Done parsing " << gates.size() << " gates." << std::endl;

  /* Remove redundant gates (optional). */
  std::cerr << "Removed " << removeRedundant() << " redundant gates." << std::endl;
  getGatePolarities(polarities, output_negated ? GatePolarity::Negative : GatePolarity::Positive);
}

void QCIRParser::readQuantifierBlock(VariableType type, const string& variables_string) {
  if (gates.size() > (unsigned int) variable_gate_boundary) {
    parseError("quantifier block after gate definitions (only prenex formulas are supported)");
  }
  // Merge adjacent blocks of the same type.
  if (quantifier_blocks.empty() ||
      (gates[quantifier_blocks.back().front()].gate_type == GateType::Existential) != (type == VariableType::Existential)) {
    quantifier_blocks.emplace_back();
  }
  for (auto& v: split(variables_string, ',')) {
    if (id_to_alias.find(v) != id_to_alias.end()) {
      parseError("variable '" + v + "' quantified more than once");
    }
    addVariable(v, type);
  }
  if (quantifier_blocks.back().empty()) {
    quantifier_blocks.pop_back();
  }
}

// Defines a gate and assigns it the next gate number (used in proofs).
void QCIRParser::defineGate(const string& gate_id, GateType gate_type, const vector<string>& input_literals) {
  addGate(gate_id, gate_type, input_literals);
  gate_number[id_to_alias[gate_id]] = gate_number.size() + 1;
}

void QCIRParser::readGate(const string& gate_id, const string& gate_type_string, const string& gate_inputs_string) {
  auto input_literals = split(gate_inputs_string, ',');
  auto known_gate = id_to_alias.find(gate_id);
  if (gate_id.empty() || (known_gate != id_to_alias.end() && gates[known_gate->second].gate_type != GateType::None)) {
    parseError("gate '" + gate_id + "' is empty or defined more than once");
  }
  for (auto& literal: input_literals) {
    if (literal.empty() || literal == "-") {
      parseError("empty input of gate '" + gate_id + "'");
    }
  }
  if (gate_type_string == QBFParser::AND_STRING) {
    defineGate(gate_id, GateType::And, input_literals);
  } else if (gate_type_string == QBFParser::OR_STRING) {
    defineGate(gate_id, GateType::Or, input_literals);
  } else if (gate_type_string == "xor" && input_literals.size() == 2) {
    // xor(a, b) = or(and(a, -b), and(-a, b)). Auxiliary gate names cannot clash with identifiers.
    auto& a = input_literals[0];
    auto& b = input_literals[1];
    defineGate(gate_id + "#1", GateType::And, {a, negateLiteral(b)});
    defineGate(gate_id + "#2", GateType::And, {negateLiteral(a), b});
    defineGate(gate_id, GateType::Or, {gate_id + "#1", gate_id + "#2"});
  } else if (gate_type_string == "ite" && input_literals.size() == 3) {
    // ite(c, a, b) = or(and(c, a), and(-c, b)).
    auto& c = input_literals[0];
    defineGate(gate_id + "#1", GateType::And, {c, input_literals[1]});
    defineGate(gate_id + "#2", GateType::And, {negateLiteral(c), input_literals[2]});
    defineGate(gate_id, GateType::Or, {gate_id + "#1", gate_id + "#2"});
  } else {
    parseError("unsupported gate '" + gate_id + " = " + gate_type_string + "(...)' with " + std::to_string(input_literals.size()) + " inputs");
  }
}

void QCIRParser::readOutput(const string& output_lit_str) {
  if (output_lit_str.empty() || output_lit_str == "-" || !output_id.empty()) {
    parseError("malformed or repeated output statement");
  }
  output_negated = (output_lit_str.front() == '-');
  output_id = output_negated ? output_lit_str.substr(1) : output_lit_str;
}

// Computes, for each gate, the depth of the innermost quantifier block containing a variable
// the gate depends on (-1 for gates that do not depend on any variable).
std::vector<int> QCIRParser::getGateDepths() const {
  std::vector<int> depth(gates.size(), -1);
  std::vector<char> done(gates.size(), false);
  std::vector<std::pair<int, unsigned int>> stack; // (alias, index of next input to visit)
  for (int i = 1; i < variable_gate_boundary; i++) {
    depth[i] = gates[i].variable_depth;
    done[i] = true;
  }
  for (unsigned int root = variable_gate_boundary; root < gates.size(); root++) {
    if (done[root]) {
      continue;
    }
    stack.emplace_back(root, 0);
    done[root] = true; // Also guards against cyclic definitions.
    while (!stack.empty()) {
      int alias = stack.back().first;
      const Gate& gate = gates[alias];
      if (stack.back().second < gate.nr_inputs) {
        int input = abs(gate.gate_inputs[stack.back().second++]);
        if (!done[input]) {
          done[input] = true;
          stack.emplace_back(input, 0);
        }
      } else {
        for (unsigned int j = 0; j < gate.nr_inputs; j++) {
          depth[alias] = std::max(depth[alias], depth[abs(gate.gate_inputs[j])]);
        }
        stack.pop_back();
      }
    }
  }
  return depth;
}

void QCIRParser::initSolver(Minisat::Solver& solver, bool early_tseitin) {
  // Each gate is represented by two Tseitin variables: an existential one that is used in
  // clauses, and a universal one that is used in terms. They are never used as decision
  // variables.
  //
  // The value of a gate is a function of the variables it depends on, so its Tseitin variables
  // can be quantified right after the innermost quantifier block containing such a variable,
  // rather than after all variables. This allows for more universal/existential reduction, and in
  // turn shorter learnt constraints and cheaper conflict analysis.
  const int nr_blocks = quantifier_blocks.size();
  std::vector<std::vector<int>> gates_at_depth(nr_blocks + 1); // Shifted by one, for gates without variables.
  if (early_tseitin) {
    auto gate_depth = getGateDepths();
    for (unsigned int i = variable_gate_boundary; i < gates.size(); i++) {
      gates_at_depth[gate_depth[i] + 1].push_back(i);
    }
  } else {
    for (unsigned int i = variable_gate_boundary; i < gates.size(); i++) {
      gates_at_depth[nr_blocks].push_back(i);
    }
  }

  // The prefix as a sequence of groups of variables. Adjacent groups of the same type end up in
  // the same quantifier block of the solver.
  struct Group {
    bool existential;
    bool tseitin;
    const std::vector<int>* aliases;
  };
  std::vector<Group> groups;
  auto blockIsExistential = [&](int depth) {
    return gates[quantifier_blocks[depth][0]].gate_type == GateType::Existential;
  };
  auto addTseitinGroups = [&](const std::vector<int>& gate_aliases, bool first_existential) {
    groups.push_back({first_existential, true, &gate_aliases});
    groups.push_back({!first_existential, true, &gate_aliases});
  };
  addTseitinGroups(gates_at_depth[0], nr_blocks > 0 && !blockIsExistential(0));
  for (int depth = 0; depth < nr_blocks; depth++) {
    groups.push_back({blockIsExistential(depth), false, &quantifier_blocks[depth]});
    addTseitinGroups(gates_at_depth[depth + 1], blockIsExistential(depth));
  }

  // Create the variables in the order of the prefix.
  std::unordered_map<int, Minisat::Var> gate_alias_to_tseitin_universal;
  std::unordered_map<int, Minisat::Var> gate_alias_to_tseitin_existential;
  Minisat::vec<Minisat::Var> block;
  bool block_is_existential = false;
  int solver_depth = 0;
  auto finishBlock = [&]() {
    if (block.size() > 0) {
      solver.addQuantifierBlock(block, block_is_existential);
      block.clear();
      solver_depth++;
    }
  };
  for (auto& group: groups) {
    if (group.aliases->empty()) {
      continue;
    }
    if (group.existential != block_is_existential) {
      finishBlock();
      block_is_existential = group.existential;
    }
    for (auto alias: *group.aliases) {
      Minisat::Var solver_var;
      if (!group.tseitin) {
        solver_var = solver.newVar(alias);
        gate_alias_to_tseitin_universal[alias] = solver_var;
        gate_alias_to_tseitin_existential[alias] = solver_var;
      } else if (group.existential) {
        solver_var = solver.newVar(alias*2, Minisat::l_Undef, false);
        gate_alias_to_tseitin_existential[alias] = solver_var;
      } else {
        solver_var = solver.newVar(alias*2+1, Minisat::l_Undef, false);
        gate_alias_to_tseitin_universal[alias] = solver_var;
      }
      solver.setVarType(solver_var, group.existential, solver_depth);
      // In proofs, variables are numbered in the order of the prefix, followed by the gates in
      // the order of their definitions.
      solver.setProofVar(solver_var, group.tseitin ? variable_gate_boundary - 1 + gate_number.at(alias) : alias);
      block.push(solver_var);
    }
  }
  finishBlock();

  // Add the clauses and terms encoding each gate, followed by the output.
  auto addConstraints = [&](const std::vector<std::vector<int>>& constraints, bool terms, int proof_gate) {
    auto& alias_to_var = terms ? gate_alias_to_tseitin_universal : gate_alias_to_tseitin_existential;
    for (auto& constraint: constraints) {
      Minisat::vec<Minisat::Lit> lits;
      for (auto l: constraint) {
        lits.push(Minisat::mkLit(alias_to_var[abs(l)], l < 0));
      }
      if (terms) {
        solver.addTerm(lits, proof_gate);
      } else {
        solver.addClauseInternal(lits, proof_gate);
      }
    }
  };
  auto output_alias = id_to_alias[output_id];
  for (bool terms: {false, true}) {
    for (unsigned int i = variable_gate_boundary; i < gates.size(); i++) {
      if (gates[i].gate_type == GateType::And || gates[i].gate_type == GateType::Or) {
        addConstraints(getClausalEncoding(i, terms), terms, variable_gate_boundary - 1 + gate_number.at(i));
      }
    }
    addConstraints({{output_negated ? -output_alias : output_alias}}, terms, 0);
  }
}

string QCIRParser::getOriginalName(int alias) const {
  return gates.at(alias).gate_id;
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
