#include "Preprocessor.h"

#include <algorithm>
#include <iostream>

#include <assert.h>

Preprocessor::Preprocessor(const CDNF_formula& clauses, const CDNF_formula& terms): qhead(0), maxvar(0), empty_seen(false), nr_constraints{0, 0}, nr_units(0), nr_pure(0), nr_blocked(0), nr_literals_reduced(0), nr_self_subsumed(0), nr_subsumed(0), nr_eliminated(0) {
  // Store each clause and term as a set of literals.
  for (const auto& clause: clauses) {
    addConstraint(clause, false);
    auto max_var_it = std::max_element(clause.begin(), clause.end(), [](int l1, int l2) { return abs(l1) < abs(l2) || (abs(l1) == abs(l2) && l1 < l2); });
    maxvar = std::max(maxvar, abs(*max_var_it));
    touchAll(clause, false);
  }
  for (const auto& term: terms) {
    addConstraint(term, true);
    auto max_var_it = std::max_element(term.begin(), term.end(), [](int l1, int l2) { return abs(l1) < abs(l2) || (abs(l1) == abs(l2) && l1 < l2); });
    maxvar = std::max(maxvar, abs(*max_var_it));
    touchAll(term, true);
  }
  assigned.resize(maxvar);
  std::fill(assigned.begin(), assigned.end(), false);
  seen.resize(2*maxvar);
  std::fill(seen.begin(), seen.end(), false);
}

void Preprocessor::preprocess() {
  try {
    do {
      findUnits();
      findPure();
      propagate();
      strengthenSelfSubsumed();
      removeSubsumed();
      added.clear();
      removeBlocked();
      boundedVariableElimination();
    } while (!added.empty() || !strengthened.empty() || !touched_for_BCE.empty());
  } catch (bool ctype) {
    // Empty clause/term detected during propagation.
    index_to_lits[ctype].clear();
    index_to_lits[!ctype].clear();
    index_to_lits[ctype][0] = {};
    std::cout << "Formula solved by preprocessing." << std::endl;
  }
  std::cout << "Propagated " << nr_units << " unit and " << nr_pure << " pure literals." << std::endl;
  std::cout << "Removed " << nr_literals_reduced << " literals by existential/universal reduction." << std::endl;
  std::cout << "Strengthened " << nr_self_subsumed << " clauses and terms by self-subsumption." << std::endl;
  std::cout << "Removed " << nr_subsumed << " subsumed clauses or terms" << std::endl;
  std::cout << "Removed " << nr_blocked << " blocked clauses and terms." << std::endl;
  std::cout << "Eliminated " << nr_eliminated << " variables." << std::endl;
  std::cout << "==================================================================================" << std::endl;
}

std::pair<CDNF_formula, CDNF_formula> Preprocessor::getClausesTerms() {
  CDNF_formula clauses, terms;
  for (const auto& [_, clause]: index_to_lits[false]) {
    clauses.emplace_back(clause.begin(), clause.end());
    assert(empty_seen || clauses.back().size() != 1);
  }
  for (const auto& [_, term]: index_to_lits[true]) {
    terms.emplace_back(term.begin(), term.end());
    assert(empty_seen || terms.back().size() != 1);
  }
  return std::make_pair(clauses, terms);
}

void Preprocessor::addConstraint(const std::vector<int>& c, bool ctype) {
  auto c_copy = c;
  std::sort(c_copy.begin(), c_copy.end(), [](const int l1, const int l2) { return abs(l1) < abs(l2); });
  auto index = nr_constraints[ctype]++;
  index_to_lits[ctype][index] = c_copy;
  added.insert(std::make_pair(index, ctype));
  for (auto l: c_copy) {
    lit_to_occurrences[ctype][l].insert(index);
  }
}

void Preprocessor::removeConstraint(int index, bool ctype, bool check_pure) {
  assert(index_to_lits[ctype].find(index) != index_to_lits[ctype].end());
  touchAll(index_to_lits[ctype][index], ctype);
  for (const auto& l: index_to_lits[ctype][index]) {
    lit_to_occurrences[ctype][l].erase(index);
    if (check_pure && lit_to_occurrences[ctype][l].empty() && isPure(-l)) {
      nr_pure += enqueue(isUniversal(abs(l)) ? l: -l);
    }
  }
  index_to_lits[ctype].erase(index);
}

bool Preprocessor::removeLit(int index, int l, bool ctype) {
  assert(index_to_lits[ctype].find(index) != index_to_lits[ctype].end());
  auto& c = index_to_lits[ctype][index];
  touchAll(c, ctype);
  auto it = std::find(c.begin(), c.end(), l);
  assert(it != c.end());
  c.erase(it);
  reduce(index, ctype);
  if (c.empty()) {
    return true;
  } else if (c.size() == 1) {
    checkAndEnqueueUnit(index, ctype);
  } else {
    strengthened.insert(std::make_pair(index, ctype));
  }
  return false;
}

void Preprocessor::findUnits() {
  for (auto& [index, ctype]: added) {
    checkAndEnqueueUnit(index, ctype);
  }
}

void Preprocessor::findPure() {
  for (auto& [v, _]: touched) {
    checkAndEnqueuePure( v);
    checkAndEnqueuePure(-v);
  }
}

void Preprocessor::propagate() {
  while (qhead < trail.size()) {
    int l = trail[qhead++];
    for (bool ctype: {false, true}) {
      int l_removed = ctype ? l: -l;
      for (int index: lit_to_occurrences[ctype][l_removed]) {
        // Strengthen clause/term.
        if (removeLit(index, l_removed, ctype)) {
          empty_seen = true;
          throw ctype;
        }
      }
      lit_to_occurrences[ctype][l_removed].clear();
      // Remove disabled constraints.
      for (int index: lit_to_occurrences[ctype][-l_removed]) {
        assert(index_to_lits[ctype].find(index) != index_to_lits[ctype].end());
        // Before removing the constraint, delete the disabling literal to avoid a redundant purity check.
        auto& c = index_to_lits[ctype][index];
        auto it = std::find(c.begin(), c.end(), -l_removed);
        assert(it != c.end());
        c.erase(it);
        removeConstraint(index, ctype, true);
      }
      // The disabling literal no longer occurs anywhere.
      lit_to_occurrences[ctype][-l_removed].clear();
    }
  }
}

void Preprocessor::checkAndEnqueueUnit(int index, bool ctype) {
  assert(index_to_lits[ctype].find(index) != index_to_lits[ctype].end());
  const auto& c = index_to_lits[ctype][index];
  if (c.size() == 1) {
    auto l = *c.begin();
    nr_units += enqueue(isUniversal(abs(l)) ? -l : l);
  }
}

bool Preprocessor::isPure(int l) {
  return lit_to_occurrences[false][-l].empty() && lit_to_occurrences[true][-l].empty();
}

void Preprocessor::checkAndEnqueuePure(int l) {
  if (isPure(l)) {
    nr_pure += enqueue(isUniversal(abs(l)) ? -l: l);
  }
}

bool Preprocessor::enqueue(int l) {
  if (!isAssigned(l)) {
    trail.push_back(l);
    assigned[abs(l) - 1] = true;
    return true;
  } else {
    return false;
  }
}

template<class T> bool Preprocessor::resolventTautological(const T& c, int pivot_variable) const {
  bool resolvent_tautological = false;
  for (const auto& l: c) {
    if (abs(l) == pivot_variable) {
      continue;
    }
    if (seen[lit2Index(-l)] && abs(l) < pivot_variable) {
      resolvent_tautological = true;
      break;
    }
  }
  return resolvent_tautological;
}

bool Preprocessor::seenBlockedByLit(int pivot_literal, bool ctype) const {
  bool blocked = true;
  if (lit_to_occurrences[ctype].find(-pivot_literal) != lit_to_occurrences[ctype].end()) {
    for (int index: lit_to_occurrences[ctype].at(-pivot_literal)) {
      auto&c = index_to_lits[ctype].at(index);
      if (!resolventTautological(c, abs(pivot_literal))) {
        blocked = false;
        break;
      }
    }
  }
  return blocked;
}

template<class T> bool Preprocessor::isBlocked(const T& c, bool ctype) {
  for (const auto& l: c) {
    seen[lit2Index(l)] = true;
  }
  bool blocked = false;
  for (const auto& l: c) {
    if (ctype == isUniversal(abs(l)) && lit_to_occurrences[!ctype][l].empty() && seenBlockedByLit(l, ctype)) {
      blocked = true;
      break;
    }
  }
  for (const auto& l: c) {
    seen[lit2Index(l)] = false;
  }
  return blocked;
}

void Preprocessor::removeBlocked() {
  do {
    touched_for_BCE.insert(touched.begin(), touched.end());
    touched_for_BVE.insert(touched.begin(), touched.end());
    touched.clear();
    auto incident_touched_BCE = incidentToVariables(touched_for_BCE);
    touched_for_BCE.clear();
    std::vector<std::pair<int, bool>> indices_to_remove;
    for (const auto& [i, ctype]: incident_touched_BCE) {
      assert(index_to_lits[ctype].find(i) != index_to_lits[ctype].end());
      const auto& c = index_to_lits[ctype][i];
      if (isBlocked(c, ctype)) {
        indices_to_remove.push_back(std::make_pair(i, ctype));
      }
    }
    for (auto& [i, ctype]: indices_to_remove) {
      removeConstraint(i, ctype, true);
    }
    nr_blocked += indices_to_remove.size();
  } while (!touched.empty());
}

bool Preprocessor::isAssigned(int l) {
  return assigned[abs(l) - 1];
}

void Preprocessor::reduce(int index, bool ctype) {
  auto& c = index_to_lits[ctype][index];
  while (!c.empty() && isUniversal(abs(c.back())) != ctype) {
    auto l = c.back();
    lit_to_occurrences[ctype][l].erase(index);
    checkAndEnqueuePure(-l);
    c.pop_back();
    nr_literals_reduced++;
  }
}

std::vector<int> Preprocessor::findSubsumed(const std::vector<int>& c, bool ctype) const {
  std::vector<int> subsumed_indices;
  assert(!c.empty());
  int l_occurs_fewest = *std::min_element(c.begin(), c.end(),
    [this, ctype](int l1, int l2) { return lit_to_occurrences[ctype].at(l1).size() < lit_to_occurrences[ctype].at(l2).size(); } );
  for (auto other_index: lit_to_occurrences[ctype].at(l_occurs_fewest)) {
    auto& c_other = index_to_lits[ctype].at(other_index);
    if (&c_other != &c && c.size() <= c_other.size() && std::includes(c.begin(), c.end(), c_other.begin(), c_other.end())) {
      subsumed_indices.push_back(other_index);
    }
  }
  return subsumed_indices;
}

void Preprocessor::selfSubsume(std::vector<int>& c, bool ctype) {
  for (unsigned int i = 0; i < c.size(); i++) {
    c[i] = -c[i];
    for (auto index: findSubsumed(c, ctype)) {
      nr_self_subsumed++;
      if (index_to_lits[ctype].find(index) != index_to_lits[ctype].end() && removeLit(index, c[i], ctype)) {
          empty_seen = true;
          throw ctype;
      }
      lit_to_occurrences[ctype][c[i]].erase(index);
    }
    checkAndEnqueuePure(c[i]);
    c[i] = -c[i];
  }
}

void Preprocessor::maybeEliminate(int v) {
  if (canEliminate(v)) {
    eliminate(v);
  }
}

void Preprocessor::eliminate(int v) {
  bool ctype = isUniversal(v);
  auto positive_occurrences = lit_to_occurrences[ctype][v];
  auto negative_occurrences = lit_to_occurrences[ctype][-v];
  std::vector<std::vector<int>> resolvents;
  for (auto index_positive: positive_occurrences) {
    for (auto index_negative: negative_occurrences) {
      std::vector<int> r;
      auto& c1 = index_to_lits[ctype][index_positive];
      auto& c2 = index_to_lits[ctype][index_negative];
      if (!resolve(c1, c2, r)) {
        while (!r.empty() && isUniversal(abs(r.back())) != ctype) {
          r.pop_back();
        }
        if (r.empty()) {
          throw ctype;
        } else {
          resolvents.emplace_back(r);
        }
      }
    }
  }
  if ((resolvents.size()) < (positive_occurrences.size() + negative_occurrences.size() + 200)) {
    // std::cerr << "Eliminating " << v << " occurring in " << positive_occurrences.size() + negative_occurrences.size() << " constraints." << std::endl;
    // std::cerr << "Adding " <<  resolvents.size() << " non-tautological resolvents." << std::endl;
    for (auto& c: resolvents) {
      addConstraint(c, ctype);
    }
    for (auto index_positive: positive_occurrences) {
      removeConstraint(index_positive, ctype, false);
      added.erase(std::make_pair(index_positive, ctype));
    }
    for (auto index_negative: negative_occurrences) {
      removeConstraint(index_negative, ctype, false);
      added.erase(std::make_pair(index_negative, ctype));
    }
    nr_eliminated++;
    touched.erase(std::make_pair(v, false));
    touched.erase(std::make_pair(v, true));
    touched_for_BCE.erase(std::make_pair(v, false));
    touched_for_BCE.erase(std::make_pair(v, true));
  }
}

bool Preprocessor::canEliminate(int v) {
  bool ctype = isUniversal(v);
  if (lit_to_occurrences[ctype][v].empty() && lit_to_occurrences[!ctype][-v].empty()) {
    return false;
  }
  // Size bounds from Een & Biere (should take a look at Cadical).
  // if (lit_to_occurrences[ctype][v].size() > 15 && lit_to_occurrences[ctype][-v].size() > 15) {
  //   return false;
  // }
  // Variable v to be eliminated may occur only in constraints ctype (only in clauses or only in terms).
  if (!lit_to_occurrences[!ctype][v].empty() || !lit_to_occurrences[!ctype][-v].empty()) {
    return false;
  }
  // v must be the rightmost variable in constraints it occurs in (TODO: relax this with a partial order).
  for (auto index: lit_to_occurrences[ctype][v]) {
    const auto& c = index_to_lits[ctype][index];
    if (abs(c.back()) != v) {
      return false;
    }
  }
  for (auto index: lit_to_occurrences[ctype][-v]) {
    const auto& c = index_to_lits[ctype][index];
    if (abs(c.back()) != v) {
      return false;
    }
  }
  return true;
}

void Preprocessor::touchAll(const std::vector<int>& c, bool ctype) {
  for (auto l: c) {
    auto v = abs(l);
    if (isUniversal(v) == ctype) {
      touched.insert(std::make_pair(v, ctype));
    }
  }
}

std::set<std::pair<int, bool>> Preprocessor::occurringInAdded() {
  std::set<std::pair<int, bool>> literals_occurring;
  for (auto& [index, ctype]: added) {
    if (index_to_lits[ctype].find(index) != index_to_lits[ctype].end()) {
      const auto& c = index_to_lits[ctype][index];
      for (auto l: c) {
        literals_occurring.insert(std::make_pair(l, ctype));
      }
    }
  }
  return literals_occurring;
}

std::set<std::pair<int, bool>> Preprocessor::incidentToLiterals(const std::set<std::pair<int, bool>>& literal_type_pairs) {
  std::set<std::pair<int, bool>> indices;
  for (auto& [l, ctype]: literal_type_pairs) {
    for (auto index: lit_to_occurrences[ctype][l]) {
      indices.insert(std::make_pair(index, ctype));
    }
  }
  return indices;
}

std::set<std::pair<int, bool>> Preprocessor::incidentToVariables(const std::set<std::pair<int, bool>>& variable_type_pairs) {
  std::set<std::pair<int, bool>> negated_variable_type_pairs;
  for (auto& [v, ctype]: variable_type_pairs) {
    negated_variable_type_pairs.insert(std::make_pair(-v, ctype));
  }
  auto indices = incidentToLiterals(variable_type_pairs);
  auto indices_incident_negative = incidentToLiterals(negated_variable_type_pairs);
  indices.insert(indices_incident_negative.begin(), indices_incident_negative.end());
  return indices;
}

void Preprocessor::strengthenSelfSubsumed() {
  auto literals_in_added = occurringInAdded();
  std::set<std::pair<int, bool>> negated_literals_in_added;
  for (auto& [l, ctype]: literals_in_added) {
    negated_literals_in_added.insert(std::make_pair(-l, ctype));
  }
  auto indices_to_check = incidentToLiterals(negated_literals_in_added);
  indices_to_check.insert(added.begin(), added.end());
  do {
    indices_to_check.insert(strengthened.begin(), strengthened.end());
    strengthened.clear();
    for (auto& [index, ctype]: indices_to_check) {
      if (index_to_lits[ctype].find(index) != index_to_lits[ctype].end()) {
        auto& c = index_to_lits[ctype][index];
        selfSubsume(c, ctype);
      }
    }
    indices_to_check.clear();
    propagate();
  } while (!strengthened.empty());
}

void Preprocessor::removeSubsumed() {
  auto indices_to_check = incidentToLiterals(occurringInAdded());
  for (auto& [index, ctype]: indices_to_check) {
    if (index_to_lits[ctype].find(index) != index_to_lits[ctype].end()) {
      auto& c = index_to_lits[ctype][index];
      auto indices_subsumed = findSubsumed(c, ctype);
      nr_subsumed += indices_subsumed.size();
      for (auto& index_subsumed: indices_subsumed) {
        removeConstraint(index_subsumed, ctype, true);
      }
    }
  }
  propagate();
}

void Preprocessor::boundedVariableElimination() {
  do {
    touched_for_BVE.insert(touched.begin(), touched.end());
    touched_for_BCE.insert(touched.begin(), touched.end());
    touched.clear();
    for (auto& [v, ctype]: touched_for_BVE) {
      if (isUniversal(v) == ctype) {
        maybeEliminate(v);
      }
    }
    touched_for_BVE.clear();
  } while (!touched.empty());
}

bool resolve(const std::vector<int>& c1, const std::vector<int>& c2, std::vector<int>& resolvent) {
  // Compute the resolvent of c1 and c2, return true if tautological.
  // We can assume that the constraints are ordered, and that the last literal is the pivot literal.
  unsigned int i, j;
  for (i = j = 0; i < (c1.size() - 1) && j < (c2.size() - 1);) {
    auto l1 = c1[i];
    auto l2 = c2[j];
    if (abs(l1) < abs(l2)) {
      resolvent.push_back(l1);
      i++;
    } else if (abs(l1) > abs(l2)) {
      resolvent.push_back(l2);
      j++;
    } else if (l1 == -l2) {
        return true;
    } else {
      // l1 == l2
      resolvent.push_back(l1);
      i++; j++;
    }
  }
  for (; i < (c1.size() - 1); i++) {
    resolvent.push_back(c1[i]);
  }
  for (; j < (c2.size() - 1); j++) {
    resolvent.push_back(c2[j]);
  }
  return false;
}
