#include "Preprocessor.h"

#include <algorithm>
#include <iostream>

#include <assert.h>

Preprocessor::Preprocessor(const CDNF_formula& clauses, const CDNF_formula& terms): qhead(0), maxvar(0), empty_seen(false), nr_units(0), nr_pure(0) {
  int nr_clauses = 0;
  for (const auto& clause: clauses) {
    index_to_litset[false][nr_clauses++] = std::unordered_set<int>(clause.begin(), clause.end());
    auto max_var_it = std::max_element(clause.begin(), clause.end(), [](int l1, int l2) { return abs(l1) < abs(l2); });
    maxvar = std::max(maxvar, abs(*max_var_it));
  }
  int nr_terms = 0;
  for (const auto& term: terms) {
    index_to_litset[true][nr_terms++] = std::unordered_set<int>(term.begin(), term.end());
    auto max_var_it = std::max_element(term.begin(), term.end(), [](int l1, int l2) { return abs(l1) < abs(l2); });
    maxvar = std::max(maxvar, abs(*max_var_it));
  }
  assigned.resize(maxvar);
  std::fill(assigned.begin(), assigned.end(), false);
}

void Preprocessor::preprocess() {
  createOccurrenceLists();
  propagate();
  std::cerr << "Propagated " << nr_units << " unit and " << nr_pure << " pure literals." << std::endl;
}

std::pair<CDNF_formula, CDNF_formula> Preprocessor::getClausesTerms() {
  CDNF_formula clauses, terms;
  for (const auto& [_, clause]: index_to_litset[false]) {
    clauses.emplace_back(clause.begin(), clause.end());
    assert(empty_seen || clauses.back().size() != 1);
  }
  for (const auto& [_, term]: index_to_litset[true]) {
    terms.emplace_back(term.begin(), term.end());
    assert(empty_seen || terms.back().size() != 1);
  }
  return std::make_pair(clauses, terms);
}

void Preprocessor::createOccurrenceLists() {
  for (int t: {0, 1}) {
    for (const auto& [index, c]: index_to_litset[t]) {
      for (const auto& l: c) {
        lit_to_occurrences[t][l].insert(index);
      }
    }
  }
}

void Preprocessor::removeConstraint(int index, bool ctype) {
  for (const auto& l: index_to_litset[ctype][index]) {
    lit_to_occurrences[ctype][l].erase(index);
    if (lit_to_occurrences[ctype][l].empty() && isPure(-l)) {
      nr_pure += enqueue(isUniversal(abs(l)) ? l: -l);
    }
  }
  index_to_litset[ctype].erase(index);
}

bool Preprocessor::removeLit(int index, int l, bool ctype) {
  // lit_to_occurrences[ctype][l].erase(index);
  index_to_litset[ctype][index].erase(l);
  if (index_to_litset[ctype][index].empty()) {
    return true;
  } else if (index_to_litset[ctype][index].size() == 1) {
    checkAndPushUnit(index, ctype);
  }
  return false;
}

void Preprocessor::findUnits() {
  for (int t: {0, 1}) {
    for (const auto& [index, c]: index_to_litset[t]) {
      checkAndPushUnit(index, t);
    }
  }
}

void Preprocessor::findPure() {
  for (int t: {0, 1}) {
    for (const auto& [l, occs]: lit_to_occurrences[t]) {
      if (isPure(l)) {
        nr_pure += enqueue(isUniversal(abs(l)) ? -l: l);
      } else if (isPure(-l)) {
        nr_pure += enqueue(isUniversal(abs(l)) ? -l: l);
      }
    }
  }
}

void Preprocessor::propagate() {
  findUnits();
  findPure();
  while (qhead < trail.size()) {
    int l = trail[qhead++];
    for (int t: {0, 1}) {
      int l_removed = t ? l: -l;
      for (int index: lit_to_occurrences[t][l_removed]) {
        if (removeLit(index, l_removed, t)) {
          empty_seen = true;
          return; // Clause or term empty, stop propagating.
        }
      }
      lit_to_occurrences[t][l_removed].clear();
      for (int index: lit_to_occurrences[t][-l_removed]) {
        index_to_litset[t][index].erase(-l_removed);
        removeConstraint(index, t);
      }
      lit_to_occurrences[t][-l_removed].clear();
    }
  }
}

void Preprocessor::checkAndPushUnit(int index, bool ctype) {
  assert(index_to_litset[ctype].find(index) != index_to_litset[ctype].end());
  const auto& c = index_to_litset[ctype][index];
  if (c.size() == 1) {
    auto l = *c.begin();
    nr_units += enqueue(isUniversal(abs(l)) ? -l : l);
    //std::cerr << "Found unit: " << units.back() << std::endl;
  }
}

bool Preprocessor::isPure(int l) {
  return lit_to_occurrences[false][-l].empty() && lit_to_occurrences[true][-l].empty();
}

bool Preprocessor::enqueue(int l) {
  bool is_assigned = assigned[abs(l) - 1];
  if (!is_assigned) {
    trail.push_back(l);
    assigned[abs(l) - 1] = true;
    return true;
  } else {
    return false;
  }
}

