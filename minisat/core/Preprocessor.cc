#include "Preprocessor.h"

Preprocessor::Preprocessor(const CDNF_formula& clauses, const CDNF_formula& terms) {
  int nr_clauses = 0;
  for (const auto& clause: clauses) {
    index_to_litset[false][nr_clauses++] = clause;
  }
  int nr_terms = 0;
  for (const auto& term: terms) {
    index_to_litset[true][nr_terms++] = term;
  }
}

void Preprocessor::preprocess() {}

std::pair<CDNF_formula, CDNF_formula> Preprocessor::getClausesTerms() {
  CDNF_formula clauses, terms;
  for (const auto& [_, clause]: index_to_litset[false]) {
    clauses.emplace_back(clause);
  }
  for (const auto& [_, term]: index_to_litset[true]) {
    terms.emplace_back(term);
  }
  return std::make_pair(clauses, terms);
}