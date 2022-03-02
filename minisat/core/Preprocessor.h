#ifndef MiniQU_Preprocessor_h
#define MiniQU_Preprocessor_h

#include <assert.h>
#include <unordered_map>
#include <vector>
#include <tuple>

typedef std::vector<std::vector<int>> CDNF_formula;

class Preprocessor {
 public:
  Preprocessor(const CDNF_formula& clauses, const CDNF_formula& terms);
  void preprocess();
  std::pair<CDNF_formula, CDNF_formula> getClausesTerms();

 protected:
  std::unordered_map<int, std::vector<int>> index_to_litset[2];

};

#endif