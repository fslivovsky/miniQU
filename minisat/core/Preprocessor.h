#ifndef MiniQU_Preprocessor_h
#define MiniQU_Preprocessor_h

#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <tuple>

typedef std::vector<std::vector<int>> CDNF_formula;

class Preprocessor {
 public:
  Preprocessor(const CDNF_formula& clauses, const CDNF_formula& terms);
  void preprocess();
  std::pair<CDNF_formula, CDNF_formula> getClausesTerms();

 protected:
  void createOccurrenceLists();
  void removeConstraint(int index, bool ctype);
  bool removeLit(int index, int l, bool ctype);
  void findUnits();
  void findPure();
  void propagate();
  void checkAndPushUnit(int index, bool ctype);
  bool isPure(int l);
  bool enqueue(int l);

  std::unordered_map<int, std::unordered_set<int>> index_to_litset[2];
  std::unordered_map<int, std::unordered_set<int>> lit_to_occurrences[2];

  int qhead;
  std::vector<int> trail;
  std::vector<bool> assigned;
  int maxvar;
  bool empty_seen;

  int nr_units, nr_pure;

};

inline bool isUniversal(int variable) {
  return variable % 2;
}

#endif