#ifndef MiniQU_Preprocessor_h
#define MiniQU_Preprocessor_h

#include <unordered_map>
#include <set>
#include <vector>
#include <tuple>
#include <utility>

typedef std::vector<std::vector<int>> CDNF_formula;

class Preprocessor {
 public:
  Preprocessor(const CDNF_formula& clauses, const CDNF_formula& terms);
  void preprocess();
  std::pair<CDNF_formula, CDNF_formula> getClausesTerms();

 protected:
  void addConstraint(const std::vector<int>& c, bool ctype);
  void removeConstraint(int index, bool ctype, bool check_pure);
  bool removeLit(int index, int l, bool ctype);
  void findUnits();
  void findPure();
  void propagate();
  void checkAndEnqueueUnit(int index, bool ctype);
  bool isPure(int l);
  void checkAndEnqueuePure(int l);
  bool enqueue(int l);
  template<class T> bool resolventTautological(const T& c, int pivot_variable) const;
  bool seenBlockedByLit(int pivot_literal, bool ctype) const;
  template<class T> bool isBlocked(const T& c, bool ctype);
  void removeBlocked();
  bool isAssigned(int l);
  void reduce(int index, bool ctype);
  std::vector<int> findSubsumed(const std::vector<int>& c, bool ctype) const;
  void selfSubsume(std::vector<int>& c, bool ctype);
  void maybeEliminate(int v);
  void eliminate(int v);
  bool canEliminate(int v);
  void touchAll(const std::vector<int>& c, bool ctype);
  std::set<std::pair<int, bool>> occurringInAdded();
  std::set<std::pair<int, bool>> incidentToLiterals(const std::set<std::pair<int, bool>>& literal_type_pairs);
  std::set<std::pair<int, bool>> incidentToVariables(const std::set<std::pair<int, bool>>& variable_type_pairs);
  void strengthenSelfSubsumed();
  void removeSubsumed();
  void boundedVariableElimination();

  std::unordered_map<int, std::vector<int>> index_to_lits[2];
  std::unordered_map<int, std::set<int>> lit_to_occurrences[2];

  unsigned int qhead;
  std::vector<int> trail;
  std::vector<bool> assigned;
  int maxvar;
  bool empty_seen;
  int nr_constraints[2];

  int nr_units, nr_pure, nr_blocked, nr_literals_reduced, nr_self_subsumed, nr_subsumed, nr_eliminated;
  std::vector<bool> seen;
  std::vector<bool> variable_type;

  std::set<std::pair<int, bool>> added;
  std::set<std::pair<int, bool>> strengthened;
  std::set<std::pair<int, bool>> touched, touched_for_BVE, touched_for_BCE;

};

inline bool isUniversal(int variable) {
  return variable % 2;
}

inline int lit2Index(int lit) {
  return 2 * (abs(lit) - 1) + (lit < 0);
}

bool resolve(const std::vector<int>& c1, const std::vector<int>& c2, std::vector<int>& resolvent);

#endif