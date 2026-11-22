#ifndef MINIQU_INTERNAL_HPP_INCLUDED
#define MINIQU_INTERNAL_HPP_INCLUDED

#include "arena.hpp"
#include "constraint.hpp"
#include "heap.hpp"
#include "limit.hpp"
#include "lit.hpp"
#include "logging.hpp"
#include "message.hpp"
#include "options.hpp"
#include "prefix.hpp"
#include "profile.hpp"
#include "random.hpp"
#include "stats.hpp"
#include "watch.hpp"

#include <array>
#include <atomic>
#include <cstdint>
#include <span>
#include <vector>

namespace miniqu {

// The whole solver state as plain data members (ARCHITECTURE 3).  The
// member functions are implemented in one file per technique; each file
// reads everything but writes only what it owns or changes it through the
// owner's functions: constraints are created and deleted only in
// 'constraint.cpp', values only in 'assign.cpp' and 'backtrack.cpp'.

class Proof;

// Dynamic data of a variable, valid while it is assigned.
struct VarData {
  int level;
  Ref reason; // 'Ref::none' for decisions and completed conflicts
  int trail;  // position on the trail
};

// What the watch loop does with a constraint whose only non-vanished
// literal is secondary (ARCHITECTURE 7.2).
enum class Lone : uint8_t { Conflict, Propagate, Ignore };

enum class Status : uint8_t { Unknown, True, False };

// Dependency learning (ARCHITECTURE 7.4, 'depend.cpp').  'on[v]' lists the
// variables 'v' was learnt to depend on; its first entry is the watched
// one, and 'watching[u]' lists the variables whose watched dependency is
// 'u'.  Trail literals before 'propagated' have had their watch lists
// processed.  Empty unless '--dl' is given.
struct Depend {
  std::vector<std::vector<Var>> on;
  std::vector<std::vector<Var>> watching;
  size_t propagated = 0;
};

// The resolvent of 'analyze_qu' as variables per block, so that the
// rightmost primary block and the literals right of it are found without
// scanning ('analyze_qu.cpp').  'position[v]' is the index of 'v' in
// 'at[depth (v)]', or -1.  Empty outside 'analyze_qu'.
struct LevelAnalysis {
  std::vector<std::vector<Var>> at;
  std::vector<int> position;
};

// The list in which a constraint of that kind watching 'l' is found: the
// list of the literal whose assignment makes 'l' vanish.  Applied to a
// literal that became true it gives the watched literal that vanished.
constexpr Lit watch_key (Kind kind, Lit l) {
  return kind == Kind::Clause ? ~l : l;
}

// The literal that becomes true when a constraint of that kind propagates
// its literal 'l': 'l' itself for a clause, its negation for a cube.
constexpr Lit forced (Kind kind, Lit l) {
  return kind == Kind::Clause ? l : ~l;
}

struct Internal {
  Options opts;
  Stats stats;
  Profiles profiles{0};
  Limit lim;
  Inc inc;
  Last last;

  Prefix prefix;

  Arena arena;
  Watches watches;
  std::array<std::vector<Ref>, 2> irredundant; // per kind
  std::array<std::vector<Ref>, 2> redundant;   // per kind
  uint64_t next_id = 1;

  std::vector<int8_t> vals;    // per literal: 1, -1 or 0
  std::vector<VarData> vtab;   // per variable
  std::vector<Lit> trail;      // assigned literals in order
  std::vector<size_t> control; // per decision level, where it starts
  size_t propagated = 0;       // trail literals propagated in both kinds
  Lit lone = lit_undef;        // to complete a mode-0 conflict

  std::vector<double> scores; // per variable
  double score_inc = 1;       // what a bump adds (EVSIDS)
  Random random;              // initial scores with '--seed'
  std::vector<Heap> heaps;    // per block (one with '--dl'), decisions only
  std::vector<int8_t> phases; // per variable: saved value, 1 or -1

  // Conflict analysis.  'seen' (per variable) is all zero outside
  // 'analyze' and 'initial_cube'; so are 'level_count' and, at 'no_var',
  // 'level_blocked' (both per decision level).
  std::vector<uint8_t> seen;
  std::vector<Lit> analyzed;      // every literal added to the resolvent
  std::vector<int> level_count;   // primary literals per level
  std::vector<Var> level_blocked; // leftmost secondary variable per level
  std::vector<Lit> derived;       // the learnt constraint
  std::vector<uint64_t> chain;    // antecedent ids, only with a proof
  std::vector<int> glue_levels;
  LevelAnalysis qu;

  Depend depend;

  Ref model_cube = Ref::none; // buffer of 'initial_cube'
  std::vector<Lit> model;     // literals of the next initial cube

  std::vector<Lit> certificate; // values of the certificate block

  Proof *proof = nullptr;
  std::atomic<bool> terminated = false;
  Status status = Status::Unknown;

  int val (Lit l) const { return vals[index (l)]; }
  // Positive: disables a constraint of that kind; negative: has vanished.
  int kval (Kind kind, Lit l) const {
    return kind == Kind::Clause ? val (l) : -val (l);
  }
  int level (Var v) const { return vtab[v].level; }
  Ref reason (Var v) const { return vtab[v].reason; }
  int decision_level () const { return static_cast<int> (control.size ()); }
  Heap &heap_of (Var v) { return heaps[opts.dl ? 0 : prefix.depth (v)]; }
  const Heap &heap_of (Var v) const {
    return heaps[opts.dl ? 0 : prefix.depth (v)];
  }

  // internal.cpp
  Var add_var (Quant, bool decision, int proof_number);
  [[nodiscard]] Status solve ();
  void search ();

  // constraint.cpp
  void add_original (Kind, std::vector<Lit> &lits, int gate);
  Ref new_constraint (uint64_t id, Kind, std::span<const Lit>, bool learnt,
                      uint32_t glue);
  void mark_garbage (Ref);
  void shrink_constraint (Ref, uint32_t new_size);
  void attach (Ref);
  void detach (Ref);
  void found_empty (Kind);

  // assign.cpp
  void assign (Lit, Ref reason);
  void new_level ();

  // propagate.hpp, propagate.cpp, propagate_ldq.cpp
  template <Kind K, Lone R> [[nodiscard]] Ref propagate_watches (Lit p);
  template <Lone R> [[nodiscard]] Ref propagate_trail ();
  [[nodiscard]] Ref propagate ();
  [[nodiscard]] Ref propagate_ldq ();

  // backtrack.cpp
  void backtrack (int new_level);

  // decide.cpp
  bool eligible (Var) const;
  [[nodiscard]] bool decide ();

  // bump.cpp
  double initial_score ();
  void bump_variable (Var);
  void decay_scores ();

  // depend.cpp
  void add_dependency_var ();
  void record_dependency (Var x, Var y);
  void update_dependency_watches ();
  bool stays_eligible (Var, int new_level) const;
  bool waits_for_dependency (Var) const;
  bool resetting_dependencies () const;
  void reset_dependencies ();

  // analyze.cpp
  void analyze (Ref conflict);
  void analyze_q (Ref conflict);
  void clear_analyzed ();

  // analyze_qu.cpp
  void analyze_qu (Ref conflict);

  // learn.cpp
  uint32_t compute_glue (std::span<const Lit>);
  void learn (Kind, Var asserting);
  void learn_dependency (Var x, Var y);

  // reduce.cpp
  void init_reduce ();
  void adjust_learnt_limit ();
  bool reducing () const;
  void protect_reasons ();
  void unprotect_reasons ();
  void reduce ();

  // collect.cpp
  bool collecting () const;
  void garbage_collect ();

  // restart.cpp
  int64_t restart_interval (int64_t restarts) const;
  bool restarting () const;
  void restart ();

  // model.cpp
  void init_model_cube ();
  [[nodiscard]] Ref alloc_model_cube (Arena &) const;
  void relocate_model_cube (Arena &);
  [[nodiscard]] Ref initial_cube ();
  void check_model_cube () const;

  // certificate.cpp
  void record_certificate ();
  int certificate_value (Var) const;

  // report.cpp
  void report (const char *event) const;

  // check.cpp
  void check_invariants () const;

#ifdef MINIQU_LOGGING
  // logging.cpp; 'LOG' calls these inside member functions.
  void log (const char *fmt, ...) const MINIQU_PRINTF (2, 3);
  void log (Ref, const char *fmt, ...) const MINIQU_PRINTF (3, 4);
#endif
};

} // namespace miniqu

#endif
