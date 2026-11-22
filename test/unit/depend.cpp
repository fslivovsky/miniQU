// Dependency learning (depend.cpp, the '--dl' paths of decide.cpp and
// backtrack.cpp, the dependency outcome of the analyses).

#include "internal_test.hpp"
#include "test.hpp"

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause;

static Internal &with_dl (Internal &internal, const char *prefix) {
  internal.opts.dl = 1;
  declare (internal, prefix);
  return internal;
}

// Variable 5 depends on 2 and then on 1; the watch moves along the
// assignments, the variable leaves and re-enters the single heap, and a
// reset forgets everything.
static void test_watches () {
  Internal internal;
  with_dl (internal, "eaeae");
  CHECK_EQ (internal.heaps.size (), 1u);
  CHECK_EQ (internal.heaps[0].size (), 5u);
  const Depend &depend = internal.depend;

  // Recording leaves the heap alone ('learn_dependency' takes 4 out after
  // its backtrack).
  internal.record_dependency (4, 1);
  CHECK (depend.on[4] == std::vector<Var> ({1}));
  CHECK (depend.watching[1] == std::vector<Var> ({4}));
  CHECK (internal.heaps[0].contains (4));
  internal.heaps[0].remove (4);
  internal.record_dependency (4, 0);
  CHECK (depend.on[4] == std::vector<Var> ({0, 1}));
  CHECK (depend.watching[0] == std::vector<Var> ({4}));
  CHECK (depend.watching[1].empty ());
  CHECK (!internal.eligible (4));
  CHECK_EQ (internal.stats.dependencies, 2);
  internal.check_invariants ();

  // 1 assigned: the watch moves to the unassigned 2.
  decide (internal, 1);
  internal.update_dependency_watches ();
  CHECK (depend.on[4] == std::vector<Var> ({1, 0}));
  CHECK (depend.watching[1] == std::vector<Var> ({4}));
  CHECK (depend.watching[0].empty ());
  CHECK (!internal.heaps[0].contains (4) && !internal.eligible (4));
  internal.check_invariants ();

  // 2 assigned: no unassigned dependency is left, 5 is back.
  decide (internal, -2);
  internal.update_dependency_watches ();
  CHECK (depend.on[4] == std::vector<Var> ({1, 0}));
  CHECK (internal.heaps[0].contains (4) && internal.eligible (4));
  CHECK_EQ (internal.depend.propagated, 2u);

  // Unassigning 2 makes 5 ineligible again but leaves it in the heap; a
  // decision pops it first (highest score), drops it and decides 2.
  internal.backtrack (1);
  CHECK_EQ (internal.depend.propagated, 1u);
  internal.bump_variable (4);
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({1, -2}));
  CHECK (!internal.heaps[0].contains (4));
  internal.check_invariants ();
  // The next decision sees 2 assigned and takes 5.
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({1, -2, -5}));

  // Backtracking to the root unassigns 2: 5 stays out of the heap.
  internal.backtrack (0);
  CHECK (!internal.heaps[0].contains (4));
  CHECK (internal.heaps[0].contains (0) && internal.heaps[0].contains (1));
  internal.check_invariants ();
  // Backtracking that keeps the watch assigned puts 5 back.
  decide (internal, 1);
  decide (internal, 2);
  decide (internal, 5);
  internal.backtrack (2);
  CHECK (internal.heaps[0].contains (4));
  internal.backtrack (0);

  internal.reset_dependencies ();
  CHECK_EQ (internal.stats.depresets, 1);
  for (Var v = 0; v < 5; v++) {
    CHECK (depend.on[v].empty () && depend.watching[v].empty ());
    CHECK (internal.heaps[0].contains (v));
  }
  internal.check_invariants ();
}

// Every 'depreset'-th restart, counted as the old 'curr_restarts + 1', if
// a constraint was learnt since the last reset.
static void test_reset_schedule () {
  Internal internal;
  with_dl (internal, "e");
  internal.stats.restarts = 19;
  CHECK (!internal.resetting_dependencies ());
  internal.stats.learned[1] = 1;
  CHECK (internal.resetting_dependencies ());
  internal.stats.restarts = 20;
  CHECK (!internal.resetting_dependencies ());
  internal.opts.depreset = 1;
  CHECK (internal.resetting_dependencies ());
  internal.reset_dependencies ();
  CHECK (!internal.resetting_dependencies ());
  internal.stats.learned[0] = 1;
  CHECK (internal.resetting_dependencies ());
  internal.opts.dl = 0;
  CHECK (!internal.resetting_dependencies ());
}

// 'forall 1 exists 2: (1 | 2) & (-1 | -2)' is true, with the inner 2
// decided first (highest score) under '--dl'.
static void declare_xor (Internal &internal, int mode, bool dl) {
  internal.opts.mode = mode;
  internal.opts.dl = dl;
  declare (internal, "ae");
  add (internal, Clause, {1, 2});
  add (internal, Clause, {-1, -2});
  internal.bump_variable (1);
}

// In mode 0 the conflict (1 | 2) under -2 is completed by assigning the
// universal 1, which blocks the decision 2: 2 depends on 1.
static void test_learn_dependency () {
  Internal internal;
  declare_xor (internal, 0, true);
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({-2}));
  const Ref conflict = internal.propagate ();
  CHECK (conflict != Ref::none);
  internal.analyze (conflict);
  CHECK_EQ (internal.stats.dependencies, 1);
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK (internal.depend.on[1] == std::vector<Var> ({0}));
  CHECK_EQ (internal.decision_level (), 0);
  CHECK (internal.trail.empty ());
  CHECK (!internal.heaps[0].contains (1));
  CHECK (internal.redundant[0].empty () && internal.redundant[1].empty ());
  internal.check_invariants ();
  // Now 1 is decided first, and 2 comes back once it is assigned.
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({-1}));
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.trail == lits ({-1, 2}));
}

// Whole runs: the same verdict in prefix order and with '--dl' (where
// mode 0 needs a dependency; mode 1 propagates the universal 1 instead).
static void test_verdicts () {
  for (int mode : {0, 1})
    for (bool dl : {false, true}) {
      Internal internal;
      declare_xor (internal, mode, dl);
      CHECK (internal.solve () == Status::True);
      CHECK_EQ (internal.stats.dependencies, mode == 0 && dl ? 1 : 0);
    }
}

// The heap holds what the old code's heap holds: a decision with every
// variable assigned empties it, and a reset puts back every decision
// variable, assigned or not.
static void test_heap_contents () {
  Internal internal;
  with_dl (internal, "ee");
  add (internal, Clause, {1});
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({1, -2}));
  internal.reset_dependencies ();
  CHECK_EQ (internal.heaps[0].size (), 2u);
  CHECK (!internal.decide ());
  CHECK (internal.heaps[0].empty ());
  internal.backtrack (0);
  CHECK (internal.heaps[0].contains (1) && !internal.heaps[0].contains (0));
  internal.reset_dependencies ();
  CHECK (internal.heaps[0].contains (0));
}

int main () {
  test_watches ();
  test_heap_contents ();
  test_reset_schedule ();
  test_learn_dependency ();
  test_verdicts ();
  return test_result ();
}
