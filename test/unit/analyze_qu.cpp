// Level-by-level analysis (analyze_qu.cpp): QU-resolution in mode 1, the
// kind switch, and mode 0 with '--legacyanalyze'.

#include "checker.hpp"
#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <memory>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

static Ref conflict_of (Internal &internal) {
  const Ref conflict = internal.propagate ();
  CHECK (conflict != Ref::none);
  return conflict;
}

// 'exists 1 forall 2 exists 3' with (1 2 3) and (1 -2 3) under -1, -3:
// mode 1 propagates the universal 2 from one clause, the other is the
// conflict.  Resolving on the universal 2 (QU-resolution) leaves (3 1),
// asserting 3 on level 1.
static void test_universal_pivot () {
  Internal internal;
  internal.opts.mode = 1;
  declare (internal, "eae");
  const Ref a = add (internal, Clause, {1, 2, 3});
  const Ref b = add (internal, Clause, {1, -2, 3});
  decide (internal, -1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, -3);
  const Ref conflict = conflict_of (internal);
  CHECK (internal.reason (1) == (conflict == a ? b : a));
  internal.analyze (conflict);
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK_EQ (internal.stats.learned[0], 1);
  const Ref learnt = internal.redundant[0][0];
  CHECK (stored (internal, learnt) == lits ({3, 1}));
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.val (L (3)) > 0 && internal.reason (2) == learnt);
  internal.check_invariants ();
}

// The dual for cubes: 'forall 1 exists 2 forall 3' with (1 2 3) and
// (1 -2 3) under 1, 3: the existential 2 is resolved, (3 1) asserts -3.
static void test_existential_pivot () {
  Internal internal;
  internal.opts.mode = 1;
  declare (internal, "aea");
  add (internal, Cube, {1, 2, 3});
  add (internal, Cube, {1, -2, 3});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, 3);
  internal.analyze (conflict_of (internal));
  CHECK_EQ (internal.stats.learned[1], 1);
  const Ref learnt = internal.redundant[1][0];
  CHECK (stored (internal, learnt) == lits ({3, 1}));
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.val (L (-3)) > 0 && internal.reason (2) == learnt);
  internal.check_invariants ();
}

// 'forall 1 exists 2 forall 3 exists 4'.  Under the decision 1 the cube
// (1 -3) forces 3, the cube (1 2 3) then forces -2 (2 is secondary there),
// and the clauses (-1 2 4), (-1 2 -4) conflict.  Resolving the clause
// conflict on 4 leaves -1 (blocked) and 2, whose reason is a cube: the
// analysis restarts from that cube as a cube analysis, with 2 taken as it
// occurs there.  Resolving on 3 with (1 -3) leaves (1 2), reduced to the
// unit cube (1): -1 at the root.  The conflict counts once, and the proof
// step (checked by the internal checker) has the chain of the cube round.
static void test_kind_switch () {
  Internal internal;
  internal.opts.mode = 1;
  declare (internal, "aeae");
  Proof proof{&internal};
  auto owned = std::make_unique<Recorder> ();
  const Recorder &recorder = *owned;
  proof.connect (std::move (owned));
  proof.connect (std::make_unique<Checker> (internal));
  internal.proof = &proof;
  const Ref forces3 = add (internal, Cube, {1, -3});
  const Ref forces2 = add (internal, Cube, {1, 2, 3});
  add (internal, Clause, {-1, 2, 4});
  add (internal, Clause, {-1, 2, -4});
  decide (internal, 1);
  const Ref conflict = conflict_of (internal);
  CHECK (deref (internal.arena, conflict).kind () == Clause);
  CHECK (internal.reason (2) == forces3 && internal.reason (1) == forces2);
  internal.analyze (conflict);
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK_EQ (internal.stats.learned[0], 0);
  CHECK_EQ (internal.stats.learned[1], 1);
  CHECK (stored (internal, internal.irredundant[1].back ()) == lits ({1}));
  CHECK (recorder.steps.back () == "a 5 t: 1 : 2 1");
  CHECK_EQ (internal.stats.checked, 1);
  CHECK_EQ (internal.decision_level (), 0);
  CHECK (internal.val (L (-1)) > 0);
  internal.check_invariants ();
  internal.proof = nullptr;
}

// A kind switch that ends in a dependency.  'forall 1 exists 2 forall 3
// exists 4 5' with '--dl': the decision 1 (level 1) forces -4 by (-1 -4);
// the decision 3 (level 2) makes the cube (1 2 3) force -2, and the
// clauses (-1 2 -3 4 5), (-1 2 -3 4 -5) conflict.  The clause analysis
// resolves 5; -3 stays (left of 4) and blocks, so it resolves 2, whose
// reason is the cube: it switches to the cube, where 2 is blocked on level
// 2 and the decision 3 right of it would have to be resolved.  So 3
// depends on 2, and the search backtracks to level 1.
static void test_switch_to_dependency () {
  Internal internal;
  internal.opts.mode = 1;
  internal.opts.dl = 1;
  declare (internal, "aeaee");
  add (internal, Clause, {-1, -4});
  add (internal, Cube, {1, 2, 3});
  add (internal, Clause, {-1, 2, -3, 4, 5});
  add (internal, Clause, {-1, 2, -3, 4, -5});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, 3);
  internal.analyze (conflict_of (internal));
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK_EQ (internal.stats.dependencies, 1);
  CHECK_EQ (internal.stats.learned[0] + internal.stats.learned[1], 0);
  CHECK (internal.depend.on[2] == std::vector<Var> ({1}));
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.trail == lits ({1, -4}));
  internal.check_invariants ();
}

// Mode 0 with '--legacyanalyze', on the example of 'search' where
// 'analyze.cpp' learns (-2 -1): the level-by-level analysis resolves the
// gate 2 first, because it is not the only literal of level 2 (the
// universal 3 is there too); once 4 is resolved so that 3 can be reduced,
// level 2 is empty and the unit (-1) is left.
static void test_legacy () {
  Internal internal;
  internal.opts.legacyanalyze = 1;
  declare (internal, "eEae");
  add (internal, Clause, {-1, 4});
  add (internal, Clause, {2, 3, -4});
  add (internal, Clause, {-2, 3, -4});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, -3);
  internal.analyze (conflict_of (internal));
  CHECK (internal.redundant[0].empty ());
  CHECK (stored (internal, internal.irredundant[0].back ()) == lits ({-1}));
  CHECK_EQ (internal.decision_level (), 0);
  CHECK (internal.val (L (-1)) > 0);
  internal.check_invariants ();
}

int main () {
  test_universal_pivot ();
  test_existential_pivot ();
  test_kind_switch ();
  test_switch_to_dependency ();
  test_legacy ();
  return test_result ();
}
