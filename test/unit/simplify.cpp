// Root-level simplification (simplify.cpp): the three steps for clauses
// and cubes, the unit conditions, the results of strengthening, watches
// after a rewrite, and the proof steps, which the internal checker
// replays.

#include "checker.hpp"
#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// An 'Internal', with the recorder and the checker connected if traced.
struct Fixture {
  Internal internal;
  Proof proof{&internal};
  Recorder *recorder = nullptr;

  // Without the throttle unless a test turns it on, and without garbage
  // collection, so that references stay valid.
  Fixture (const char *prefix, bool traced, int mode = 0) {
    internal.opts.mode = mode;
    internal.opts.rootsimpdelay = 0;
    internal.opts.gcfrac = 100;
    declare (internal, prefix);
    if (!traced)
      return;
    auto owned = std::make_unique<Recorder> ();
    recorder = owned.get ();
    proof.connect (std::move (owned));
    proof.connect (std::make_unique<Checker> (internal));
    internal.proof = &proof;
  }
  ~Fixture () { internal.proof = nullptr; }

  Ref add (Kind kind, std::initializer_list<int> dimacs) {
    return ::add (internal, kind, dimacs);
  }

  // Propagates, then simplifies once; returns the root conflict.
  Ref simplify () {
    internal.init_model_cube ();
    CHECK (internal.propagate () == Ref::none);
    CHECK (internal.simplifying ());
    return internal.simplify_root ();
  }

  // The literals of a stored constraint, in order of the variables.
  std::vector<Lit> sorted (Ref ref) const {
    std::vector<Lit> result = stored (internal, ref);
    std::sort (result.begin (), result.end ());
    return result;
  }
  bool garbage (Ref ref) const {
    return deref (internal.arena, ref).garbage ();
  }
  bool unit_reason (int dimacs) const {
    const Ref r = internal.reason (var (L (dimacs)));
    return r != Ref::none && deref (internal.arena, r).size () == 1;
  }
  // The proof steps after the first 'from'.
  std::vector<std::string> steps (size_t from) const {
    return {recorder->steps.begin () + (long) from, recorder->steps.end ()};
  }
};

// Step 1 for clauses: 2 is forced by (-1 2) under the unit (1), 3 by
// (-1 -2 3) under the new (2) and (1), in the order of the reason's
// literals.  Both reasons are then disabled by literals with units and
// deleted (step 3).  Ids are counted alike without a proof.
static void test_units_clauses (bool traced) {
  Fixture f ("eee", traced);
  f.add (Clause, {1});
  const Ref r2 = f.add (Clause, {-1, 2});
  const Ref r3 = f.add (Clause, {-1, -2, 3});
  CHECK (f.simplify () == Ref::none);
  CHECK (f.unit_reason (1) && f.unit_reason (2) && f.unit_reason (3));
  CHECK (f.garbage (r2) && f.garbage (r3));
  CHECK_EQ (f.internal.stats.rootunits, 2);
  CHECK_EQ (f.internal.stats.rootdeleted, 2);
  CHECK_EQ (f.internal.irredundant[0].size (), 3u);
  CHECK_EQ (f.internal.next_id, 6u);
  if (traced) {
    const std::vector<std::string> expected = {
        "a 4 c: 2 : 2 1", "a 5 c: 3 : 3 4 1", "d 2", "d 3"};
    CHECK (f.steps (3) == expected);
    CHECK_EQ (f.internal.stats.checked, 2);
  }
}

// Step 1 for cubes: the unit cube (-1) forces 1, (1 2) forces -2, and
// (1 -2 3) forces -3.  The chain lists the units in the order of the
// reason's literals.
static void test_units_cubes () {
  Fixture f ("aaa", true);
  f.add (Cube, {-1});
  const Ref r2 = f.add (Cube, {1, 2});
  const Ref r3 = f.add (Cube, {1, -2, 3});
  CHECK (f.simplify () == Ref::none);
  CHECK (f.internal.val (L (-3)) > 0);
  CHECK (f.unit_reason (2) && f.unit_reason (3));
  CHECK (f.garbage (r2) && f.garbage (r3));
  const std::vector<std::string> expected = {
      "a 4 t: 2 : 2 1", "a 5 t: 3 : 3 4 1", "d 2", "d 3"};
  CHECK (f.steps (3) == expected);
}

// 'forall 1 exists 2 3 4': the unit cube (1) assigns -1, and (1 2) then
// forces 2.  -1 has a unit, but a cube, so (1 2) gives no clause unit, and
// 1 is not removed from (1 3 4).  (-1 3 4) is disabled by -1, whose unit
// has the other kind, and is deleted.
static void test_other_kind () {
  Fixture f ("aeee", true);
  f.add (Cube, {1});
  const Ref reason = f.add (Clause, {1, 2});
  const Ref kept = f.add (Clause, {1, 3, 4});
  const Ref disabled = f.add (Clause, {-1, 3, 4});
  const size_t before = f.recorder->steps.size ();
  CHECK (f.simplify () == Ref::none);
  CHECK (f.internal.reason (1) == reason);
  CHECK (!f.garbage (reason) && !f.garbage (kept) && f.garbage (disabled));
  CHECK (f.sorted (kept) == lits ({1, 3, 4}));
  CHECK_EQ (f.internal.stats.rootunits, 0);
  CHECK_EQ (f.internal.stats.rootstrengthened, 0);
  CHECK_EQ (f.internal.stats.rootdeleted, 1);
  const std::vector<std::string> expected = {"d 4"};
  CHECK (f.steps (before) == expected);
}

// Mode 1, 'forall 1 exists 2': (2) assigns 2 and (1 -2) forces the
// secondary 1.  The unit of 1 reduces to the empty clause.
static void test_secondary_unit () {
  Fixture f ("ae", true, 1);
  f.add (Clause, {2});
  f.add (Clause, {1, -2});
  CHECK (f.internal.propagate () == Ref::none);
  CHECK (f.internal.val (L (1)) > 0);
  CHECK (f.simplify () == Ref::none);
  CHECK (f.internal.status == Status::False);
  const std::vector<std::string> expected = {"a 3 c: : 2 1", "e c 3"};
  CHECK (f.steps (2) == expected);
}

// Step 2 for clauses: in 'exists 1 2 forall 3 exists 4', (1 2 3 4) under
// the unit (-4) loses 4, and the reduction then removes 3.
static void test_strengthen_clause (bool traced) {
  Fixture f ("eeae", traced);
  f.add (Clause, {-4});
  const Ref c = f.add (Clause, {1, 2, 3, 4});
  CHECK (f.simplify () == Ref::none);
  CHECK (!f.garbage (c));
  CHECK (f.sorted (c) == lits ({1, 2}));
  CHECK_EQ (f.internal.stats.rootstrengthened, 1);
  CHECK_EQ (f.internal.stats.rootlits, 2);
  CHECK_EQ (f.internal.next_id, 4u);
  if (traced) {
    CHECK_EQ (deref (f.internal.arena, c).id (), 3u);
    const std::vector<std::string> expected = {"a 3 c: 1 2 : 2 1", "d 2"};
    CHECK (f.steps (2) == expected);
  }
  f.internal.check_invariants ();
}

// Step 2 for cubes: the unit cube (-1) assigns 1, which vanishes in the
// cube (1 2 3); step 3 deletes (-1 2 3), disabled by -1.
static void test_strengthen_cube () {
  Fixture f ("aaa", true);
  f.add (Cube, {-1});
  const Ref c = f.add (Cube, {1, 2, 3});
  const Ref d = f.add (Cube, {-1, 2, 3});
  CHECK (f.simplify () == Ref::none);
  CHECK (f.sorted (c) == lits ({2, 3}));
  CHECK (f.garbage (d));
  const std::vector<std::string> expected = {"a 4 t: 2 3 : 2 1", "d 2",
                                             "d 3"};
  CHECK (f.steps (3) == expected);
}

// 'exists 1 forall 2 exists 3': (1 2 3) under (-3) becomes (1 2), reduced
// to the unit (1), which is stored after the pass and assigns 1.  Without
// 3 it would be (2 3) with 2 the only universal: the empty clause.
static void test_strengthen_unit () {
  Fixture f ("eae", true);
  f.add (Clause, {-3});
  const Ref c = f.add (Clause, {1, 2, 3});
  CHECK (f.simplify () == Ref::none);
  CHECK (f.garbage (c));
  CHECK (f.internal.val (L (1)) > 0 && f.unit_reason (1));
  const std::vector<std::string> expected = {"a 3 c: 1 : 2 1", "d 2"};
  CHECK (f.steps (2) == expected);
  CHECK (f.internal.propagate () == Ref::none);
  // The next run sees 1 as new and finds nothing to do.
  CHECK (f.internal.simplifying ());
  CHECK (f.internal.simplify_root () == Ref::none);
  CHECK_EQ (f.internal.stats.rootunits, 0);
}

static void test_strengthen_empty () {
  Fixture f ("aae", true);
  f.add (Clause, {-3});
  f.add (Clause, {1, 2, 3});
  CHECK (f.simplify () == Ref::none);
  CHECK (f.internal.status == Status::False);
  const std::vector<std::string> expected = {"a 3 c: : 2 1", "e c 3"};
  CHECK (f.steps (2) == expected);
}

// 'forall 1 exists 2 forall 3 4 exists 5': (1) as a cube assigns -1, so
// (1 -2) forces -2 without a clause unit; (-5) assigns -5.  (2 3 4 5) loses
// 5 and is reduced to (2), which has vanished: a root conflict, which the
// analysis turns into the empty clause.
static void test_root_conflict () {
  Fixture f ("aeaae", true);
  f.add (Cube, {1});
  f.add (Clause, {1, -2});
  f.add (Clause, {-5});
  f.add (Clause, {2, 3, 4, 5});
  const Ref conflict = f.simplify ();
  CHECK (conflict != Ref::none);
  CHECK (stored (f.internal, conflict) == lits ({2}));
  f.internal.analyze (conflict);
  CHECK (f.internal.status == Status::False);
  const std::vector<std::string> expected = {"a 5 c: 2 : 4 3", "d 4",
                                             "a 6 c: : 5 2", "e c 6"};
  CHECK (f.steps (4) == expected);
}

// The same, with 3 existential: (2 3 5) under (-5) becomes (2 3), whose
// only non-vanished literal is 3.  The constraint is watched by 3 and 2,
// and propagation goes back to -2 and propagates 3.
static void test_unit_by_reduction () {
  Fixture f ("aeeae", true);
  f.add (Cube, {1});
  f.add (Clause, {1, -2});
  f.add (Clause, {-5});
  const Ref c = f.add (Clause, {2, 3, 4, 5});
  CHECK (f.simplify () == Ref::none);
  CHECK (stored (f.internal, c) == lits ({3, 2}));
  CHECK (f.internal.propagated < f.internal.trail.size ());
  CHECK (f.internal.propagate () == Ref::none);
  CHECK (f.internal.val (L (3)) > 0 && f.internal.reason (2) == c);
  f.internal.check_invariants ();
}

// (1 2 3) is first watched by 1 and 2; propagating -1 moves the watch to 3
// and leaves 1 as the blocker of the watch on 2.  Removing 1 rewrites the
// watches, and the constraint propagates 3 after the decision -2.
static void test_watches_after_removal () {
  Fixture f ("eee", false);
  f.add (Clause, {-1});
  const Ref c = f.add (Clause, {1, 2, 3});
  CHECK (f.simplify () == Ref::none);
  CHECK_EQ (deref (f.internal.arena, c).size (), 2u);
  f.internal.check_invariants ();
  decide (f.internal, -2);
  CHECK (f.internal.propagate () == Ref::none);
  CHECK (f.internal.val (L (3)) > 0 && f.internal.reason (2) == c);
}

// A redundant constraint stays redundant and keeps its 'used' mark; its
// glue is capped at the new size.
static void test_redundant () {
  Fixture f ("eeeee", false);
  f.add (Clause, {-1});
  Internal &internal = f.internal;
  const Ref c = internal.new_constraint (internal.next_id++, Clause,
                                         lits ({1, 2, 3, 4, 5}), true, 5);
  const Ref d = internal.new_constraint (internal.next_id++, Clause,
                                         lits ({1, 2, 3}), true, 3);
  deref (internal.arena, c).set_used (2);
  deref (internal.arena, d).set_used (1);
  CHECK (f.simplify () == Ref::none);
  const Constraint &x = deref (internal.arena, c);
  const Constraint &y = deref (internal.arena, d);
  CHECK (x.redundant () && x.size () == 4 && x.glue () == 4 &&
         x.used () == 2);
  CHECK (y.redundant () && y.size () == 2 && y.glue () == 2 &&
         y.used () == 1);
  CHECK_EQ (internal.redundant[0].size (), 2u);
}

// Off with '--no-rootsimp' and in mode 2; the throttle waits for as many
// propagations as stored literals after the last run.
static void test_schedule () {
  for (int mode : {0, 2}) {
    Fixture f ("eee", false, mode);
    f.internal.opts.rootsimp = mode == 2;
    f.add (Clause, {-1});
    const Ref c = f.add (Clause, {1, 2, 3});
    f.internal.init_model_cube ();
    CHECK (f.internal.propagate () == Ref::none);
    CHECK (!f.internal.simplifying ());
    CHECK_EQ (deref (f.internal.arena, c).size (), 3u);
  }
  Fixture f ("eee", false);
  f.internal.opts.rootsimpdelay = 1;
  f.add (Clause, {-1});
  f.add (Clause, {1, 2, 3});
  CHECK (f.simplify () == Ref::none);
  Internal &internal = f.internal;
  const int64_t limit = internal.stats.propagations + 3;
  CHECK_EQ (internal.lim.simplify, limit);
  // Nothing new on the trail.
  CHECK (!internal.simplifying ());
  internal.simplifier.trail = 0;
  internal.stats.propagations = limit - 1;
  CHECK (!internal.simplifying ());
  internal.stats.propagations = limit;
  CHECK (internal.simplifying ());
  internal.opts.rootsimpdelay = 0;
  internal.stats.propagations = 0;
  CHECK (internal.simplifying ());
}

int main () {
  for (bool traced : {false, true}) {
    test_units_clauses (traced);
    test_strengthen_clause (traced);
  }
  test_units_cubes ();
  test_other_kind ();
  test_secondary_unit ();
  test_strengthen_cube ();
  test_strengthen_unit ();
  test_strengthen_empty ();
  test_root_conflict ();
  test_unit_by_reduction ();
  test_watches_after_removal ();
  test_redundant ();
  test_schedule ();
  return test_result ();
}
