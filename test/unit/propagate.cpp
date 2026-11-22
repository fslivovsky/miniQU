// The watch loop and the propagation driver (propagate.hpp,
// propagate.cpp), and lazy detaching of deleted constraints.

#include "propagate.hpp"
#include "internal_test.hpp"
#include "test.hpp"

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

static bool in_list (const Internal &internal, Kind kind, Lit key,
                     Ref ref) {
  for (const Watch &w : internal.watches (kind, key))
    if (w.ref == ref)
      return true;
  return false;
}

static void test_clause_chain () {
#ifdef MINIQU_LOGGING
  // Logging is exercised once, on a run that assigns and propagates.
  set_logging (true);
#endif
  Internal internal;
  declare (internal, "eeee");
  const Ref r1 = add (internal, Clause, {-1, 2});
  const Ref r2 = add (internal, Clause, {-2, -3, 4});
  add (internal, Clause, {3});
  CHECK (internal.propagate () == Ref::none);
  CHECK_EQ (internal.propagated, 1u);
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.trail == lits ({3, 1, 2, 4}));
  CHECK (internal.reason (1) == r1 && internal.reason (3) == r2);
  CHECK_EQ (internal.level (1), 1);
  CHECK_EQ (internal.level (3), 1);
  CHECK_EQ (internal.level (2), 0);
  CHECK_EQ (internal.propagated, 4u);
  CHECK_EQ (internal.stats.propagations, 4);
  internal.check_invariants ();
#ifdef MINIQU_LOGGING
  set_logging (false);
#endif
}

static void test_cube_chain () {
  Internal internal;
  declare (internal, "aaea");
  // A cube with a single non-vanished literal forces its negation.
  const Ref r1 = add (internal, Cube, {1, 2});
  const Ref r2 = add (internal, Cube, {-2, 3, 4});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.trail == lits ({1, -2}));
  CHECK (internal.reason (1) == r1);
  // The existential 3, left of the universal 4, keeps the second cube from
  // propagating; once it vanishes (is true), -4 is forced.
  decide (internal, 3);
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.trail == lits ({1, -2, 3, -4}));
  CHECK (internal.reason (3) == r2);
  CHECK_EQ (internal.level (3), 2);
  internal.check_invariants ();
}

static void test_conflicts () {
  for (int mode : {0, 1}) {
    Internal internal;
    internal.opts.mode = mode;
    declare (internal, "eeaa");
    add (internal, Clause, {-1, 2});
    const Ref clash = add (internal, Clause, {-1, -2});
    decide (internal, 1);
    const Ref conflict = internal.propagate ();
    CHECK (conflict == clash);
    CHECK (internal.kval (Clause, L (-1)) < 0 &&
           internal.kval (Clause, L (-2)) < 0);
    // 'propagated' stays at the literal whose propagation conflicted.
    CHECK_EQ (internal.propagated, 0u);
  }
  for (int mode : {0, 1}) {
    Internal internal;
    internal.opts.mode = mode;
    declare (internal, "aaee");
    add (internal, Cube, {1, 2});
    const Ref solution = add (internal, Cube, {1, -2});
    decide (internal, 1);
    const Ref conflict = internal.propagate ();
    CHECK (conflict == solution);
    CHECK (deref (internal.arena, conflict).kind () == Cube);
    CHECK (internal.kval (Cube, L (1)) < 0 &&
           internal.kval (Cube, L (-2)) < 0);
  }
}

// A clause whose only non-vanished literal is universal.
static void test_lone_secondary () {
  {
    // Mode 0: conflict, completed by assigning the vanishing value
    // without a reason on the current level.
    Internal internal;
    declare (internal, "aeA");
    const Ref r = add (internal, Clause, {1, 2});
    decide (internal, -2);
    CHECK (internal.propagate () == r);
    CHECK (internal.val (L (-1)) > 0);
    CHECK (internal.reason (0) == Ref::none);
    CHECK_EQ (internal.level (0), 1);
    CHECK (internal.lone == lit_undef);
  }
  {
    // The same for a cube with a lone existential: it vanishes by being
    // assigned true.
    Internal internal;
    declare (internal, "ea");
    const Ref r = add (internal, Cube, {1, 2});
    decide (internal, 2);
    CHECK (internal.propagate () == r);
    CHECK (internal.val (L (1)) > 0);
    CHECK (internal.reason (0) == Ref::none);
  }
  {
    // Mode 1: propagated with the clause as reason.
    Internal internal;
    internal.opts.mode = 1;
    declare (internal, "ae");
    const Ref r = add (internal, Clause, {1, 2});
    decide (internal, -2);
    CHECK (internal.propagate () == Ref::none);
    CHECK (internal.val (L (1)) > 0);
    CHECK (internal.reason (0) == r);
    internal.check_invariants ();
  }
  {
    // Lone::Ignore (vivification in mode 0): neither, but a primary lone
    // literal is still propagated.
    Internal internal;
    declare (internal, "aee");
    const Ref r = add (internal, Clause, {1, 2});
    const Ref s = add (internal, Clause, {-2, 3});
    decide (internal, -2);
    CHECK ((internal.propagate_watches<Clause, Lone::Ignore> (L (-2)) ==
            Ref::none));
    CHECK (!internal.val (L (1)));
    CHECK (in_list (internal, Clause, L (-2), r));
    internal.backtrack (0);
    decide (internal, 2);
    CHECK ((internal.propagate_watches<Clause, Lone::Ignore> (L (2)) ==
            Ref::none));
    CHECK (internal.val (L (3)) > 0 && internal.reason (2) == s);
  }
}

static void test_blockers_and_watches () {
  Internal internal;
  declare (internal, "eeee");
  const Ref r = add (internal, Clause, {1, 2, 3, 4});
  CHECK (in_list (internal, Clause, L (-1), r));
  CHECK (in_list (internal, Clause, L (-2), r));
  // The watch of 1 has the blocker 2: with 2 true the clause is not
  // loaded.  One tick per list visited, two lists per literal.
  internal.new_level ();
  internal.assign (L (2), Ref::none);
  internal.assign (L (-1), Ref::none);
  CHECK (internal.propagate () == Ref::none);
  CHECK_EQ (internal.stats.ticks, 4);
  CHECK (stored (internal, r) == lits ({1, 2, 3, 4}));
  internal.backtrack (0);

  // Without the blocker the clause is loaded and the watch moves to the
  // first literal that has not vanished, which takes position 1.
  internal.stats.ticks = 0;
  decide (internal, -1);
  CHECK (internal.propagate () == Ref::none);
  CHECK_EQ (internal.stats.ticks, 3);
  CHECK (stored (internal, r) == lits ({2, 3, 1, 4}));
  CHECK (!in_list (internal, Clause, L (-1), r));
  CHECK (in_list (internal, Clause, L (-3), r));
  internal.check_invariants ();
  // Unassigning does not move watches back.
  internal.backtrack (0);
  CHECK (in_list (internal, Clause, L (-3), r));
  internal.check_invariants ();
}

// A conflict stops the scan; the remaining watches of the list stay.
static void test_conflict_keeps_watches () {
  Internal internal;
  declare (internal, "eee");
  const Ref a = add (internal, Clause, {1, 2});
  const Ref b = add (internal, Clause, {1, 2, 3});
  internal.new_level ();
  for (int lit : {-2, -3, -1})
    internal.assign (L (lit), Ref::none);
  CHECK (internal.propagate () == a);
  CHECK_EQ (internal.watches (Clause, L (-2)).size (), 2u);
  CHECK (in_list (internal, Clause, L (-2), b));
  CHECK (stored (internal, b) == lits ({1, 2, 3}));
  CHECK_EQ (internal.stats.propagations, 1);
}

static void test_garbage () {
  Internal internal;
  declare (internal, "eee");
  const Ref a = add (internal, Clause, {1, 2});
  const Ref b = add (internal, Clause, {1, 3});
  const uint32_t words = deref (internal.arena, a).words ();
  internal.mark_garbage (a);
  CHECK (deref (internal.arena, a).garbage ());
  CHECK_EQ (internal.arena.wasted (), words);
  // Detaching is lazy: the entry stays until the list is looked up.
  CHECK (in_list (internal, Clause, L (-1), a));
  decide (internal, -1);
  CHECK (internal.propagate () == Ref::none);
  CHECK (!in_list (internal, Clause, L (-1), a));
  CHECK (in_list (internal, Clause, L (-2), a));
  CHECK (!internal.val (L (2)));
  CHECK (internal.val (L (3)) > 0 && internal.reason (2) == b);
  internal.check_invariants ();

  // Strict detaching removes both watches at once.
  internal.backtrack (0);
  internal.detach (b);
  CHECK (!in_list (internal, Clause, L (-1), b));
  CHECK (!in_list (internal, Clause, L (-3), b));
  internal.attach (b);
  internal.check_invariants ();

  // Shrinking accounts the words.
  internal.detach (b);
  internal.shrink_constraint (b, 1);
  CHECK_EQ (internal.arena.wasted (), words + 1);
  CHECK_EQ (deref (internal.arena, b).size (), 1u);
}

int main () {
  test_clause_chain ();
  test_cube_chain ();
  test_conflicts ();
  test_lone_secondary ();
  test_blockers_and_watches ();
  test_conflict_keeps_watches ();
  test_garbage ();
  return test_result ();
}
