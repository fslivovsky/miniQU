// Long-distance propagation (propagate_ldq.cpp), mode 2: the prefix-aware
// unit rule, the conflict rule, stale watch entries, and garbage
// collection with a stale entry of a deleted constraint.  Every case runs
// for clauses and for cubes: the cube prefix swaps the quantifiers, and a
// literal is made to vanish by assigning it false in a clause and true in
// a cube.

#include "internal_test.hpp"
#include "test.hpp"

#include <string>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause;

static bool in_list (const Internal &internal, Kind kind, Lit key,
                     Ref ref) {
  for (const Watch &w : internal.watches (kind, key))
    if (w.ref == ref)
      return true;
  return false;
}

// Declares the prefix for clauses ('e' primary), with quantifiers swapped
// for cubes.
static void declare_for (Internal &internal, Kind kind,
                         std::string prefix) {
  internal.opts.mode = 2;
  if (kind != Clause)
    for (char &c : prefix)
      c = c == 'e' ? 'a' : 'e';
  declare (internal, prefix.c_str ());
}

// The decision under which the literal 'dimacs' vanishes.
static int vanish (Kind kind, int dimacs) {
  return kind == Clause ? -dimacs : dimacs;
}

// 'exists 1 forall 2 exists 3' with (1 2 3): under -1, the only primary
// literal left is 3, but the unassigned 2 left of it blocks it.  Once 2
// vanishes too, 3 is propagated on that level.
static void test_left_secondary_blocks (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "eae");
  const Ref r = add (internal, kind, {1, 2, 3});
  decide (internal, vanish (kind, 1));
  CHECK (internal.propagate () == Ref::none);
  CHECK (!internal.val (L (3)));
  CHECK (stored (internal, r) == lits ({3, 2, 1}));
  internal.check_invariants ();
  decide (internal, vanish (kind, 2));
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.kval (kind, L (3)) > 0);
  CHECK (internal.reason (2) == r);
  CHECK_EQ (internal.level (2), 2);
  internal.check_invariants ();
}

// A secondary literal right of the last primary one does not block: in
// 'exists 1 2 forall 3 exists 4' with (1 2 3 4), under -1 and -4 the
// literal 2 is propagated although 3 is unassigned.
static void test_right_secondary_does_not_block (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "eeae");
  const Ref r = add (internal, kind, {1, 2, 3, 4});
  decide (internal, vanish (kind, 1));
  CHECK (internal.propagate () == Ref::none);
  decide (internal, vanish (kind, 4));
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.kval (kind, L (2)) > 0 && internal.reason (1) == r);
  CHECK (!internal.val (L (3)));
  internal.check_invariants ();
}

// After -1 the constraint (1 2 3) is watched by 3 and 2; when 3 vanishes
// as well, no primary literal is left: a conflict, although 2 is
// unassigned (no completion as in mode 0).
static void test_conflict (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "eae");
  const Ref r = add (internal, kind, {1, 2, 3});
  decide (internal, vanish (kind, 1));
  CHECK (internal.propagate () == Ref::none);
  decide (internal, vanish (kind, 3));
  CHECK (internal.propagate () == r);
  CHECK (!internal.val (L (2)));
  CHECK_EQ (internal.propagated, 1u);
}

// 'forall 1 2 3 exists 4' (for clauses) with (1 2 3 4), first watched by
// 1 and 2.  When 2 vanishes, position 0 (the secondary 1) gives way to the
// primary 4 and position 1 goes to 3, left of 4: the entry of 1 is stale.
// Meeting it later drops it.
static void test_stale_entry (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "aaae");
  const Ref r = add (internal, kind, {1, 2, 3, 4});
  const Lit key1 = watch_key (kind, L (1));
  CHECK (in_list (internal, kind, key1, r));
  decide (internal, vanish (kind, 2));
  CHECK (internal.propagate () == Ref::none);
  CHECK (stored (internal, r) == lits ({4, 3, 2, 1}));
  CHECK (in_list (internal, kind, key1, r));
  CHECK (in_list (internal, kind, watch_key (kind, L (4)), r));
  CHECK (in_list (internal, kind, watch_key (kind, L (3)), r));
  internal.check_invariants ();
  decide (internal, vanish (kind, 1));
  CHECK (internal.propagate () == Ref::none);
  CHECK (!in_list (internal, kind, key1, r));
  CHECK (!internal.val (L (4)));
  decide (internal, vanish (kind, 3));
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.kval (kind, L (4)) > 0 && internal.reason (3) == r);
  internal.check_invariants ();
}

// A stale entry of a deleted constraint stays in a list that deleting did
// not smudge; the invariant check accepts it and garbage collection drops
// it instead of relocating a deleted constraint.
static void test_stale_entry_of_garbage (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "aaae");
  const Ref r = add (internal, kind, {1, 2, 3, 4});
  add (internal, kind, {1, 3, 4}); // keeps the arena non-empty
  internal.init_model_cube ();
  decide (internal, vanish (kind, 2));
  CHECK (internal.propagate () == Ref::none);
  internal.backtrack (0);
  const Lit key1 = watch_key (kind, L (1));
  CHECK (in_list (internal, kind, key1, r));
  internal.mark_garbage (r);
  CHECK (!internal.watches.dirty (kind, key1));
  internal.check_invariants ();
  internal.garbage_collect ();
  CHECK_EQ (internal.stats.relocated, 1);
  CHECK (internal.watches (kind, key1).size () == 1);
  internal.check_invariants ();
}

int main () {
  for (Kind kind : {Kind::Clause, Kind::Cube}) {
    test_left_secondary_blocks (kind);
    test_right_secondary_does_not_block (kind);
    test_conflict (kind);
    test_stale_entry (kind);
    test_stale_entry_of_garbage (kind);
  }
  return test_result ();
}
