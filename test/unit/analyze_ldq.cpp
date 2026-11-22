// Long-distance analysis (analyze_ldq.cpp), mode 2, for clauses and cubes
// (the cube prefix swaps the quantifiers; a literal vanishes by being
// false in a clause and true in a cube).

#include "internal_test.hpp"
#include "test.hpp"

#include <string>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause;

static void declare_for (Internal &internal, Kind kind,
                         std::string prefix) {
  internal.opts.mode = 2;
  if (kind != Clause)
    for (char &c : prefix)
      c = c == 'e' ? 'a' : 'e';
  declare (internal, prefix.c_str ());
}

static int vanish (Kind kind, int dimacs) {
  return kind == Clause ? -dimacs : dimacs;
}

// 'exists 1 2 forall 3 exists 4' with A = (1 2 3 4) and B = (1 -2 -3 4).
// Under -4 (level 1) and -1 (level 2), A propagates 2 although 3 is
// unassigned (it is right of 2), and B is the conflict, with -3
// unassigned.  Resolving on 2 gives the long-distance resolvent
// (1 4 3 -3): 3 and -3 are both right of the pivot.  It asserts 1 on
// level 2 (no secondary literal is left of it) and is watched by 1 and 4,
// so it backjumps to level 1.
static void test_long_distance_resolvent (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "eeae");
  const Ref a = add (internal, kind, {1, 2, 3, 4});
  const Ref b = add (internal, kind, {1, -2, -3, 4});
  decide (internal, vanish (kind, 4));
  CHECK (internal.propagate () == Ref::none);
  decide (internal, vanish (kind, 1));
  const Ref conflict = internal.propagate ();
  CHECK (conflict == b);
  CHECK (internal.reason (1) == a && !internal.val (L (3)));
  internal.analyze (conflict);
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK_EQ (internal.stats.learned[index (kind)], 1);
  const Ref learnt = internal.redundant[index (kind)].back ();
  CHECK (stored (internal, learnt) == lits ({1, 4, 3, -3}));
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.kval (kind, L (1)) > 0 && internal.reason (0) == learnt);
  CHECK_EQ (deref (internal.arena, learnt).glue (), 2u);
  CHECK (internal.propagate () == Ref::none);
  internal.check_invariants ();
}

// 'exists 1 forall 2 exists 3' with (1 2 3) and (1 -2 3).  Under -1
// (level 1) both are watched by 3 and the unassigned 2 left of it; when 3
// vanishes too (level 2), no primary literal is left: a conflict.  Its
// primary literals are decisions, and the unassigned 2 left of 3 keeps it
// from asserting, so with '--dl' the analysis learns that 3 depends on 2
// and backtracks below 3.
static void test_dependency (Kind kind) {
  Internal internal;
  internal.opts.dl = 1;
  declare_for (internal, kind, "eae");
  add (internal, kind, {1, 2, 3});
  add (internal, kind, {1, -2, 3});
  decide (internal, vanish (kind, 1));
  CHECK (internal.propagate () == Ref::none);
  decide (internal, vanish (kind, 3));
  const Ref conflict = internal.propagate ();
  CHECK (conflict != Ref::none);
  internal.analyze (conflict);
  CHECK_EQ (internal.stats.dependencies, 1);
  CHECK_EQ (internal.stats.learned[index (kind)], 0);
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.depend.on[2].size () == 1 &&
         internal.depend.on[2][0] == 1);
}

// Resolving every primary literal away at the root gives the empty
// constraint: (1 2) and (1 -2) with the unit (-1) for 'exists 1 2'.
static void test_empty (Kind kind) {
  Internal internal;
  declare_for (internal, kind, "ee");
  add (internal, kind, {1, 2});
  add (internal, kind, {1, -2});
  add (internal, kind, {-1});
  const Ref conflict = internal.propagate ();
  CHECK (conflict != Ref::none);
  internal.analyze (conflict);
  CHECK (internal.status ==
         (kind == Clause ? Status::False : Status::True));
}

int main () {
  for (Kind kind : {Kind::Clause, Kind::Cube}) {
    test_long_distance_resolvent (kind);
    test_dependency (kind);
    test_empty (kind);
  }
  return test_result ();
}
