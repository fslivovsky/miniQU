// Backtracking: values, trail, heaps, block counters and saved phases
// (backtrack.cpp).

#include "internal_test.hpp"
#include "test.hpp"

using namespace miniqu;

// Decides 'dimacs' as 'decide.cpp' will: popped from the heap of its block.
static void pop_and_decide (Internal &internal, int dimacs) {
  const Var v = var (L (dimacs));
  CHECK (internal.heaps[internal.prefix.depth (v)].pop () == v);
  decide (internal, dimacs);
  CHECK (internal.propagate () == Ref::none);
}

static void test_phases (int phasesaving, std::vector<int> expected) {
  Internal internal;
  internal.opts.phasesaving = phasesaving;
  declare (internal, "eeaee");
  add (internal, Kind::Clause, {-1, 2});
  add (internal, Kind::Clause, {-4, 5});
  pop_and_decide (internal, 1);
  pop_and_decide (internal, 3);
  pop_and_decide (internal, 4);
  CHECK (internal.trail == lits ({1, 2, 3, 4, 5}));
  CHECK_EQ (internal.decision_level (), 3);
  for (const Block &b : internal.prefix.blocks)
    CHECK_EQ (b.unassigned, 0);
  CHECK (!internal.heaps[2].contains (3));
  internal.check_invariants ();

  internal.backtrack (1);
  CHECK (internal.trail == lits ({1, 2}));
  CHECK_EQ (internal.decision_level (), 1);
  CHECK_EQ (internal.propagated, 2u);
  for (int v = 3; v <= 5; v++)
    CHECK (!internal.val (L (v)));
  CHECK_EQ (internal.prefix.blocks[1].unassigned, 1);
  CHECK_EQ (internal.prefix.blocks[2].unassigned, 2);
  CHECK (internal.heaps[1].contains (2));
  CHECK (internal.heaps[2].contains (3) && internal.heaps[2].contains (4));
  std::vector<int> phases;
  for (Var v = 0; v < 5; v++)
    phases.push_back (internal.phases[v]);
  CHECK (phases == expected);
  internal.check_invariants ();

  // Backtracking to the current level changes nothing; propagation
  // continues from the restored head.
  internal.backtrack (1);
  CHECK_EQ (internal.trail.size (), 2u);
  pop_and_decide (internal, 4);
  CHECK (internal.trail == lits ({1, 2, 4, 5}));
  internal.backtrack (0);
  CHECK (internal.trail.empty () && internal.control.empty ());
  CHECK_EQ (internal.propagated, 0u);
  CHECK_EQ (internal.prefix.blocks[0].unassigned, 2);
  CHECK (internal.heaps[0].contains (0) && internal.heaps[0].contains (1));
  internal.check_invariants ();
}

int main () {
  // The initial phase is false.  Saving level 1 keeps only the implied
  // literals of the highest level undone (5), not its decision (4) and not
  // the lower levels (3); level 2 keeps everything.
  test_phases (0, {-1, -1, -1, -1, -1});
  test_phases (1, {-1, -1, -1, -1, 1});
  test_phases (2, {-1, -1, 1, 1, 1});
  return test_result ();
}
