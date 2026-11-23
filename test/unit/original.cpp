// Original constraints: normalisation, reduction, units and the formula
// decided at input (constraint.cpp, prefix.cpp).

#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <memory>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

static void test_prefix () {
  Internal internal;
  declare (internal, "eEaeAa");
  const Prefix &prefix = internal.prefix;
  CHECK_EQ (prefix.blocks.size (), 4u);
  CHECK (prefix.blocks[0].quant == Quant::Exists);
  CHECK_EQ (prefix.blocks[0].begin, 0u);
  CHECK_EQ (prefix.blocks[0].end, 2u);
  CHECK_EQ (prefix.blocks[0].unassigned, 1);
  CHECK_EQ (prefix.blocks[1].unassigned, 1);
  CHECK_EQ (prefix.blocks[3].begin, 4u);
  CHECK_EQ (prefix.blocks[3].end, 6u);
  CHECK_EQ (prefix.blocks[3].unassigned, 1);
  CHECK_EQ (prefix.depth (5), 3u);
  CHECK_EQ (prefix.vars[3].proof, 4);
  CHECK (prefix.is_primary (Clause, 0) && !prefix.is_primary (Cube, 0));
  CHECK (prefix.is_primary (Cube, 2) && !prefix.is_primary (Clause, 2));
  // One heap per block, holding its decision variables.
  CHECK_EQ (internal.heaps.size (), 4u);
  CHECK (internal.heaps[0].contains (0) && !internal.heaps[0].contains (1));
  CHECK (internal.heaps[3].contains (5) && !internal.heaps[3].contains (4));

  // Trailing secondary literals go, in both kinds, also several of them
  // and from different blocks; all of them without a primary literal.  The
  // others keep their order.
  std::vector<Lit> ls = lits ({6, -3, 1, 4, -5});
  prefix.qreduce (ls, Clause);
  CHECK (ls == lits ({-3, 1, 4}));
  ls = lits ({1, 3, 4, 6});
  prefix.qreduce (ls, Cube);
  CHECK (ls == lits ({1, 3, 4, 6}));
  ls = lits ({1, 3, 4});
  prefix.qreduce (ls, Cube);
  CHECK (ls == lits ({1, 3}));
  ls = lits ({3, 5, 6});
  prefix.qreduce (ls, Clause);
  CHECK (ls.empty ());
  internal.check_invariants ();
}

// With a tracer, so that the constraints store their ids.
static void test_normalisation () {
  Internal internal;
  Proof proof{&internal};
  proof.connect (std::make_unique<Recorder> ());
  internal.proof = &proof;
  declare (internal, "eeae");
  // Duplicates are removed and the literals sorted.
  const Ref r = add (internal, Clause, {4, 1, -2, 1, 4});
  CHECK (stored (internal, r) == lits ({1, -2, 4}));
  CHECK_EQ (deref (internal.arena, r).id (), 1u);
  CHECK (!deref (internal.arena, r).redundant ());
  // A tautological clause and a contradictory cube are skipped without an
  // id and are not counted.
  add (internal, Clause, {1, 4, -1});
  add (internal, Cube, {3, -3});
  CHECK_EQ (internal.irredundant[0].size (), 1u);
  CHECK (internal.irredundant[1].empty ());
  CHECK_EQ (internal.next_id, 2u);
  CHECK_EQ (internal.stats.originals[0], 1);
  CHECK_EQ (internal.stats.originals[1], 0);
  // A reduced original takes two ids, the stored one is the second.
  const Ref reduced = add (internal, Clause, {1, 2, 3});
  CHECK (stored (internal, reduced) == lits ({1, 2}));
  CHECK_EQ (deref (internal.arena, reduced).id (), 3u);
  const Ref cube = add (internal, Cube, {-4, 3, 1});
  CHECK (stored (internal, cube) == lits ({1, 3}));
  CHECK_EQ (deref (internal.arena, cube).id (), 5u);
  CHECK_EQ (internal.stats.originals[0], 2);
  CHECK_EQ (internal.stats.originals[1], 1);
  // Stored without simplification under the root assignment.
  add (internal, Clause, {2});
  CHECK (internal.val (L (2)) > 0);
  const Ref unsimplified = add (internal, Clause, {-2, 4});
  CHECK (stored (internal, unsimplified) == lits ({-2, 4}));
  CHECK (internal.status == Status::Unknown);
  internal.check_invariants ();
  internal.proof = nullptr;
}

static void test_units () {
  Internal internal;
  declare (internal, "eaea");
  const Ref clause = add (internal, Clause, {-1});
  const Ref cube = add (internal, Cube, {2});
  // A unit clause assigns its literal, a unit cube the negation; both are
  // reasons on level 0 and are never watched.
  CHECK (internal.val (L (-1)) > 0);
  CHECK (internal.reason (0) == clause);
  CHECK (internal.val (L (-2)) > 0);
  CHECK (internal.reason (1) == cube);
  CHECK_EQ (internal.level (1), 0);
  CHECK (internal.trail == lits ({-1, -2}));
  CHECK (internal.watches (Clause, L (1)).empty ());
  CHECK (internal.watches (Cube, L (2)).empty ());
  // Without a tracer no id is stored.
  CHECK (!deref (internal.arena, clause).has_id ());
  // A clause reduced to a unit is assigned too, and the same unit twice
  // is stored twice and decides nothing.
  const Ref reduced = add (internal, Clause, {3, 4});
  CHECK (stored (internal, reduced) == lits ({3}));
  CHECK (internal.reason (2) == reduced);
  add (internal, Clause, {-1});
  CHECK_EQ (internal.irredundant[0].size (), 3u);
  CHECK (internal.reason (0) == clause);
  // A unit clause and a unit cube do not interact.
  CHECK (internal.status == Status::Unknown);
  internal.check_invariants ();
}

static void test_decided () {
  {
    // Complementary unit clauses: the empty clause takes an id.
    Internal internal;
    declare (internal, "ea");
    add (internal, Clause, {1});
    add (internal, Clause, {-1});
    CHECK (internal.status == Status::False);
    CHECK_EQ (internal.next_id, 4u);
    // Nothing is stored any more once the formula is decided, but the
    // ids are still those of the proof.
    add (internal, Clause, {1, 2});
    CHECK_EQ (internal.irredundant[0].size (), 2u);
    CHECK_EQ (internal.next_id, 6u);
    CHECK (internal.solve () == Status::False);
  }
  {
    Internal internal;
    declare (internal, "ea");
    add (internal, Cube, {-2});
    add (internal, Cube, {2});
    CHECK (internal.status == Status::True);
  }
  {
    // A clause over universal variables only reduces to the empty clause,
    // a cube over existential ones to the empty cube.
    Internal internal;
    declare (internal, "ae");
    add (internal, Clause, {1});
    CHECK (internal.status == Status::False);
    CHECK (internal.irredundant[0].empty ());
    CHECK_EQ (internal.next_id, 3u);
  }
  {
    Internal internal;
    declare (internal, "ae");
    add (internal, Cube, {-1, 2});
    CHECK (internal.status == Status::Unknown);
    add (internal, Cube, {2});
    CHECK (internal.status == Status::True);
  }
  {
    // The empty constraint as input (QDIMACS line "0").
    Internal internal;
    declare (internal, "e");
    add (internal, Clause, {});
    CHECK (internal.status == Status::False);
    CHECK_EQ (internal.next_id, 2u);
  }
}

int main () {
  test_prefix ();
  test_normalisation ();
  test_units ();
  test_decided ();
  return test_result ();
}
