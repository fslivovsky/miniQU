// Usage marks and glue updates (tier.cpp): the marks of new learnt
// constraints, 'bump_constraint' directly and from the analyses.

#include "database.hpp"
#include "test.hpp"

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause;

static uint32_t used (const Internal &internal, Ref ref) {
  return deref (internal.arena, ref).used ();
}
static uint32_t glue (const Internal &internal, Ref ref) {
  return deref (internal.arena, ref).glue ();
}

// Learns (-2 1) with glue 2 (see test/unit/search.cpp) and returns it.
static Ref learn_clause (Internal &internal) {
  declare (internal, "aee");
  add (internal, Clause, {1, -2, 3});
  add (internal, Clause, {1, -2, -3});
  decide (internal, -1);
  decide (internal, 2);
  const Ref conflict = internal.propagate ();
  CHECK (conflict != Ref::none);
  internal.analyze (conflict);
  CHECK_EQ (internal.redundant[0].size (), 1u);
  return internal.redundant[0][0];
}

// A new learnt constraint is marked by its tier.
static void test_marked_on_learning () {
  {
    Internal internal;
    const Ref learnt = learn_clause (internal);
    CHECK_EQ (glue (internal, learnt), 2u);
    CHECK_EQ (used (internal, learnt), 2u);
  }
  {
    Internal internal;
    internal.opts.tier2glue = 1;
    CHECK_EQ (used (internal, learn_clause (internal)), 1u);
  }
  {
    Internal internal;
    internal.opts.tiers = 0;
    CHECK_EQ (used (internal, learn_clause (internal)), 0u);
  }
}

// Variables 1, 5 are on level 1 and 3, -4 on level 2 (see database.hpp);
// the glue of a constraint that is partly unassigned counts its assigned
// literals only.
//   E {1 2 3 5}: levels 1, -, 2, 1  -> 2        I {3 6}: 2, -  -> 1
//   U4 {-1 -2 3 -4}: 1, -, 2, 2     -> 2
static void test_bump_lowers_glue () {
  Database db;
  Internal &internal = db.internal;
  db.propagate_reasons ();

  // Glue 4 to 2 enters tier 1 (2 <= tier1glue).
  internal.bump_constraint (deref (internal.arena, db.E));
  CHECK_EQ (glue (internal, db.E), 2u);
  CHECK_EQ (used (internal, db.E), 2u);
  CHECK_EQ (internal.stats.used[0], 1);
  CHECK_EQ (internal.stats.glueupdates[0], 1);
  CHECK_EQ (internal.stats.promoted[0], 1);
  // Bumping again changes nothing but the use count.
  internal.bump_constraint (deref (internal.arena, db.E));
  CHECK_EQ (glue (internal, db.E), 2u);
  CHECK_EQ (internal.stats.used[0], 2);
  CHECK_EQ (internal.stats.glueupdates[0], 1);

  // Tier 1 is not recomputed.
  internal.opts.tier1glue = 5;
  internal.bump_constraint (deref (internal.arena, db.G)); // really 1
  CHECK_EQ (glue (internal, db.G), 5u);
  CHECK_EQ (internal.stats.glueupdates[0], 1);
  internal.opts.tier1glue = 0;

  // From tier 3 into tier 2 only: counted as promotion once, and a drop
  // within tier 2 is a glue update without promotion.
  internal.opts.tier2glue = 3;
  internal.bump_constraint (deref (internal.arena, db.I)); // 4 -> 1
  CHECK_EQ (glue (internal, db.I), 1u);
  CHECK_EQ (internal.stats.promoted[0], 2);
  deref (internal.arena, db.D).set_glue (3);
  internal.bump_constraint (deref (internal.arena, db.D)); // {1 3 6}: 1, 2
  CHECK_EQ (glue (internal, db.D), 2u);
  CHECK_EQ (internal.stats.glueupdates[0], 3);
  CHECK_EQ (internal.stats.promoted[0], 2);

  // The same for cubes, counted apart.
  internal.bump_constraint (deref (internal.arena, db.U4));
  CHECK_EQ (glue (internal, db.U4), 2u);
  CHECK_EQ (internal.stats.used[1], 1);
  CHECK_EQ (internal.stats.glueupdates[1], 1);
  CHECK_EQ (internal.stats.promoted[1], 1);
  CHECK_EQ (used (internal, db.U4), 2u);
}

// A recomputed glue that is not lower, which can happen because fewer
// literals were assigned when the glue was counted, is not stored.
static void test_bump_never_raises () {
  Database db;
  Internal &internal = db.internal;
  internal.opts.tier1glue = 0;
  db.propagate_reasons ();
  deref (internal.arena, db.U4).set_glue (1); // really 2
  internal.bump_constraint (deref (internal.arena, db.U4));
  CHECK_EQ (glue (internal, db.U4), 1u);
  CHECK_EQ (internal.stats.glueupdates[1], 0);
  CHECK_EQ (internal.stats.used[1], 1);
}

// '--no-glueupdate' leaves the glue and still marks; '--no-tiers' leaves
// the marks; irredundant constraints are not touched at all.
static void test_switches () {
  Database db;
  Internal &internal = db.internal;
  db.propagate_reasons ();
  internal.opts.glueupdate = 0;
  internal.bump_constraint (deref (internal.arena, db.E));
  CHECK_EQ (glue (internal, db.E), 4u);
  CHECK_EQ (used (internal, db.E), 2u); // glue 4 <= tier2glue 6
  internal.opts.glueupdate = 1;
  internal.opts.tiers = 0;
  internal.bump_constraint (deref (internal.arena, db.I));
  CHECK_EQ (glue (internal, db.I), 1u);
  CHECK_EQ (used (internal, db.I), 0u);

  const Ref original = internal.irredundant[0][0];
  const int64_t used_before = internal.stats.used[0];
  internal.bump_constraint (deref (internal.arena, original));
  CHECK_EQ (internal.stats.used[0], used_before);
  CHECK_EQ (deref (internal.arena, original).glue (), 0u);
  CHECK_EQ (deref (internal.arena, original).used (), 0u);
}

// The conflict and the reasons resolved with are bumped by the analysis
// (mode 0, 1 and 2 alike), the constraint it learns is marked.  Under the
// decisions 4 and 1, the clauses (-1 2) and (-1 -2 3) force 2 and 3 and
// (-1 -2 -3) is the conflict; resolving gives the unit (-1).
static void test_bump_in_analysis (int mode) {
  Internal internal;
  internal.opts.mode = mode;
  internal.opts.tier1glue = 0;
  declare (internal, "eeee");
  internal.size_watches ();
  const Ref reason2 = internal.new_constraint (internal.next_id++, Clause,
                                               lits ({-1, 2}), true, 9);
  const Ref reason3 = internal.new_constraint (internal.next_id++, Clause,
                                               lits ({-1, -2, 3}), true, 9);
  const Ref conflict = internal.new_constraint (
      internal.next_id++, Clause, lits ({-1, -2, -3}), true, 9);
  decide (internal, 4);
  decide (internal, 1);
  CHECK (internal.propagate () == conflict);
  internal.analyze (conflict);
  CHECK_EQ (internal.stats.used[0], 3);
  CHECK_EQ (internal.stats.used[1], 0);
  for (Ref ref : {reason2, reason3, conflict}) {
    CHECK_EQ (glue (internal, ref), 1u);
    CHECK_EQ (used (internal, ref), 2u);
  }
}

int main () {
  test_marked_on_learning ();
  test_bump_lowers_glue ();
  test_bump_never_raises ();
  test_switches ();
  for (int mode : {0, 1, 2})
    test_bump_in_analysis (mode);
  return test_result ();
}
