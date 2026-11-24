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
  internal.init_tiers ();
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
    internal.init_tiers ();
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
  internal.init_tiers ();
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
  internal.init_tiers ();
  internal.bump_constraint (deref (internal.arena, db.G)); // really 1
  CHECK_EQ (glue (internal, db.G), 5u);
  CHECK_EQ (internal.stats.glueupdates[0], 1);
  internal.opts.tier1glue = 0;
  internal.init_tiers ();

  // From tier 3 into tier 2 only: counted as promotion once, and a drop
  // within tier 2 is a glue update without promotion.
  internal.opts.tier2glue = 3;
  internal.init_tiers ();
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
  internal.init_tiers ();
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
  internal.init_tiers ();
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
  internal.init_tiers ();
  internal.opts.tier1glue = 0;
  internal.init_tiers ();
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

// Fills the histogram of a kind: 'uses[g]' uses of glue g.
static void fill (Internal &internal, Kind kind,
                  std::initializer_list<int64_t> uses) {
  auto &histogram = internal.tiers.usage[index (kind)];
  histogram.fill (0);
  size_t glue = 0;
  for (int64_t n : uses)
    histogram[glue++] = n;
}

static std::array<int, 2> limits (const Internal &internal, Kind kind) {
  return {internal.tiers.tier1[index (kind)],
          internal.tiers.tier2[index (kind)]};
}

// The limits are the smallest glues that cover 'tier1limit' and
// 'tier2limit' percent of the uses, per kind.
static void test_retier_from_histogram () {
  Internal internal;
  internal.opts.recomputetier = 1;
  internal.init_tiers ();
  CHECK ((limits (internal, Kind::Clause) == std::array<int, 2>{2, 6}));

  // All clause uses at glue 1; cube uses spread over glue 1..10.
  fill (internal, Kind::Clause, {0, 100});
  fill (internal, Kind::Cube, {0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10});
  internal.retier ();
  CHECK_EQ (internal.stats.retiered, 1);
  // Clause tier 2 is raised above tier 1.
  CHECK ((limits (internal, Kind::Clause) == std::array<int, 2>{1, 2}));
  // 50% of 100 uses is reached at glue 5, 90% at glue 9.
  CHECK ((limits (internal, Kind::Cube) == std::array<int, 2>{5, 9}));

  // The kinds move independently: more clause uses at glue 3 leave the
  // cube limits where they are.
  fill (internal, Kind::Clause, {0, 50, 0, 50});
  internal.retier ();
  CHECK ((limits (internal, Kind::Clause) == std::array<int, 2>{1, 3}));
  CHECK ((limits (internal, Kind::Cube) == std::array<int, 2>{5, 9}));
  CHECK_EQ (internal.stats.retiered, 2);
}

// A kind without uses keeps its limits; uses of glue 0 count for every
// limit; the last bucket stands for every glue above.
static void test_retier_edges () {
  Internal internal;
  internal.opts.recomputetier = 1;
  internal.opts.tier1glue = 3;
  internal.opts.tier2glue = 8;
  internal.init_tiers ();
  fill (internal, Kind::Cube, {0, 0, 0, 0, 0, 7});
  internal.retier ();
  CHECK ((limits (internal, Kind::Clause) == std::array<int, 2>{3, 8}));
  CHECK ((limits (internal, Kind::Cube) == std::array<int, 2>{5, 6}));

  fill (internal, Kind::Cube, {100, 1});
  internal.retier ();
  CHECK ((limits (internal, Kind::Cube) == std::array<int, 2>{1, 2}));

  internal.tiers.usage[1].fill (0);
  internal.tiers.usage[1][Tiers::buckets - 1] = 5;
  internal.retier ();
  CHECK_EQ (internal.tiers.tier1[1], Tiers::buckets - 1);
  CHECK_EQ (internal.tiers.tier2[1], Tiers::buckets);
}

// The minimum glues are applied before tier 2 is forced above tier 1, and
// the percentages are the options.
static void test_retier_options () {
  Internal internal;
  internal.opts.recomputetier = 1;
  internal.opts.tier1minglue = 4;
  internal.opts.tier2minglue = 3;
  internal.init_tiers ();
  fill (internal, Kind::Clause, {0, 100});
  internal.retier ();
  CHECK ((limits (internal, Kind::Clause) == std::array<int, 2>{4, 5}));

  internal.opts.tier1minglue = 0;
  internal.opts.tier2minglue = 0;
  internal.opts.tier1limit = 10;
  internal.opts.tier2limit = 100;
  fill (internal, Kind::Clause,
        {0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10});
  internal.retier ();
  CHECK ((limits (internal, Kind::Clause) == std::array<int, 2>{1, 10}));
}

// The schedule: first after 2 conflicts, then 2^count conflicts later up
// to 2^16, only with the option.
static void test_retier_schedule () {
  Internal internal;
  internal.init_tiers ();
  internal.stats.conflicts = 1000;
  CHECK (!internal.retiering ());
  internal.opts.recomputetier = 1;
  internal.init_tiers ();
  internal.stats.conflicts = 1;
  CHECK (!internal.retiering ());
  internal.stats.conflicts = 2;
  CHECK (internal.retiering ());
  internal.retier ();
  CHECK_EQ (internal.lim.retier, 4);
  internal.stats.conflicts = 4;
  internal.retier ();
  CHECK_EQ (internal.lim.retier, 4 + 4);
  internal.stats.retiered = 20;
  internal.stats.conflicts = 100;
  internal.retier ();
  CHECK_EQ (internal.lim.retier, 100 + 65536);
}

// Bumping records the updated glue in the histogram of its kind, only
// with the option, and the glue recomputed above the cutoff
// (tier1 + 1) / 2 instead of above tier 1.
static void test_bump_histogram () {
  Database db;
  Internal &internal = db.internal;
  db.propagate_reasons ();
  internal.bump_constraint (deref (internal.arena, db.E)); // 4 -> 2
  for (const auto &histogram : internal.tiers.usage)
    for (int64_t uses : histogram)
      CHECK_EQ (uses, 0);

  // Glue 2 is not above tier 1 (limit 2), so it stays...
  Constraint &b = deref (internal.arena, db.B);
  CHECK_EQ (b.glue (), 2u);
  internal.bump_constraint (b);
  CHECK_EQ (b.glue (), 2u);

  // ... but it is above the cutoff 1 with the option, and drops to 1.
  internal.opts.recomputetier = 1;
  internal.bump_constraint (b);
  CHECK_EQ (b.glue (), 1u);
  internal.bump_constraint (deref (internal.arena, db.U4)); // 4 -> 2
  CHECK_EQ (internal.tiers.usage[0][1], 1);
  CHECK_EQ (internal.tiers.usage[1][2], 1);

  // The cutoff is that of the kind of the constraint.
  internal.tiers.tier1[1] = 3; // cutoff 2: glue 4 is above
  Constraint &u = deref (internal.arena, db.U5);
  u.set_glue (4);
  internal.bump_constraint (u);
  CHECK_EQ (u.glue (), 2u);
  internal.tiers.tier1[1] = 5; // cutoff 3: not above
  u.set_glue (3);
  internal.bump_constraint (u);
  CHECK_EQ (u.glue (), 3u);
  CHECK_EQ (internal.tiers.usage[1][3], 1);
}

// Marks use the limit of the kind of the constraint.
static void test_marks_per_kind () {
  Database db;
  Internal &internal = db.internal;
  internal.tiers.tier2[0] = 1;
  internal.tiers.tier2[1] = 5;
  db.propagate_reasons ();
  internal.bump_constraint (deref (internal.arena, db.E));  // glue 2
  internal.bump_constraint (deref (internal.arena, db.U4)); // glue 2
  CHECK_EQ (used (internal, db.E), 1u);
  CHECK_EQ (used (internal, db.U4), 2u);
}

int main () {
  test_retier_from_histogram ();
  test_retier_edges ();
  test_retier_options ();
  test_retier_schedule ();
  test_bump_histogram ();
  test_marks_per_kind ();
  test_marked_on_learning ();
  test_bump_lowers_glue ();
  test_bump_never_raises ();
  test_switches ();
  for (int mode : {0, 1, 2})
    test_bump_in_analysis (mode);
  return test_result ();
}
