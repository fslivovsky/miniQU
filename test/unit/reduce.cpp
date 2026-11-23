// Reduction of the learnt databases (reduce.cpp): the triggers, the old
// size schedule, the selection of the constraints to delete (M1 policy and
// tiers), the protection of reasons, and the deletion steps.

#include "database.hpp"
#include "test.hpp"

#include <string>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

static void test_schedule () {
  Internal internal;
  declare (internal, "eeeeeeee");
  for (int i = 1; i <= 7; i++)
    add (internal, Clause, {i, i + 1});
  // A third of the seven originals, but at least '--minlearnts'.
  internal.init_reduce ();
  CHECK (internal.lim.max_learnts > 2.33 &&
         internal.lim.max_learnts < 2.34);
  internal.opts.minlearnts = 10;
  internal.init_reduce ();
  CHECK_EQ (internal.lim.max_learnts, 10.0);

  // The limit grows by 10% at the 100th, 250th, 475th and 812th learnt
  // constraint: the interval starts at 100 and grows by 50%.
  double expected = internal.lim.max_learnts;
  for (int64_t n = 1; n <= 812; n++) {
    internal.adjust_learnt_limit ();
    if (n == 100 || n == 250 || n == 475 || n == 812)
      expected *= 1.1;
    CHECK_EQ (internal.lim.max_learnts, expected);
  }
}

static void test_triggers () {
  Database db;
  Internal &internal = db.internal;
  internal.opts.reduceint = 0;
  internal.init_reduce ();
  // Nine learnt clauses and six cubes, one original: the limit is 10 and
  // each assigned variable lowers the count.
  CHECK_EQ (internal.lim.max_learnts, 1.0 / 3);
  internal.lim.max_learnts = 15;
  // The size trigger is off by default.
  CHECK (!internal.reducing ());
  internal.opts.reducesize = 1;
  CHECK (internal.reducing ());
  internal.lim.max_learnts = 16;
  CHECK (!internal.reducing ());
  db.propagate_reasons ();
  internal.lim.max_learnts = 11;
  CHECK (internal.reducing ());
  internal.lim.max_learnts = 12;
  CHECK (!internal.reducing ());

  // '--reduceint' is a conflict trigger with arithmetic growth, alone or
  // together with the size trigger.
  internal.opts.reduceint = 2;
  internal.opts.reducesize = 0;
  internal.init_reduce ();
  internal.lim.max_learnts = 1;
  CHECK_EQ (internal.lim.reduce, 2);
  CHECK (!internal.reducing ());
  internal.stats.conflicts = 2;
  CHECK (internal.reducing ());
  internal.reduce ();
  CHECK_EQ (internal.lim.reduce, 2 + 2 * 1);
  internal.stats.conflicts = 3;
  CHECK (!internal.reducing ());
  internal.stats.conflicts = 4;
  CHECK (internal.reducing ());
  internal.reduce ();
  CHECK_EQ (internal.lim.reduce, 4 + 2 * 2);
  internal.stats.conflicts = 5;
  CHECK (!internal.reducing ());
  internal.opts.reducesize = 1;
  CHECK (internal.reducing ());
}

// Runs 'reduce' with reasons on the trail; 'deleted' are the constraints
// that have to go, in the order of the deletion steps (checked if traced).
// Without ids the order of equal glue and size is the same: creation order.
static void test_reduce (bool traced, int tier1glue,
                         std::vector<Ref Database::*> deleted, int clauses,
                         int cubes) {
  Database db (traced);
  Internal &internal = db.internal;
  internal.opts.tier1glue = tier1glue;
  // The M1 policy, with marks that would protect the constraints if
  // '--tiers' were on.
  internal.opts.tiers = 0;
  internal.opts.reducetarget = 50;
  for (Kind kind : {Clause, Cube})
    for (Ref ref : internal.redundant[index (kind)])
      deref (internal.arena, ref).set_used (2);
  // Keep the arena in place so that the references of 'db' stay valid.
  internal.opts.gcfrac = 100;
  db.propagate_reasons ();
  if (traced)
    db.recorder->steps.clear ();

  internal.reduce ();

  std::vector<std::string> expected;
  for (Ref Database::*member : deleted) {
    CHECK (db.garbage (db.*member));
    if (traced)
      expected.push_back ("d " + std::to_string (db.id (db.*member)));
  }
  if (traced)
    CHECK (db.recorder->steps == expected);
  CHECK_EQ (internal.stats.reductions, 1);
  CHECK_EQ (internal.stats.reduced[0], clauses);
  CHECK_EQ (internal.stats.reduced[1], cubes);
  CHECK_EQ (internal.stats.collections, 0);

  // Everything else lives on, in the lists, and the reasons are
  // unprotected again.
  size_t live = 0;
  for (Kind kind : {Clause, Cube})
    for (Ref ref : internal.redundant[index (kind)]) {
      CHECK (!deref (internal.arena, ref).garbage ());
      CHECK (!deref (internal.arena, ref).reason ());
      live++;
    }
  CHECK_EQ (live, 15 - deleted.size ());
  CHECK (!db.garbage (db.R) && !db.garbage (db.Q));
  CHECK_EQ (internal.reason (4), db.R);
  CHECK_EQ (internal.reason (3), db.Q);
  internal.check_invariants ();
}

// Without a reduction the reasons would be the first to go, and nothing
// is deleted below the glue limit.
static void test_everything_protected () {
  Database db;
  Internal &internal = db.internal;
  internal.opts.tier1glue = 1000;
  db.propagate_reasons ();
  internal.reduce ();
  CHECK_EQ (internal.stats.reduced[0] + internal.stats.reduced[1], 0);
  CHECK_EQ (internal.redundant[0].size (), 9u);
  CHECK_EQ (internal.redundant[1].size (), 6u);
}

// The tier policy: reasons are skipped (and keep their mark), a nonzero
// mark keeps a constraint and is decremented even in tier 1, tier 1 is
// kept, and the first 'reducetarget' percent of the rest, in (glue, size,
// creation) order, are deleted.  Candidates: clauses C D H I E (glue 3, 3,
// 3, 4, 4), cubes U2 U4 U5 (3, 4, 4); G and U3 are marked.
static void test_tiers (bool traced) {
  Database db (traced);
  Internal &internal = db.internal;
  internal.opts.gcfrac = 100;
  internal.opts.tiers = 1;
  internal.opts.reducetarget = 75;
  const auto mark = [&] (Ref ref, uint32_t used) {
    deref (internal.arena, ref).set_used (used);
  };
  const auto used = [&] (Ref ref) {
    return deref (internal.arena, ref).used ();
  };
  mark (db.G, 1);
  mark (db.U3, 2);
  mark (db.A, 2); // tier 1
  mark (db.R, 2); // a reason
  mark (db.Q, 1); // a reason
  db.propagate_reasons ();
  if (traced)
    db.recorder->steps.clear ();

  internal.reduce ();

  // 5 * 75 / 100 = 3 clauses: E, I (glue 4, by size) and C (the first
  // of the glue-3 clauses); 3 * 75 / 100 = 2 cubes: U4, U5.
  std::vector<std::string> expected;
  for (Ref ref : {db.E, db.I, db.C, db.U4, db.U5}) {
    CHECK (db.garbage (ref));
    if (traced)
      expected.push_back ("d " + std::to_string (db.id (ref)));
  }
  if (traced)
    CHECK (db.recorder->steps == expected);
  for (Ref ref :
       {db.A, db.B, db.D, db.H, db.G, db.R, db.U1, db.U2, db.U3, db.Q})
    CHECK (!db.garbage (ref));
  CHECK_EQ (internal.stats.reduced[0], 3);
  CHECK_EQ (internal.stats.reduced[1], 2);
  CHECK_EQ (used (db.G), 0u);
  CHECK_EQ (used (db.U3), 1u);
  CHECK_EQ (used (db.A), 1u);
  CHECK_EQ (used (db.R), 2u);
  CHECK_EQ (used (db.Q), 1u);

  // The marks wear off: G is a candidate now, with D and H.  Two of the
  // three go, G (glue 5) and the first of D and H.
  internal.reduce ();
  CHECK (db.garbage (db.G) && db.garbage (db.D));
  CHECK (!db.garbage (db.H));
  CHECK_EQ (used (db.A), 0u);
  internal.check_invariants ();
}

// With '--no-tiers' the marks are ignored and not changed.
static void test_no_tiers_ignores_marks () {
  Database db;
  Internal &internal = db.internal;
  internal.opts.gcfrac = 100;
  internal.opts.tiers = 0;
  internal.opts.reducetarget = 50;
  deref (internal.arena, db.G).set_used (2);
  db.propagate_reasons ();
  internal.reduce ();
  CHECK (db.garbage (db.G));
  // The mark is not decremented either (checked on a survivor).
  deref (internal.arena, db.D).set_used (1);
  internal.reduce ();
  CHECK_EQ (deref (internal.arena, db.D).used (), 1u);
}

// 'reducetarget' is a percentage of the candidates, rounded down.
static void test_target () {
  for (int target : {10, 25, 50, 100}) {
    Database db;
    Internal &internal = db.internal;
    internal.opts.gcfrac = 100;
    internal.opts.tiers = 0;
    internal.opts.reducetarget = target;
    db.propagate_reasons ();
    internal.reduce ();
    // Six clause and four cube candidates at the default tier-1 limit.
    CHECK_EQ (internal.stats.reduced[0], 6 * target / 100);
    CHECK_EQ (internal.stats.reduced[1], 4 * target / 100);
  }
}

// The collection after a reduction is due by 'gcfrac'.
static void test_collection_after_reduce (bool traced) {
  Database db (traced);
  Internal &internal = db.internal;
  internal.opts.gcfrac = 1;
  db.propagate_reasons ();
  internal.reduce ();
  CHECK_EQ (internal.stats.collections, 1);
  CHECK_EQ (internal.arena.wasted (), 0u);
  internal.check_invariants ();
}

int main () {
  test_schedule ();
  test_triggers ();
  for (bool traced : {false, true}) {
    // Default tier-1 limit 2: clauses G, E, I (glue 5, 4, 4 by size) and
    // cubes U4, U5 (equal glue and size, so in creation order).
    test_reduce (traced, 2,
                 {&Database::G, &Database::E, &Database::I, &Database::U4,
                  &Database::U5},
                 3, 2);
    // No protected tier: also C, the first of the three clauses of glue 3
    // and size 3.
    test_reduce (traced, 0,
                 {&Database::G, &Database::E, &Database::I, &Database::C,
                  &Database::U4, &Database::U5},
                 4, 2);
    test_collection_after_reduce (traced);
    test_tiers (traced);
  }
  test_no_tiers_ignores_marks ();
  test_target ();
  test_everything_protected ();
  return test_result ();
}
