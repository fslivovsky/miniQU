// Reduction of the learnt databases (reduce.cpp): the triggers, the old
// size schedule, the selection of the constraints to delete, the protection
// of reasons, and the deletion steps.

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
  internal.init_reduce ();
  // Nine learnt clauses and six cubes, one original: the limit is 10 and
  // each assigned variable lowers the count.
  CHECK_EQ (internal.lim.max_learnts, 1.0 / 3);
  internal.lim.max_learnts = 15;
  CHECK (internal.reducing ());
  internal.lim.max_learnts = 16;
  CHECK (!internal.reducing ());
  db.propagate_reasons ();
  internal.lim.max_learnts = 11;
  CHECK (internal.reducing ());
  internal.lim.max_learnts = 12;
  CHECK (!internal.reducing ());

  // '--reduceint' adds a conflict trigger with arithmetic growth.
  internal.opts.reduceint = 2;
  internal.init_reduce ();
  internal.lim.max_learnts = 1e9;
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
  }
  test_everything_protected ();
  return test_result ();
}
