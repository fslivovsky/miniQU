// Garbage collection (collect.cpp): when it is due, what it keeps, and the
// order of the copy.

#include "database.hpp"
#include "test.hpp"

#include <map>
#include <set>
#include <tuple>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// Everything observable about the live constraints, independent of where
// they are: id -> (kind, redundant, glue, literals).
using Contents =
    std::map<uint64_t, std::tuple<Kind, bool, uint32_t, std::vector<Lit>>>;

static Contents contents (const Internal &internal) {
  Contents result;
  for (Kind kind : {Clause, Cube})
    for (const auto *lists : {&internal.irredundant, &internal.redundant})
      for (Ref ref : (*lists)[index (kind)]) {
        const Constraint &c = deref (internal.arena, ref);
        CHECK (!c.garbage () && !c.moved ());
        result[c.id ()] = {c.kind (), c.redundant (), c.glue (),
                           std::vector<Lit> (c.begin (), c.end ())};
      }
  return result;
}

// The whole reference structure, to compare two collections.
static std::vector<uint32_t> layout (const Internal &internal) {
  std::vector<uint32_t> result;
  for (Kind kind : {Clause, Cube}) {
    for (Var v = 0; v < internal.prefix.size (); v++)
      for (bool negative : {false, true})
        for (const Watch &w : internal.watches (kind, mk_lit (v, negative)))
          result.push_back (static_cast<uint32_t> (w.ref));
    for (const auto *lists : {&internal.irredundant, &internal.redundant})
      for (Ref ref : (*lists)[index (kind)])
        result.push_back (static_cast<uint32_t> (ref));
  }
  for (Lit l : internal.trail)
    result.push_back (static_cast<uint32_t> (internal.reason (var (l))));
  return result;
}

// The first time a watch list names a constraint it is the one right
// after the previous new constraint, starting at 0 (ARCHITECTURE 5.3 step
// 2).  Applies to every list, since each constraint is first met in the
// walk of the variable order.
static void check_watch_order (const Internal &internal) {
  std::set<Ref> met;
  uint32_t next = 0;
  for (Var v = 0; v < internal.prefix.size (); v++)
    for (bool negative : {false, true})
      for (Kind kind : {Clause, Cube})
        for (const Watch &w : internal.watches (kind, mk_lit (v, negative)))
          if (met.insert (w.ref).second) {
            CHECK_EQ (static_cast<uint32_t> (w.ref), next);
            next += deref (internal.arena, w.ref).words ();
          }
  // Every constraint of this database is watched, so only the model buffer
  // follows.
  CHECK_EQ (next, internal.arena.size () -
                      Constraint::words (internal.prefix.size ()));
}

static void test_due () {
  Internal internal;
  declare (internal, "ee");
  add (internal, Clause, {1, 2});
  internal.init_model_cube ();
  internal.opts.gcfrac = 0;
  CHECK_EQ (internal.arena.wasted (), 0u);
  CHECK (internal.collecting ());
  internal.opts.gcfrac = 20;
  CHECK (!internal.collecting ());
  internal.opts.gcfrac = 100;
  internal.arena.free (internal.arena.size ());
  CHECK (!internal.collecting ());
  internal.opts.gcfrac = 99;
  CHECK (internal.collecting ());
}

static void test_collect_nothing_wasted () {
  Database db;
  Internal &internal = db.internal;
  internal.opts.gcfrac = 0;
  db.propagate_reasons ();
  const Contents before = contents (internal);
  const uint32_t size = internal.arena.size ();
  const uint64_t cube_id =
      deref (internal.arena, internal.model_cube).id ();
  CHECK (internal.collecting ());
  internal.garbage_collect ();
  CHECK_EQ (internal.stats.collections, 1);
  CHECK_EQ (internal.stats.relocated, (int64_t) before.size ());
  CHECK_EQ (internal.arena.size (), size);
  CHECK (contents (internal) == before);
  CHECK_EQ (deref (internal.arena, internal.model_cube).id (), cube_id);
  internal.check_invariants ();
}

static void test_collect_deleted () {
  Database db;
  Internal &internal = db.internal;
  db.propagate_reasons ();
  // Delete constraints that are watched and one of each list, then collect.
  for (Ref ref : {db.A, db.G, db.U1, db.U5})
    internal.mark_garbage (ref);
  for (Kind kind : {Clause, Cube}) {
    auto &list = internal.redundant[index (kind)];
    std::erase_if (
        list, [&] (Ref r) { return deref (internal.arena, r).garbage (); });
  }
  const Contents before = contents (internal);
  const uint32_t live = internal.arena.size () - internal.arena.wasted ();
  const uint64_t id_r = db.id (db.R), id_q = db.id (db.Q);
  internal.garbage_collect ();
  CHECK_EQ (internal.arena.size (), live);
  CHECK_EQ (internal.arena.wasted (), 0u);
  CHECK (contents (internal) == before);
  CHECK_EQ (internal.stats.relocated, (int64_t) before.size ());
  // The reasons are the copies of the same constraints.
  CHECK_EQ (db.id (internal.reason (4)), id_r);
  CHECK_EQ (db.id (internal.reason (3)), id_q);
  check_watch_order (internal);
  internal.check_invariants ();

  // A second collection changes nothing, not even the addresses.
  const std::vector<uint32_t> first = layout (internal);
  internal.garbage_collect ();
  CHECK (layout (internal) == first);
  CHECK (contents (internal) == before);
  internal.check_invariants ();
}

// Units are in no watch list and are only reached through the lists.
static void test_units () {
  Internal internal;
  declare (internal, "eee");
  add (internal, Clause, {1});
  add (internal, Clause, {2, 3});
  add (internal, Clause, {-2, 3});
  internal.init_model_cube ();
  const Contents before = contents (internal);
  const Ref unit = internal.reason (0);
  CHECK (unit != Ref::none);
  internal.garbage_collect ();
  CHECK (contents (internal) == before);
  CHECK (internal.reason (0) != Ref::none);
  CHECK_EQ (deref (internal.arena, internal.reason (0)).size (), 1u);
  CHECK_EQ (internal.irredundant[0].size (), 3u);
  internal.check_invariants ();
}

int main () {
  test_due ();
  test_collect_nothing_wasted ();
  test_collect_deleted ();
  test_units ();
  return test_result ();
}
