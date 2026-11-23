// Internal consistency checks (ARCHITECTURE 4.3, 9.6).  Called by debug
// builds at root level after every pass and by the unit tests; available in
// every build because '--check' asks for them in mode 2 (ARCHITECTURE 8.1).
// A violation is a bug of the solver and ends the run through 'fatal'.
//
// Checked: INV-REDUCED and duplicate/complementary literals of every stored
// constraint, INV-WATCH (every live constraint of size >= 2 is watched by
// its literals 0 and 1, and once propagation is complete a vanished watched
// literal is only left in a disabled constraint), consistency of trail,
// values, levels and reasons, the unassigned counts of the blocks, and that
// every unassigned decision variable is in the heap of its block (with
// '--dl': or waits for its watched dependency, and every watch is in the
// list of the variable it watches).  No
// stored reference, in the lists, the reasons and the watch lists that are
// clean, is to a moved constraint; clean watch lists hold no garbage (the
// state after a garbage collection, ARCHITECTURE 5.3).
//
// Mode 2 (propagate_ldq.cpp, ARCHITECTURE 6.3): watch lists may hold stale
// entries, also of deleted constraints in clean lists, which are accepted;
// a live constraint must still be watched by its literals 0 and 1.  Once
// propagation is complete, a constraint that is not disabled and whose
// watches are as mode 2 keeps them (a primary literal and another primary
// one or a secondary one left of it) is not unit under the long-distance
// rule.  An original keeps its first two literals watched until one of
// them vanishes, which may miss a unit or a conflict (as in the old
// solver), so it is exempt until then.  A reason in mode 2 may contain
// secondary literals that were unassigned and right of the forced one
// when it propagated and were assigned later either way, so only its
// primary literals are checked.

#include "internal.hpp"

#include <algorithm>
#include <unordered_map>
#include <vector>

namespace miniqu {

#define CHECK_INVARIANT(COND, ...) \
  do { \
    if (!(COND)) \
      fatal ("invariant violated: " __VA_ARGS__); \
  } while (0)

// For every live constraint of size >= 2, which of its literals 0 and 1 are
// watched: bit i of the entry is set if the list of literal i holds the
// constraint.  The blocker of a watch is another literal of the
// constraint, though not necessarily the other watched one: propagation
// replaces watched literals without updating the blocker of the watch that
// stays.  One pass over all lists, so that checking after every garbage
// collection of a stress run stays affordable.
static std::unordered_map<Ref, uint8_t>
watched_positions (const Watches &watches, const Arena &arena, Var vars) {
  std::unordered_map<Ref, uint8_t> result;
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (Var v = 0; v < vars; v++)
      for (bool negative : {false, true}) {
        const Lit p = mk_lit (v, negative);
        for (const Watch &w : watches (kind, p)) {
          const Constraint &c = deref (arena, w.ref);
          if (c.garbage ())
            continue;
          for (unsigned i = 0; i < 2; i++)
            if (watch_key (kind, c[i]) == p && w.blocker != c[i] &&
                std::find (c.begin (), c.end (), w.blocker) != c.end ())
              result[w.ref] |= (uint8_t) (1u << i);
        }
      }
  return result;
}

// Watched by a primary literal and by another primary one or a secondary
// one left of it.
static bool long_distance_watched (const Internal &internal, Kind kind,
                                   const Constraint &c) {
  const auto watches = [&] (Lit p, Lit other) {
    return internal.prefix.is_primary (kind, var (p)) &&
           (internal.prefix.is_primary (kind, var (other)) ||
            var (other) < var (p));
  };
  return watches (c[0], c[1]) || watches (c[1], c[0]);
}

// Not disabled, exactly one primary literal not vanished, and every
// unassigned secondary literal right of it.
static bool long_distance_unit (const Internal &internal, Kind kind,
                                const Constraint &c) {
  Var unit = no_var, blocking = no_var;
  for (Lit l : c) {
    if (internal.kval (kind, l) > 0)
      return false;
    if (internal.kval (kind, l) < 0)
      continue;
    if (!internal.prefix.is_primary (kind, var (l)))
      blocking = std::min (blocking, var (l));
    else if (unit != no_var)
      return false;
    else
      unit = var (l);
  }
  return unit != no_var && unit < blocking;
}

void Internal::check_invariants () const {
  const Var vars = prefix.size ();
  std::vector<uint8_t> marked (2 * (size_t) vars, 0);
  const std::unordered_map<Ref, uint8_t> watched =
      watched_positions (watches, arena, vars);
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (const auto *lists : {&irredundant, &redundant})
      for (Ref ref : (*lists)[index (kind)]) {
        const Constraint &c = deref (arena, ref);
        CHECK_INVARIANT (!c.moved (), "list refers to a moved constraint");
        CHECK_INVARIANT (
            c.has_id () == (proof != nullptr),
            "constraint stores an id iff a tracer is connected");
        if (c.garbage ())
          continue;
        CHECK_INVARIANT (c.kind () == kind, "constraint in a wrong list");
        Var rightmost = 0;
        for (Lit l : c) {
          CHECK_INVARIANT (var (l) < vars, "unknown variable");
          CHECK_INVARIANT (!marked[index (l)], "duplicate literal");
          CHECK_INVARIANT (opts.mode == 2 || !marked[index (~l)],
                           "complementary literals");
          marked[index (l)] = 1;
          rightmost = std::max (rightmost, var (l));
        }
        for (Lit l : c)
          marked[index (l)] = 0;
        CHECK_INVARIANT (prefix.is_primary (kind, rightmost),
                         "constraint %lu not reduced",
                         (unsigned long) message_id (c));
        if (c.size () < 2)
          continue;
        CHECK_INVARIANT (watched.contains (ref) && watched.at (ref) == 3,
                         "constraint %lu not watched",
                         (unsigned long) message_id (c));
        CHECK_INVARIANT (
            propagated < trail.size () ||
                (kval (kind, c[0]) >= 0 && kval (kind, c[1]) >= 0) ||
                std::any_of (c.begin (), c.end (),
                             [&] (Lit l) { return kval (kind, l) > 0; }),
            "constraint %lu watched by a vanished literal",
            (unsigned long) message_id (c));
        CHECK_INVARIANT (opts.mode != 2 || propagated < trail.size () ||
                             !long_distance_watched (*this, kind, c) ||
                             !long_distance_unit (*this, kind, c),
                         "constraint %lu unit but not propagated",
                         (unsigned long) message_id (c));
      }

  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (Var v = 0; v < vars; v++)
      for (bool negative : {false, true}) {
        const Lit p = mk_lit (v, negative);
        if (watches.dirty (kind, p))
          continue;
        for (const Watch &w : watches (kind, p)) {
          const Constraint &c = deref (arena, w.ref);
          if (opts.mode == 2 && c.garbage () &&
              watch_key (kind, c[0]) != p && watch_key (kind, c[1]) != p)
            continue;
          CHECK_INVARIANT (!c.garbage () && !c.moved (),
                           "clean watch list of %u holds a deleted or "
                           "moved constraint",
                           v + 1);
        }
      }

  CHECK_INVARIANT (propagated <= trail.size (), "propagated beyond trail");
  CHECK_INVARIANT (control.empty () || control.back () <= trail.size (),
                   "decision level starts beyond trail");
  std::vector<int> unassigned (prefix.blocks.size (), 0);
  size_t assigned = 0;
  for (Var v = 0; v < vars; v++) {
    const Lit l = mk_lit (v);
    CHECK_INVARIANT (val (l) == -val (~l), "values of %u differ", v + 1);
    const bool decision = prefix.vars[v].decision;
    if (!val (l)) {
      if (decision) {
        unassigned[prefix.depth (v)]++;
        CHECK_INVARIANT (heap_of (v).contains (v) ||
                             (opts.dl && waits_for_dependency (v)),
                         "variable %u not in its heap", v + 1);
      }
      continue;
    }
    assigned++;
    const VarData &d = vtab[v];
    CHECK_INVARIANT (d.trail >= 0 && (size_t) d.trail < trail.size () &&
                         var (trail[(size_t) d.trail]) == v &&
                         val (trail[(size_t) d.trail]) > 0,
                     "trail position of %u", v + 1);
    CHECK_INVARIANT (d.level >= 0 && d.level <= decision_level (),
                     "level of %u", v + 1);
    const size_t position = (size_t) d.trail;
    CHECK_INVARIANT (
        (d.level == 0 || control[(size_t) d.level - 1] <= position) &&
            ((size_t) d.level == control.size () ||
             position < control[(size_t) d.level]),
        "variable %u on the trail of another level", v + 1);
    if (d.reason != Ref::none) {
      // The reason forced the true literal 't' to a positive kind value
      // and all its other literals had vanished.
      const Constraint &c = deref (arena, d.reason);
      CHECK_INVARIANT (!c.garbage () && !c.moved (),
                       "reason of %u deleted or moved", v + 1);
      const Lit t = val (l) > 0 ? l : ~l;
      const Lit forced = watch_key (c.kind (), ~t);
      CHECK_INVARIANT (std::find (c.begin (), c.end (), forced) != c.end (),
                       "reason of %u does not contain it", v + 1);
      for (Lit other : c)
        CHECK_INVARIANT (other == forced || kval (c.kind (), other) < 0 ||
                             (opts.mode == 2 &&
                              !prefix.is_primary (c.kind (), var (other))),
                         "reason of %u is not unit", v + 1);
    }
  }
  CHECK_INVARIANT (assigned == trail.size (), "trail and values differ");
  for (size_t b = 0; b < prefix.blocks.size (); b++)
    CHECK_INVARIANT (prefix.blocks[b].unassigned == unassigned[b],
                     "unassigned count of block %zu", b);
  CHECK_INVARIANT (depend.propagated <= trail.size (),
                   "dependency head beyond trail");
  for (Var v = 0; v < depend.on.size (); v++)
    if (!depend.on[v].empty ()) {
      const std::vector<Var> &watching = depend.watching[depend.on[v][0]];
      CHECK_INVARIANT (std::count (watching.begin (), watching.end (), v) ==
                           1,
                       "dependency watch of %u", v + 1);
    }
}

} // namespace miniqu
