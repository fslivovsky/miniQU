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
// every unassigned decision variable is in the heap of its block.

#include "internal.hpp"

#include <algorithm>
#include <vector>

namespace miniqu {

#define CHECK_INVARIANT(COND, ...) \
  do { \
    if (!(COND)) \
      fatal ("invariant violated: " __VA_ARGS__); \
  } while (0)

// The blocker of a watch is another literal of the constraint, though not
// necessarily the other watched one: propagation replaces watched literals
// without updating the blocker of the watch that stays.
static bool watched (const Watches &watches, const Constraint &c, Ref ref,
                     unsigned i) {
  const Kind kind = c.kind ();
  const std::vector<Watch> &list = watches (kind, watch_key (kind, c[i]));
  return std::any_of (list.begin (), list.end (), [&] (const Watch &w) {
    return w.ref == ref && w.blocker != c[i] &&
           std::find (c.begin (), c.end (), w.blocker) != c.end ();
  });
}

void Internal::check_invariants () const {
  const Var vars = prefix.size ();
  std::vector<uint8_t> seen (2 * (size_t) vars, 0);
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (const auto *lists : {&irredundant, &redundant})
      for (Ref ref : (*lists)[index (kind)]) {
        const Constraint &c = deref (arena, ref);
        if (c.garbage ())
          continue;
        CHECK_INVARIANT (c.kind () == kind, "constraint in a wrong list");
        Var rightmost = 0;
        for (Lit l : c) {
          CHECK_INVARIANT (var (l) < vars, "unknown variable");
          CHECK_INVARIANT (!seen[index (l)], "duplicate literal");
          CHECK_INVARIANT (opts.mode == 2 || !seen[index (~l)],
                           "complementary literals");
          seen[index (l)] = 1;
          rightmost = std::max (rightmost, var (l));
        }
        for (Lit l : c)
          seen[index (l)] = 0;
        CHECK_INVARIANT (prefix.is_primary (kind, rightmost),
                         "constraint %lu not reduced",
                         (unsigned long) c.id ());
        if (c.size () < 2)
          continue;
        CHECK_INVARIANT (
            watched (watches, c, ref, 0) && watched (watches, c, ref, 1),
            "constraint %lu not watched", (unsigned long) c.id ());
        CHECK_INVARIANT (
            propagated < trail.size () ||
                (kval (kind, c[0]) >= 0 && kval (kind, c[1]) >= 0) ||
                std::any_of (c.begin (), c.end (),
                             [&] (Lit l) { return kval (kind, l) > 0; }),
            "constraint %lu watched by a vanished literal",
            (unsigned long) c.id ());
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
        CHECK_INVARIANT (heaps[prefix.depth (v)].contains (v),
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
      CHECK_INVARIANT (!c.garbage (), "reason of %u deleted", v + 1);
      const Lit t = val (l) > 0 ? l : ~l;
      const Lit forced = watch_key (c.kind (), ~t);
      CHECK_INVARIANT (std::find (c.begin (), c.end (), forced) != c.end (),
                       "reason of %u does not contain it", v + 1);
      for (Lit other : c)
        CHECK_INVARIANT (other == forced || kval (c.kind (), other) < 0,
                         "reason of %u is not unit", v + 1);
    }
  }
  CHECK_INVARIANT (assigned == trail.size (), "trail and values differ");
  for (size_t b = 0; b < prefix.blocks.size (); b++)
    CHECK_INVARIANT (prefix.blocks[b].unassigned == unassigned[b],
                     "unassigned count of block %zu", b);
}

} // namespace miniqu
