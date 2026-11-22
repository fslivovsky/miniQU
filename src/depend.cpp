// Dependency learning (ARCHITECTURE 7.4; the old
// 'updateDependencyWatchers', 'resetDependencies', the dependency branch of
// 'search' and of 'cancelUntil').
//
// With '--dl' decisions need not follow the prefix.  When an analysis has
// to resolve away a decision x to reduce a blocked secondary variable y
// left of it, x was decided too early: it is recorded to depend on y, and
// from then on x is decided only when y is assigned.  Every dependency
// points to a smaller variable (y < x), so the dependencies are acyclic
// and the smallest unassigned decision variable is always eligible.
//
// Only one dependency per variable is watched, the first entry of its
// list: the variable is eligible when that one is assigned.  When a
// watched variable gets assigned, each variable watching it looks for
// another unassigned dependency and moves its watch there, or else goes
// back into the decision heap.  Like the old code this runs lazily, from a
// trail head of its own, before each decision; and it checks only the
// watch, so a variable that became eligible stays so after backtracking
// unassigned one of its other dependencies (it is then decided too early
// again and the analysis reports the dependency anew, possibly as a
// duplicate list entry, as in the old code).
//
// A variable popped from the heap while ineligible is dropped; it comes
// back when its watched dependency is assigned (here) or when the
// backtrack that unassigns it leaves that dependency assigned
// ('backtrack.cpp').  Every 'depreset'-th restart all dependencies are
// forgotten (porting note 9), provided a constraint was learnt since the
// last reset (see 'resetting_dependencies').
//
// Dependencies are heuristic: the analyses are sound for any decision
// order, so nothing here needs a proof step.

#include "internal.hpp"

#include <algorithm>
#include <cassert>
#include <utility>

namespace miniqu {

void Internal::add_dependency_var () {
  depend.on.emplace_back ();
  depend.watching.emplace_back ();
}

// 'x' depends on 'y' and watches it from now on.  Called right before the
// backtrack that unassigns both, as in the old 'search', so that the
// backtrack leaves 'x' out of the heap ('learn_dependency').
void Internal::record_dependency (Var x, Var y) {
  assert (opts.dl && y < x);
  stats.dependencies++;
  LOG ("learnt dependency of %u on %u", x + 1, y + 1);
  std::vector<Var> &on = depend.on[x];
  on.push_back (y);
  std::swap (on.front (), on.back ());
  if (on.size () > 1) {
    std::vector<Var> &old = depend.watching[on.back ()];
    const auto it = std::find (old.begin (), old.end (), x);
    assert (it != old.end ());
    *it = old.back ();
    old.pop_back ();
  }
  depend.watching[y].push_back (x);
}

void Internal::update_dependency_watches () {
  Heap &heap = heaps[0];
  while (depend.propagated < trail.size ()) {
    const Var v = var (trail[depend.propagated++]);
    std::vector<Var> &watching = depend.watching[v];
    size_t j = 0;
    for (const Var w : watching) {
      std::vector<Var> &on = depend.on[w];
      assert (on.front () == v);
      const auto unassigned =
          std::find_if (on.begin () + 1, on.end (),
                        [this] (Var u) { return !val (mk_lit (u)); });
      if (unassigned != on.end ()) {
        std::iter_swap (on.begin (), unassigned);
        depend.watching[on.front ()].push_back (w);
        continue;
      }
      if (!heap.contains (w))
        heap.push (w);
      watching[j++] = w;
    }
    watching.resize (j);
  }
}

// Whether the unassigned 'v' is eligible once the search is back on level
// 'new_level'.
bool Internal::stays_eligible (Var v, int new_level) const {
  const std::vector<Var> &on = depend.on[v];
  return on.empty () ||
         (val (mk_lit (on.front ())) && level (on.front ()) <= new_level);
}

// Why an unassigned decision variable may be missing from the heap: its
// watched dependency is unassigned, or assigned but not yet processed.
bool Internal::waits_for_dependency (Var v) const {
  const std::vector<Var> &on = depend.on[v];
  if (on.empty ())
    return false;
  const Var u = on.front ();
  return !val (mk_lit (u)) || (size_t) vtab[u].trail >= depend.propagated;
}

// The old schedule counts restarts from 1 and resets after the 19th, 39th,
// ... with the old constant 20.  A reset is skipped while no constraint has
// been learnt since the last one: a dependency counts as a conflict for the
// restart schedule, so restarting and resetting after every conflict (the
// stress configuration) would otherwise repeat the same decisions and the
// same dependency forever.
bool Internal::resetting_dependencies () const {
  return opts.dl && (stats.restarts + 1) % opts.depreset == 0 &&
         stats.learned[0] + stats.learned[1] > depend.learned;
}

void Internal::reset_dependencies () {
  stats.depresets++;
  depend.learned = stats.learned[0] + stats.learned[1];
  LOG ("resetting dependencies");
  for (std::vector<Var> &on : depend.on)
    on.clear ();
  for (std::vector<Var> &watching : depend.watching)
    watching.clear ();
  depend.propagated = 0;
  // Root-level assigned variables too, as the old 'resetDependencies'.
  Heap &heap = heaps[0];
  for (Var v = 0; v < prefix.size (); v++)
    if (prefix.vars[v].decision && !heap.contains (v))
      heap.push (v);
}

} // namespace miniqu
