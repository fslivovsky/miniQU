// Backtracking (ARCHITECTURE 7.2, 7.3): unassigns every literal above the
// new level, the reverse of 'assign'.
//
// Phase saving follows the old 'cancelUntil': with 'phasesaving=2' every
// unassigned variable keeps its value as saved phase, with 1 only the
// variables implied on the highest level undone (its decision excluded,
// as in MiniSat), with 0 none.  Decision variables go back into the heap
// of their block; without dependency learning a variable must be in its
// heap whenever it is unassigned, since decisions pop from the heap of the
// current block only.

#include "internal.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

void Internal::backtrack (int new_level) {
  assert (new_level >= 0);
  if (new_level >= decision_level ())
    return;
  LOG ("backtrack to level %d", new_level);
  const size_t start = control[static_cast<size_t> (new_level)];
  const size_t last_decision = control.back ();
  for (size_t i = trail.size (); i-- > start;) {
    const Lit l = trail[i];
    const Var v = var (l);
    if (opts.phasesaving > 1 ||
        (opts.phasesaving == 1 && i > last_decision))
      phases[v] = sign (l) ? -1 : 1;
    vals[index (l)] = vals[index (~l)] = 0;
    if (prefix.vars[v].decision) {
      prefix.block (v).unassigned++;
      Heap &heap = heaps[prefix.depth (v)];
      if (!heap.contains (v))
        heap.push (v);
    }
  }
  trail.resize (start);
  control.resize (static_cast<size_t> (new_level));
  propagated = std::min (propagated, start);
}

} // namespace miniqu
