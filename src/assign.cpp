// Assigning literals (ARCHITECTURE 7.2): the only place, together with
// 'backtrack.cpp', that writes values, levels, reasons and the trail.
//
// 'Block::unassigned' counts the unassigned decision variables of a block,
// so that the current decision block (the first one with a nonzero count)
// is found without scanning.  The old solver maintained it only without
// dependency learning; it is maintained always here, which costs one
// increment and keeps the count meaningful for 'check_invariants'.

#include "internal.hpp"

#include <cassert>

namespace miniqu {

void Internal::assign (Lit l, Ref reason) {
  const Var v = var (l);
  assert (!val (l));
  vals[index (l)] = 1;
  vals[index (~l)] = -1;
  vtab[v] =
      VarData{decision_level (), reason, static_cast<int> (trail.size ())};
  trail.push_back (l);
  if (prefix.vars[v].decision)
    prefix.block (v).unassigned--;
  if (reason == Ref::none)
    LOG ("assign %s%u without reason", sign (l) ? "-" : "", v + 1);
  else
    LOG (reason, "assign %s%u reason", sign (l) ? "-" : "", v + 1);
}

// Root simplification ('simplify.cpp') makes a unit derived for a root
// literal its reason.  A unit has no other literals, so the reasons stay
// consistent with the trail order.
void Internal::replace_reason (Var v, Ref unit) {
  assert (!level (v) && val (mk_lit (v)));
  assert (deref (arena, unit).size () == 1);
  assert (var (deref (arena, unit)[0]) == v);
  vtab[v].reason = unit;
  LOG (unit, "new reason of %u", v + 1);
}

void Internal::new_level () {
  control.push_back (trail.size ());
  LOG ("new decision level");
}

} // namespace miniqu
