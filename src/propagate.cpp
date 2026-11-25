// Unit propagation during search, modes 0 and 1 (ARCHITECTURE 4.7, 7.2).
//
// The mode selects the instance of the watch loop once per call, never per
// watch.  Mode 0 (Q-resolution) treats a constraint whose single
// non-vanished literal is secondary as a conflict, and completes it after
// the loop: that literal gets its vanishing value, without reason, on the
// current level (porting note 2), so that every literal of the conflict is
// assigned when analysis starts.  Mode 1 (QU-resolution) propagates such a
// literal like a primary one.  Mode 2 has its own loop.
//
// Vivification ('vivify.cpp') propagates one kind only, from a trail head
// of its own ('propagate_kind'), with secondary lone literals ignored in
// mode 0 and propagated in mode 1 (ARCHITECTURE 7.2, ROADMAP V1, V2).
//
// Propagation itself derives nothing, so there are no proof steps here.

#include "propagate.hpp"

namespace miniqu {

// Profiled once per call of the driver, never per watch.
Ref Internal::propagate () {
  PROFILE_SCOPE (propagate);
  switch (opts.mode) {
  case 0: {
    const Ref conflict = propagate_trail<Lone::Conflict> ();
    if (lone != lit_undef) {
      assert (conflict != Ref::none && !val (lone));
      const Kind kind = deref (arena, conflict).kind ();
      assign (kind == Kind::Clause ? ~lone : lone, Ref::none);
      lone = lit_undef;
    }
    return conflict;
  }
  case 1:
    return propagate_trail<Lone::Propagate> ();
  default:
    return propagate_ldq ();
  }
}

// The trail from 'head' through the watch lists of K only.  'propagated',
// 'depend.propagated', 'lone' and 'stats.propagations' stay as they are;
// 'head' stays at the literal that caused a conflict.
template <Kind K, Lone R>
Ref Internal::propagate_kind_trail (size_t &head) {
  Ref conflict = Ref::none;
  while (conflict == Ref::none && head < trail.size ()) {
    stats.vivifyprops++;
    conflict = propagate_watches<K, R> (trail[head]);
    if (conflict == Ref::none)
      head++;
  }
  return conflict;
}

// The instance is selected once per call.  Modes 0 and 1 only.
Ref Internal::propagate_kind (Kind kind, size_t &head) {
  assert (opts.mode != 2);
  if (kind == Kind::Clause)
    return opts.mode
               ? propagate_kind_trail<Kind::Clause, Lone::Propagate> (head)
               : propagate_kind_trail<Kind::Clause, Lone::Ignore> (head);
  return opts.mode
             ? propagate_kind_trail<Kind::Cube, Lone::Propagate> (head)
             : propagate_kind_trail<Kind::Cube, Lone::Ignore> (head);
}

} // namespace miniqu
