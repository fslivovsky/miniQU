#ifndef MINIQU_PROPAGATE_HPP_INCLUDED
#define MINIQU_PROPAGATE_HPP_INCLUDED

#include "internal.hpp"

#include <algorithm>
#include <cassert>
#include <utility>

namespace miniqu {

// The one MiniSat watch loop (ARCHITECTURE 6.2, 7.2), written once for both
// kinds through the kind value.  'p' has just become true; the list visited
// holds the constraints of kind K whose watched literal 'lost' vanished
// with it.  For each watch:
//
//   - if the blocker disables the constraint, it is not loaded;
//   - otherwise 'lost' is moved to position 1, and position 0 is tested in
//     the same way (it becomes the blocker of the kept watch);
//   - otherwise positions 2.. are searched for a literal that has not
//     vanished, which then becomes the watched literal at position 1;
//   - otherwise position 0 is the only literal left: if it vanished too the
//     constraint is a conflict, if it is primary it is propagated (kind
//     value positive, with the constraint as reason), and if it is
//     secondary the rule R decides.  Under 'Lone::Conflict' (mode 0) it is
//     a conflict, and the literal is remembered in 'lone' so that the
//     driver completes the conflict.
//
// After a conflict the remaining watches are kept as they are.  Assigning
// a literal does not allocate, so the reference into the arena stays valid
// throughout.  Returns the conflict or 'Ref::none'.
template <Kind K, Lone R> Ref Internal::propagate_watches (Lit p) {
  const Lit lost = watch_key (K, p);
  WatchList &list = watches.lookup (K, p, arena);
  stats.ticks++;
  Ref conflict = Ref::none;
  auto i = list.begin (), j = i;
  const auto end = list.end ();
  while (i != end) {
    const Watch w = *i++;
    if (kval (K, w.blocker) > 0) {
      *j++ = w;
      continue;
    }
    stats.ticks++;
    Constraint &c = deref (arena, w.ref);
    if (c[0] == lost)
      std::swap (c[0], c[1]);
    assert (c[1] == lost);
    const Lit first = c[0];
    const Watch kept{w.ref, first};
    if (first != w.blocker && kval (K, first) > 0) {
      *j++ = kept;
      continue;
    }
    const uint32_t size = c.size ();
    uint32_t k = 2;
    while (k < size && kval (K, c[k]) < 0)
      k++;
    if (k < size) {
      c[1] = c[k];
      c[k] = lost;
      watches (K, watch_key (K, c[1])).push (kept);
      continue;
    }
    *j++ = kept;
    if (kval (K, first) < 0)
      conflict = w.ref;
    else if (R == Lone::Propagate || prefix.is_primary (K, var (first)))
      assign (K == Kind::Clause ? first : ~first, w.ref);
    else if (R == Lone::Conflict) {
      lone = first;
      conflict = w.ref;
    }
    if (conflict != Ref::none) {
      LOG (conflict, "conflict");
      j = std::copy (i, end, j);
      break;
    }
  }
  list.truncate (j);
  return conflict;
}

// Propagates the trail in both kinds, clauses first for every literal,
// until it is exhausted or a conflict is found.  'propagated' counts only
// literals for which both loops ran to the end, so on a conflict it stays
// at the literal that caused it.
//
// Never inlined: this loop, with the two watch loops inside it, is where
// the solver spends half its time, and it is compiled best as a function of
// its own.  With link-time optimisation the compiler otherwise decides by
// the size of 'search ()' whether the loop ends up inside that function.
// GCC 13.3 kept it separate until one more branch was added to
// 'search ()'; then propagation ran 30% slower on identical searches.  GCC
// 11.5 had it inside 'search ()' all along (STATUS.md, 2026-11-27).
template <Lone R> [[gnu::noinline]] Ref Internal::propagate_trail () {
  Ref conflict = Ref::none;
  while (conflict == Ref::none && propagated < trail.size ()) {
    const Lit p = trail[propagated];
    stats.propagations++;
    conflict = propagate_watches<Kind::Clause, R> (p);
    if (conflict == Ref::none)
      conflict = propagate_watches<Kind::Cube, R> (p);
    if (conflict == Ref::none)
      propagated++;
  }
  return conflict;
}

} // namespace miniqu

#endif
