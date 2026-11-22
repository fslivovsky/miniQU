// Long-distance propagation for mode 2 (ARCHITECTURE 4.7, 6.3, 7.2; the
// old 'propagateLDQ').
//
// The unit rule is prefix-aware: a constraint without a disabling literal
// is unit when exactly one primary literal has not vanished and every
// unassigned secondary literal is to its right (a secondary literal to its
// left could still be assigned so that the primary one is not forced).  It
// is a conflict when no primary literal is left.  No conflict is completed
// as in mode 0: the analysis takes unassigned secondary literals as they
// are.
//
// Watches.  A constraint is watched by a primary literal and by either
// another primary literal or a secondary literal to the left of the
// primary one; as long as both are non-vanished, the constraint is neither
// unit nor a conflict.  Originals start with their two leftmost literals
// watched (the order of 'add_original', as in the old solver), which may
// both be secondary, or a primary one with a secondary one right of it.
// Until one of them vanishes this can miss a conflict or a unit, which
// weakens propagation but nothing else: every secondary literal of an
// original is an input variable and is assigned before the search ends,
// and from the first time a watch moves the watches are as above.  Learnt
// constraints come from 'analyze_ldq' with the asserting literal at
// position 0 and the literal of the backjump level at position 1.  When a
// watched literal vanishes:
//
//   - a disabling blocker, a disabling position 0 or a disabling literal
//     anywhere else leaves the watches alone;
//   - if position 0 is primary, position 1 is replaced by a non-vanished
//     literal that is primary or left of position 0;
//   - if position 0 is secondary, it is first replaced by a non-vanished
//     primary literal, which gets a new watch, and then position 1 as in
//     the previous case.  The old position 0 keeps its watch entry,
//     although it is no longer watched: a *stale* entry;
//   - if nothing is found, position 0 is propagated if it is primary and
//     not vanished, and the constraint is a conflict otherwise.
//
// Because watches of position 0 move too, a watch list may hold stale
// entries (the constraint no longer has that literal at position 0 or 1).
// They are dropped when they are met.  A stale entry may refer to a
// deleted constraint in a list that was never smudged, which the garbage
// collector and 'check_invariants' accept in mode 2.  A stale entry becomes
// a regular one again when its literal returns to position 0 or 1; the old
// code then pushed a second entry (it compared the new position-1 literal
// after overwriting it), which is not ported: entries in a list are
// distinct here.
//
// Not a database transformation; no proof steps (mode 2 has no proofs).

#include "internal.hpp"

#include <algorithm>
#include <cassert>
#include <utility>

namespace miniqu {

template <Kind K> Ref Internal::propagate_ldq_watches (Lit p) {
  const Lit lost = watch_key (K, p);
  std::vector<Watch> &list = watches.lookup (K, p, arena);
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
    if (c[1] != lost)
      continue;
    // Deleting smudged the lists of positions 0 and 1, and a deleted
    // constraint is never reordered, so only a stale entry can reach one.
    assert (!c.garbage ());
    Lit first = c[0];
    const Watch kept{w.ref, first};
    if (first != w.blocker && kval (K, first) > 0) {
      *j++ = kept;
      continue;
    }
    const uint32_t size = c.size ();
    bool disabled = false;
    for (uint32_t k = 2; !disabled && k < size; k++)
      disabled = kval (K, c[k]) > 0;
    if (disabled) {
      *j++ = kept;
      continue;
    }

    // Position 1 is replaced by a literal that can keep position 0 from
    // being unit: a non-vanished primary literal, or a non-vanished
    // secondary one to its left.
    const auto replace_second = [&] () {
      const Var pivot = var (c[0]);
      for (uint32_t k = 2; k < size; k++) {
        const Lit l = c[k];
        if (kval (K, l) < 0 ||
            (!prefix.is_primary (K, var (l)) && var (l) > pivot))
          continue;
        c[1] = l;
        c[k] = lost;
        // If the old position 0 comes back as position 1, its entry is
        // valid again and is not duplicated.
        if (l != first)
          watches (K, watch_key (K, l)).push_back (kept);
        return true;
      }
      return false;
    };

    if (prefix.is_primary (K, var (first))) {
      if (replace_second ())
        continue;
    } else {
      uint32_t k = 2;
      while (k < size &&
             (kval (K, c[k]) < 0 || !prefix.is_primary (K, var (c[k]))))
        k++;
      if (k < size) {
        c[0] = c[k];
        c[k] = first;
        watches (K, watch_key (K, c[0])).push_back (kept);
        if (replace_second ())
          continue;
        first = c[0];
      }
    }

    *j++ = kept;
    if (kval (K, first) < 0 || !prefix.is_primary (K, var (first))) {
      conflict = w.ref;
      LOG (conflict, "conflict");
      j = std::copy (i, end, j);
      break;
    }
    assign (forced (K, first), w.ref);
  }
  list.erase (j, end);
  return conflict;
}

// The trail driver of mode 2, the same shape as 'propagate_trail'
// (propagate.hpp): clauses first for every literal, 'propagated' stays at
// the literal whose propagation found a conflict.
Ref Internal::propagate_ldq () {
  Ref conflict = Ref::none;
  while (conflict == Ref::none && propagated < trail.size ()) {
    const Lit p = trail[propagated];
    stats.propagations++;
    conflict = propagate_ldq_watches<Kind::Clause> (p);
    if (conflict == Ref::none)
      conflict = propagate_ldq_watches<Kind::Cube> (p);
    if (conflict == Ref::none)
      propagated++;
  }
  return conflict;
}

} // namespace miniqu
