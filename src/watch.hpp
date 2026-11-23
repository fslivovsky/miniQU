#ifndef MINIQU_WATCH_HPP_INCLUDED
#define MINIQU_WATCH_HPP_INCLUDED

#include "arena.hpp"
#include "constraint.hpp"
#include "lit.hpp"

#include <algorithm>
#include <array>
#include <cstdint>
#include <vector>

namespace miniqu {

// A watch is eight bytes: the watched constraint and the other watched
// literal as blocker, which is tested before the constraint is loaded
// (ARCHITECTURE 6.1).
struct Watch {
  Ref ref;
  Lit blocker;
};
static_assert (sizeof (Watch) == 8);

// One vector of watches per literal and kind.  The list at '(kind, p)' is
// the one visited when 'p' becomes true.  Clause and cube lists are
// separate so that each propagation loop is specialised for its kind.
//
// Deleting a constraint does not search the lists it is watched in; it only
// 'smudge's them.  A dirty list is cleaned of garbage constraints before
// propagation reads it ('lookup'), or all at once before garbage collection
// ('clean_all').  Garbage keeps its memory until collection, so a stale
// watch can still be dereferenced.
class Watches {
  // Both lists of a literal and their dirty flags share one cache line, so
  // that propagating a literal touches one line of list headers.
  struct alignas (64) PerLit {
    std::array<std::vector<Watch>, 2> lists; // by kind
    std::array<uint8_t, 2> dirty;
  };
  std::vector<PerLit> lits;
  std::array<std::vector<Lit>, 2> dirty_lits; // flag set, once each

  static void remove_garbage (std::vector<Watch> &list,
                              const Arena &arena) {
    list.erase (std::remove_if (list.begin (), list.end (),
                                [&arena] (const Watch &w) {
                                  return deref (arena, w.ref).garbage ();
                                }),
                list.end ());
  }

public:
  void init (Var vars) {
    lits.assign (2 * (size_t) vars, {});
    for (auto &d : dirty_lits)
      d.clear ();
  }

  // Adds empty lists for new variables, keeping the existing ones; the
  // solver creates variables one at a time.
  void resize (Var vars) { lits.resize (2 * (size_t) vars); }

  // Raw access; may contain garbage entries.
  std::vector<Watch> &operator() (Kind kind, Lit p) {
    return lits[index (p)].lists[index (kind)];
  }
  const std::vector<Watch> &operator() (Kind kind, Lit p) const {
    return lits[index (p)].lists[index (kind)];
  }

  bool dirty (Kind kind, Lit p) const {
    return lits[index (p)].dirty[index (kind)];
  }

  void smudge (Kind kind, Lit p) {
    uint8_t &d = lits[index (p)].dirty[index (kind)];
    if (d)
      return;
    d = 1;
    dirty_lits[index (kind)].push_back (p);
  }

  void clean (Kind kind, Lit p, const Arena &arena) {
    PerLit &l = lits[index (p)];
    if (!l.dirty[index (kind)])
      return;
    remove_garbage (l.lists[index (kind)], arena);
    l.dirty[index (kind)] = 0;
  }

  // The list propagation reads: clean of garbage.
  std::vector<Watch> &lookup (Kind kind, Lit p, const Arena &arena) {
    clean (kind, p, arena);
    return lits[index (p)].lists[index (kind)];
  }

  void clean_all (const Arena &arena) {
    for (Kind kind : {Kind::Clause, Kind::Cube}) {
      for (Lit p : dirty_lits[index (kind)])
        clean (kind, p, arena);
      dirty_lits[index (kind)].clear ();
    }
  }

  // Removes garbage from every list, dirty or not.  Mode 2 needs it before
  // garbage collection: its stale entries (propagate_ldq.cpp) may refer to
  // a deleted constraint from a list that deleting did not smudge.
  void clean_every_list (const Arena &arena) {
    for (PerLit &l : lits) {
      for (std::vector<Watch> &list : l.lists)
        remove_garbage (list, arena);
      l.dirty = {};
    }
    for (auto &d : dirty_lits)
      d.clear ();
  }

  // Drops all watches, to reconnect after a pass that rewrites many
  // constraints (ARCHITECTURE 10.2).
  void clear_all () {
    for (PerLit &l : lits) {
      for (std::vector<Watch> &list : l.lists)
        list.clear ();
      l.dirty = {};
    }
    for (auto &d : dirty_lits)
      d.clear ();
  }
};

} // namespace miniqu

#endif
