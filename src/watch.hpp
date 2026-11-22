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
  struct PerKind {
    std::vector<std::vector<Watch>> lists;
    std::vector<uint8_t> dirty;  // per literal
    std::vector<Lit> dirty_lits; // literals whose flag is set, once each
  };
  std::array<PerKind, 2> kinds;

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
    for (PerKind &k : kinds) {
      k.lists.assign (2 * (size_t) vars, {});
      k.dirty.assign (2 * (size_t) vars, 0);
      k.dirty_lits.clear ();
    }
  }

  // Adds empty lists for new variables, keeping the existing ones; the
  // solver creates variables one at a time.
  void resize (Var vars) {
    for (PerKind &k : kinds) {
      k.lists.resize (2 * (size_t) vars);
      k.dirty.resize (2 * (size_t) vars, 0);
    }
  }

  // Raw access; may contain garbage entries.
  std::vector<Watch> &operator() (Kind kind, Lit p) {
    return kinds[index (kind)].lists[index (p)];
  }
  const std::vector<Watch> &operator() (Kind kind, Lit p) const {
    return kinds[index (kind)].lists[index (p)];
  }

  bool dirty (Kind kind, Lit p) const {
    return kinds[index (kind)].dirty[index (p)];
  }

  void smudge (Kind kind, Lit p) {
    PerKind &k = kinds[index (kind)];
    if (k.dirty[index (p)])
      return;
    k.dirty[index (p)] = 1;
    k.dirty_lits.push_back (p);
  }

  void clean (Kind kind, Lit p, const Arena &arena) {
    PerKind &k = kinds[index (kind)];
    if (!k.dirty[index (p)])
      return;
    remove_garbage (k.lists[index (p)], arena);
    k.dirty[index (p)] = 0;
  }

  // The list propagation reads: clean of garbage.
  std::vector<Watch> &lookup (Kind kind, Lit p, const Arena &arena) {
    clean (kind, p, arena);
    return kinds[index (kind)].lists[index (p)];
  }

  void clean_all (const Arena &arena) {
    for (Kind kind : {Kind::Clause, Kind::Cube}) {
      PerKind &k = kinds[index (kind)];
      for (Lit p : k.dirty_lits)
        clean (kind, p, arena);
      k.dirty_lits.clear ();
    }
  }

  // Removes garbage from every list, dirty or not.  Mode 2 needs it before
  // garbage collection: its stale entries (propagate_ldq.cpp) may refer to
  // a deleted constraint from a list that deleting did not smudge.
  void clean_every_list (const Arena &arena) {
    for (PerKind &k : kinds) {
      for (std::vector<Watch> &list : k.lists)
        remove_garbage (list, arena);
      std::fill (k.dirty.begin (), k.dirty.end (), 0);
      k.dirty_lits.clear ();
    }
  }

  // Drops all watches, to reconnect after a pass that rewrites many
  // constraints (ARCHITECTURE 10.2).
  void clear_all () {
    for (PerKind &k : kinds) {
      for (std::vector<Watch> &list : k.lists)
        list.clear ();
      std::fill (k.dirty.begin (), k.dirty.end (), 0);
      k.dirty_lits.clear ();
    }
  }
};

} // namespace miniqu

#endif
