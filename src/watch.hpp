#ifndef MINIQU_WATCH_HPP_INCLUDED
#define MINIQU_WATCH_HPP_INCLUDED

#include "arena.hpp"
#include "constraint.hpp"
#include "lit.hpp"
#include "message.hpp"

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <type_traits>
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
static_assert (std::is_trivially_copyable_v<Watch>);

// MiniSat's 'vec' for watches: 16 bytes instead of the 24 of a
// 'std::vector', because the list headers are read once per propagated
// literal (ARCHITECTURE 6.1).  Grows by about 3/2 with 'realloc', which a
// trivially copyable element allows.  Only suffixes are erased in bulk:
// every caller compacts a list in place and then truncates it.
class WatchList {
  Watch *data = nullptr;
  uint32_t size_ = 0, capacity_ = 0;

  void grow () {
    const uint64_t capacity = capacity_ + (uint64_t) capacity_ / 2 + 2;
    if (capacity > UINT32_MAX)
      fatal ("out of memory: watch list exceeds 2^32 watches");
    void *p = std::realloc (data, sizeof (Watch) * (size_t) capacity);
    if (!p)
      fatal ("out of memory: watch list of %lu watches",
             (unsigned long) capacity);
    data = static_cast<Watch *> (p);
    capacity_ = static_cast<uint32_t> (capacity);
  }

public:
  WatchList () = default;
  WatchList (const WatchList &) = delete;
  WatchList &operator= (const WatchList &) = delete;
  // Moves leave the source empty; 'std::vector' relocates with them.
  WatchList (WatchList &&other) noexcept
      : data (other.data), size_ (other.size_),
        capacity_ (other.capacity_) {
    other.data = nullptr;
    other.size_ = other.capacity_ = 0;
  }
  WatchList &operator= (WatchList &&other) noexcept {
    if (this != &other) {
      std::free (data);
      data = other.data, size_ = other.size_, capacity_ = other.capacity_;
      other.data = nullptr;
      other.size_ = other.capacity_ = 0;
    }
    return *this;
  }
  ~WatchList () { std::free (data); }

  Watch *begin () { return data; }
  Watch *end () { return data + size_; }
  const Watch *begin () const { return data; }
  const Watch *end () const { return data + size_; }
  size_t size () const { return size_; }
  bool empty () const { return !size_; }
  size_t capacity () const { return capacity_; }

  void push (Watch w) {
    if (size_ == capacity_)
      grow ();
    data[size_++] = w;
  }

  // Truncates to 'first'; '[first, last)' must be the suffix.
  void erase (Watch *first, [[maybe_unused]] Watch *last) {
    assert (begin () <= first && first <= end ());
    assert (last == end ());
    size_ = static_cast<uint32_t> (first - data);
  }

  // Removes one watch, keeping the order of the others.
  void erase (Watch *it) {
    assert (begin () <= it && it < end ());
    std::copy (it + 1, end (), it);
    size_--;
  }

  // Keeps the memory.
  void clear () { size_ = 0; }
};
static_assert (sizeof (WatchList) == 16);

// One list of watches per literal and kind.  The list at '(kind, p)' is
// the one visited when 'p' becomes true.  Clause and cube lists are
// separate so that each propagation loop is specialised for its kind.
//
// Deleting a constraint does not search the lists it is watched in; it only
// 'smudge's them.  A dirty list is cleaned of garbage constraints before
// propagation reads it ('lookup'), or all at once before garbage collection
// ('clean_all').  Garbage keeps its memory until collection, so a stale
// watch can still be dereferenced.
class Watches {
  // Both lists of a literal take 16+16 bytes, so the four list headers of
  // a variable share one cache line, half the 64 bytes per literal of the
  // round-2 record (ARCHITECTURE 6.1).
  struct alignas (32) PerLit {
    std::array<WatchList, 2> lists; // by kind
  };
  static_assert (sizeof (PerLit) == 32);
  std::vector<PerLit> lits;

  // The dirty flags by literal and kind, apart from the lists: 'lookup'
  // reads one per propagated literal and kind, and two bytes per literal
  // put 32 literals on a cache line instead of widening the record.
  std::vector<std::array<uint8_t, 2>> dirty_flags;
  std::array<std::vector<Lit>, 2> dirty_lits; // flag set, once each

  static void remove_garbage (WatchList &list, const Arena &arena) {
    list.erase (std::remove_if (list.begin (), list.end (),
                                [&arena] (const Watch &w) {
                                  return deref (arena, w.ref).garbage ();
                                }),
                list.end ());
  }

  void clear_dirty_flags () {
    std::fill (dirty_flags.begin (), dirty_flags.end (),
               std::array<uint8_t, 2>{});
    for (auto &d : dirty_lits)
      d.clear ();
  }

public:
  // Adds empty, clean lists for new variables, keeping the existing ones.
  void resize (Var vars) {
    lits.resize (2 * (size_t) vars);
    dirty_flags.resize (2 * (size_t) vars, std::array<uint8_t, 2>{});
  }
  Var size () const { return static_cast<Var> (lits.size () / 2); }

  // Raw access; may contain garbage entries.
  WatchList &operator() (Kind kind, Lit p) {
    return lits[index (p)].lists[index (kind)];
  }
  const WatchList &operator() (Kind kind, Lit p) const {
    return lits[index (p)].lists[index (kind)];
  }

  bool dirty (Kind kind, Lit p) const {
    return dirty_flags[index (p)][index (kind)];
  }

  void smudge (Kind kind, Lit p) {
    uint8_t &d = dirty_flags[index (p)][index (kind)];
    if (d)
      return;
    d = 1;
    dirty_lits[index (kind)].push_back (p);
  }

  void clean (Kind kind, Lit p, const Arena &arena) {
    uint8_t &d = dirty_flags[index (p)][index (kind)];
    if (!d)
      return;
    remove_garbage (lits[index (p)].lists[index (kind)], arena);
    d = 0;
  }

  // The list propagation reads: clean of garbage.
  WatchList &lookup (Kind kind, Lit p, const Arena &arena) {
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
    for (PerLit &l : lits)
      for (WatchList &list : l.lists)
        remove_garbage (list, arena);
    clear_dirty_flags ();
  }

  // Drops all watches, to reconnect after a pass that rewrites many
  // constraints (ARCHITECTURE 10.2).
  void clear_all () {
    for (PerLit &l : lits)
      for (WatchList &list : l.lists)
        list.clear ();
    clear_dirty_flags ();
  }
};

} // namespace miniqu

#endif
