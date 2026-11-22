#ifndef MINIQU_CONSTRAINT_HPP_INCLUDED
#define MINIQU_CONSTRAINT_HPP_INCLUDED

#include "arena.hpp"
#include "lit.hpp"

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <span>

namespace miniqu {

// Layout of a clause or cube in the arena (ARCHITECTURE 5.2), sixteen bytes
// of header followed by the literals:
//
//   word 0     size
//   word 1     bit field: kind, redundant, garbage, moved, reason,
//              7 reserved bits, 20-bit saturating glue
//   word 2, 3  64-bit proof id, low word first
//   word 4..   literals
//
// 'Constraint' is only ever a view onto arena words and is reached through
// 'deref'.  This file is the one place that knows the layout (and the only
// one that does word arithmetic), so that a 12-byte header, should the
// measurement of ROADMAP M1.3 ask for one, changes nothing else.

class Constraint {
  uint32_t size_;
  uint32_t bits;
  uint32_t id_low;
  uint32_t id_high;

  // The arena has no member of this type: the literals follow the header
  // in the arena's words, which is what the flexible array member models.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
  Lit lits_[];
#pragma GCC diagnostic pop

  static constexpr uint32_t kind_bit = 1u << 0;
  static constexpr uint32_t redundant_bit = 1u << 1;
  static constexpr uint32_t garbage_bit = 1u << 2;
  static constexpr uint32_t moved_bit = 1u << 3;
  static constexpr uint32_t reason_bit = 1u << 4;
  static constexpr unsigned glue_shift = 12;
  static constexpr uint32_t glue_max = (1u << 20) - 1;

  bool test (uint32_t bit) const { return bits & bit; }
  void set (uint32_t bit, bool value) {
    bits = value ? (bits | bit) : (bits & ~bit);
  }

  friend Ref alloc_constraint (Arena &, std::span<const Lit>, Kind, bool,
                               uint64_t);
  friend Constraint &deref (Arena &, Ref);
  friend const Constraint &deref (const Arena &, Ref);

public:
  Constraint () = delete;
  Constraint (const Constraint &) = delete;
  Constraint &operator= (const Constraint &) = delete;

  static constexpr uint32_t header_words = 4;

  // Number of arena words of a constraint with that many literals.  A
  // constraint has at least one literal, which also holds the forwarding
  // reference during garbage collection.
  static constexpr uint32_t words (uint32_t size) {
    return header_words + size;
  }
  uint32_t words () const { return words (size_); }

  uint32_t size () const { return size_; }
  std::span<Lit> lits () { return {lits_, size_}; }
  std::span<const Lit> lits () const { return {lits_, size_}; }
  Lit *begin () { return lits_; }
  Lit *end () { return lits_ + size_; }
  const Lit *begin () const { return lits_; }
  const Lit *end () const { return lits_ + size_; }
  Lit &operator[] (uint32_t i) { return lits_[i]; }
  const Lit &operator[] (uint32_t i) const { return lits_[i]; }

  // Lowers the size in place and returns the number of words that became
  // waste, which the caller reports to the arena.
  uint32_t shrink (uint32_t new_size) {
    assert (new_size >= 1 && new_size <= size_);
    const uint32_t freed = size_ - new_size;
    size_ = new_size;
    return freed;
  }

  // Only for the buffer of 'model.cpp', which is allocated with the
  // largest size it can need and never watched or stored in a list: its
  // literals are rewritten in place, and the size can grow back up to the
  // allocated one, or be zero (the empty cube).
  void set_size (uint32_t n) { size_ = n; }

  Kind kind () const { return test (kind_bit) ? Kind::Cube : Kind::Clause; }
  bool redundant () const { return test (redundant_bit); }
  bool garbage () const { return test (garbage_bit); }
  bool moved () const { return test (moved_bit); }
  bool reason () const { return test (reason_bit); }
  void set_redundant (bool v) { set (redundant_bit, v); }
  void set_garbage (bool v) { set (garbage_bit, v); }
  void set_reason (bool v) { set (reason_bit, v); }

  uint32_t glue () const { return bits >> glue_shift; }
  void set_glue (uint32_t g) {
    bits = (bits & ((1u << glue_shift) - 1)) |
           (std::min (g, glue_max) << glue_shift);
  }

  uint64_t id () const { return (uint64_t) id_high << 32 | id_low; }

  // Relocation: the copy lives at 'to'; the old constraint keeps its memory
  // but is marked moved and stores the new reference in its first literal.
  void forward (Ref to) {
    set (moved_bit, true);
    lits_[0].x = static_cast<uint32_t> (to);
  }
  Ref forwarded () const {
    assert (moved ());
    return static_cast<Ref> (lits_[0].x);
  }
};

inline Constraint &deref (Arena &arena, Ref r) {
  return *reinterpret_cast<Constraint *> (arena.words (r));
}

inline const Constraint &deref (const Arena &arena, Ref r) {
  return *reinterpret_cast<const Constraint *> (arena.words (r));
}

// Allocates and fills a constraint; glue starts at zero.
inline Ref alloc_constraint (Arena &arena, std::span<const Lit> lits,
                             Kind kind, bool redundant, uint64_t id) {
  assert (!lits.empty ());
  const uint32_t size = static_cast<uint32_t> (lits.size ());
  const Ref ref = arena.alloc (Constraint::words (size));
  Constraint &c = deref (arena, ref);
  c.size_ = size;
  c.bits = (kind == Kind::Cube ? Constraint::kind_bit : 0u) |
           (redundant ? Constraint::redundant_bit : 0u);
  c.id_low = static_cast<uint32_t> (id);
  c.id_high = static_cast<uint32_t> (id >> 32);
  std::copy (lits.begin (), lits.end (), c.lits_);
  return ref;
}

} // namespace miniqu

#endif
