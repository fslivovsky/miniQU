#ifndef MINIQU_CONSTRAINT_HPP_INCLUDED
#define MINIQU_CONSTRAINT_HPP_INCLUDED

#include "arena.hpp"
#include "lit.hpp"
#include "message.hpp"

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <span>

namespace miniqu {

// Layout of a clause or cube in the arena (ARCHITECTURE 5.2), twelve bytes
// of header followed by the literals:
//
//   word 0     bits 0-4: kind, redundant, garbage, moved, reason;
//              bits 5-31: size
//   word 1     proof id, bits 0-31
//   word 2     bits 0-11: proof id, bits 32-43;
//              bits 12-25: saturating glue; bits 26-31 reserved
//   word 3..   literals
//
// 'Constraint' is only ever a view onto arena words and is reached through
// 'deref'.  This file is the one place that knows the layout (and the only
// one that does word arithmetic): the sixteen-byte header with a full
// 32-bit size, a 64-bit id and a 20-bit glue was measured against this one
// (ROADMAP M1.3) and is in the history of this file.

class Constraint {
  uint32_t head; // flags and size
  uint32_t id_low;
  uint32_t id_high_glue;

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
  static constexpr unsigned size_shift = 5;
  static constexpr uint32_t flags_mask = (1u << size_shift) - 1;
  static constexpr unsigned id_high_bits = 12;
  static constexpr uint32_t id_high_mask = (1u << id_high_bits) - 1;
  static constexpr unsigned glue_shift = id_high_bits;
  static constexpr unsigned glue_bits = 14;
  static constexpr uint32_t glue_mask = ((1u << glue_bits) - 1)
                                        << glue_shift;

  bool test (uint32_t bit) const { return head & bit; }
  void set (uint32_t bit, bool value) {
    head = value ? (head | bit) : (head & ~bit);
  }
  void store_size (uint32_t n) {
    assert (n <= size_max);
    head = (head & flags_mask) | n << size_shift;
  }

  friend Ref alloc_constraint (Arena &, std::span<const Lit>, Kind, bool,
                               uint64_t);
  friend Constraint &deref (Arena &, Ref);
  friend const Constraint &deref (const Arena &, Ref);

public:
  Constraint () = delete;
  Constraint (const Constraint &) = delete;
  Constraint &operator= (const Constraint &) = delete;

  static constexpr uint32_t header_words = 3;
  // The limits of the packed header: allocating a larger constraint is a
  // fatal error, a larger id or glue is an assertion failure and
  // saturates, respectively.
  static constexpr uint32_t size_max = (1u << (32 - size_shift)) - 1;
  static constexpr uint64_t id_max =
      (uint64_t (1) << (32 + id_high_bits)) - 1;
  static constexpr uint32_t glue_max = (1u << glue_bits) - 1;

  // Number of arena words of a constraint with that many literals.  A
  // constraint has at least one literal, which also holds the forwarding
  // reference during garbage collection.
  static constexpr uint32_t words (uint32_t size) {
    return header_words + size;
  }
  uint32_t words () const { return words (size ()); }

  uint32_t size () const { return head >> size_shift; }
  std::span<Lit> lits () { return {lits_, size ()}; }
  std::span<const Lit> lits () const { return {lits_, size ()}; }
  Lit *begin () { return lits_; }
  Lit *end () { return lits_ + size (); }
  const Lit *begin () const { return lits_; }
  const Lit *end () const { return lits_ + size (); }
  Lit &operator[] (uint32_t i) { return lits_[i]; }
  const Lit &operator[] (uint32_t i) const { return lits_[i]; }

  // Lowers the size in place and returns the number of words that became
  // waste, which the caller reports to the arena.
  uint32_t shrink (uint32_t new_size) {
    assert (new_size >= 1 && new_size <= size ());
    const uint32_t freed = size () - new_size;
    store_size (new_size);
    return freed;
  }

  // Only for the buffer of 'model.cpp', which is allocated with the
  // largest size it can need and never watched or stored in a list: its
  // literals are rewritten in place, and the size can grow back up to the
  // allocated one, or be zero (the empty cube).
  void set_size (uint32_t n) { store_size (n); }

  Kind kind () const { return test (kind_bit) ? Kind::Cube : Kind::Clause; }
  bool redundant () const { return test (redundant_bit); }
  bool garbage () const { return test (garbage_bit); }
  bool moved () const { return test (moved_bit); }
  bool reason () const { return test (reason_bit); }
  void set_redundant (bool v) { set (redundant_bit, v); }
  void set_garbage (bool v) { set (garbage_bit, v); }
  void set_reason (bool v) { set (reason_bit, v); }

  uint32_t glue () const {
    return (id_high_glue & glue_mask) >> glue_shift;
  }
  void set_glue (uint32_t g) {
    id_high_glue = (id_high_glue & ~glue_mask) |
                   (std::min (g, glue_max) << glue_shift);
  }

  uint64_t id () const {
    return (uint64_t) (id_high_glue & id_high_mask) << 32 | id_low;
  }
  // A constraint changes its id when it is replaced in the proof by a
  // shorter one ('Proof::strengthen'), and so does the reused buffer of
  // 'model.cpp' for every initial cube.
  void set_id (uint64_t id) {
    assert (id <= id_max);
    id_low = static_cast<uint32_t> (id);
    id_high_glue =
        (id_high_glue & ~id_high_mask) | static_cast<uint32_t> (id >> 32);
  }

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
  if (lits.size () > Constraint::size_max)
    fatal ("constraint of %zu literals is too large", lits.size ());
  const uint32_t size = static_cast<uint32_t> (lits.size ());
  const Ref ref = arena.alloc (Constraint::words (size));
  Constraint &c = deref (arena, ref);
  c.head = (kind == Kind::Cube ? Constraint::kind_bit : 0u) |
           (redundant ? Constraint::redundant_bit : 0u);
  c.id_high_glue = 0;
  c.store_size (size);
  c.set_id (id);
  std::copy (lits.begin (), lits.end (), c.lits_);
  return ref;
}

} // namespace miniqu

#endif
