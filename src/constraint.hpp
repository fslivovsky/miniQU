#ifndef MINIQU_CONSTRAINT_HPP_INCLUDED
#define MINIQU_CONSTRAINT_HPP_INCLUDED

#include "arena.hpp"
#include "lit.hpp"
#include "message.hpp"

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <optional>
#include <span>

namespace miniqu {

// Layout of a clause or cube in the arena (ARCHITECTURE 5.2): one header
// word, the literals, then optional trailing words.
//
//   word 0          bits 0-5: kind, redundant, garbage, moved, reason,
//                   has_id; bits 6-31: size
//   words 1..size   literals
//   if redundant    one word: bits 0-13 saturating glue, 14-15 used,
//                   16-31 reserved
//   if has_id       two words: the 64-bit proof id, low word first
//
// This is MiniSat's scheme.  Under benchmark load (eight processes sharing
// one L3 cache) every header word in front of the literals costs measurable
// time, so what not every constraint needs trails behind them (STATUS.md,
// "M1 round 2: diagnosis of B1"; ARCHITECTURE 5.2).
//
// 'Constraint' is only ever a view onto arena words and is reached through
// 'deref'.  This file is the one place that knows the layout and the only
// one that does word arithmetic.

class Constraint {
  uint32_t head; // flags and size

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
  static constexpr uint32_t has_id_bit = 1u << 5;
  static constexpr unsigned size_shift = 6;
  static constexpr uint32_t flags_mask = (1u << size_shift) - 1;
  static constexpr unsigned glue_bits = 14;
  static constexpr uint32_t glue_mask = (1u << glue_bits) - 1;
  static constexpr unsigned used_shift = glue_bits;
  static constexpr uint32_t used_mask = 3u << used_shift;

  bool test (uint32_t bit) const { return head & bit; }
  void set (uint32_t bit, bool value) {
    head = value ? (head | bit) : (head & ~bit);
  }
  void store_size (uint32_t n) {
    assert (n <= size_max);
    head = (head & flags_mask) | n << size_shift;
  }

  uint32_t *word (uint32_t i) {
    return reinterpret_cast<uint32_t *> (this) + i;
  }
  const uint32_t *word (uint32_t i) const {
    return reinterpret_cast<const uint32_t *> (this) + i;
  }
  // The trailing words start right after the last literal.
  static constexpr uint32_t trailing_words (bool redundant, bool has_id) {
    return (redundant ? 1u : 0u) + (has_id ? 2u : 0u);
  }
  uint32_t trailing_words () const {
    return trailing_words (redundant (), has_id ());
  }
  uint32_t glue_word () const { return 1 + size (); }
  uint32_t id_word () const {
    return 1 + size () + (redundant () ? 1u : 0u);
  }

  friend Ref alloc_constraint (Arena &, std::span<const Lit>, Kind, bool,
                               std::optional<uint64_t>);
  friend Constraint &deref (Arena &, Ref);
  friend const Constraint &deref (const Arena &, Ref);

public:
  Constraint () = delete;
  Constraint (const Constraint &) = delete;
  Constraint &operator= (const Constraint &) = delete;

  // Allocating a larger constraint is a fatal error; a larger glue
  // saturates.
  static constexpr uint32_t size_max = (1u << (32 - size_shift)) - 1;
  static constexpr uint32_t glue_max = glue_mask;
  static constexpr uint32_t used_max = 2;

  // Number of arena words of a constraint.  A constraint has at least one
  // literal, which also holds the forwarding reference during garbage
  // collection.
  static constexpr uint32_t words (uint32_t size, bool redundant,
                                   bool has_id) {
    return 1 + size + trailing_words (redundant, has_id);
  }
  uint32_t words () const {
    return words (size (), redundant (), has_id ());
  }

  uint32_t size () const { return head >> size_shift; }
  std::span<Lit> lits () { return {lits_, size ()}; }
  std::span<const Lit> lits () const { return {lits_, size ()}; }
  Lit *begin () { return lits_; }
  Lit *end () { return lits_ + size (); }
  const Lit *begin () const { return lits_; }
  const Lit *end () const { return lits_ + size (); }
  Lit &operator[] (uint32_t i) { return lits_[i]; }
  const Lit &operator[] (uint32_t i) const { return lits_[i]; }

  // Lowers the size in place, moving the trailing words behind the new
  // last literal, and returns the number of words that became waste,
  // which the caller reports to the arena.
  uint32_t shrink (uint32_t new_size) {
    assert (new_size >= 1 && new_size <= size ());
    const uint32_t freed = size () - new_size;
    const uint32_t *trailing = word (1 + size ());
    std::copy (trailing, trailing + trailing_words (), word (1 + new_size));
    store_size (new_size);
    return freed;
  }

  // Only for the buffer of 'model.cpp', which is irredundant, allocated
  // with the largest size it can need and never watched or stored in a
  // list: its literals are rewritten in place after this call, and the
  // size can grow back up to the allocated one, or be zero (the empty
  // cube).  The id words move with the size and stay inside the
  // allocation.
  void set_size (uint32_t n) {
    assert (!redundant ());
    if (!has_id ()) {
      store_size (n);
      return;
    }
    const uint64_t saved = id ();
    store_size (n);
    set_id (saved);
  }

  Kind kind () const { return test (kind_bit) ? Kind::Cube : Kind::Clause; }
  bool redundant () const { return test (redundant_bit); }
  bool garbage () const { return test (garbage_bit); }
  bool moved () const { return test (moved_bit); }
  bool reason () const { return test (reason_bit); }
  bool has_id () const { return test (has_id_bit); }
  void set_garbage (bool v) { set (garbage_bit, v); }
  void set_reason (bool v) { set (reason_bit, v); }

  // Only redundant constraints store a glue.
  uint32_t glue () const {
    return redundant () ? *word (glue_word ()) & glue_mask : 0;
  }
  void set_glue (uint32_t g) {
    assert (redundant ());
    uint32_t &w = *word (glue_word ());
    w = (w & ~glue_mask) | std::min (g, glue_max);
  }

  // How recently a learnt constraint was learnt or used in an analysis
  // (tier.cpp): 0 for irredundant constraints and deletion candidates.
  uint32_t used () const {
    return redundant () ? (*word (glue_word ()) & used_mask) >> used_shift
                        : 0;
  }
  void set_used (uint32_t u) {
    assert (redundant () && u <= used_max);
    uint32_t &w = *word (glue_word ());
    w = (w & ~used_mask) | u << used_shift;
  }

  uint64_t id () const {
    assert (has_id ());
    const uint32_t *w = word (id_word ());
    return (uint64_t) w[1] << 32 | w[0];
  }
  // A constraint changes its id when it is replaced in the proof by a
  // shorter one ('Proof::strengthen'), and so does the reused buffer of
  // 'model.cpp' for every initial cube.
  void set_id (uint64_t id) {
    assert (has_id ());
    uint32_t *w = word (id_word ());
    w[0] = static_cast<uint32_t> (id);
    w[1] = static_cast<uint32_t> (id >> 32);
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

// Allocates and fills a constraint, with id words iff 'id' has a value;
// glue starts at zero.
inline Ref alloc_constraint (Arena &arena, std::span<const Lit> lits,
                             Kind kind, bool redundant,
                             std::optional<uint64_t> id) {
  assert (!lits.empty ());
  if (lits.size () > Constraint::size_max)
    fatal ("constraint of %zu literals is too large", lits.size ());
  const uint32_t size = static_cast<uint32_t> (lits.size ());
  const Ref ref =
      arena.alloc (Constraint::words (size, redundant, id.has_value ()));
  Constraint &c = deref (arena, ref);
  c.head = (kind == Kind::Cube ? Constraint::kind_bit : 0u) |
           (redundant ? Constraint::redundant_bit : 0u) |
           (id ? Constraint::has_id_bit : 0u);
  c.store_size (size);
  std::copy (lits.begin (), lits.end (), c.lits_);
  if (redundant)
    *c.word (c.glue_word ()) = 0;
  if (id)
    c.set_id (*id);
  return ref;
}

// Garbage collection: a word-by-word copy into another arena, flags and
// trailing words included, of a constraint that is neither garbage, moved
// nor protected.
inline Ref copy_constraint (Arena &to, const Constraint &from) {
  assert (!from.garbage () && !from.moved () && !from.reason ());
  const uint32_t words = from.words ();
  const Ref ref = to.alloc (words);
  const uint32_t *source = reinterpret_cast<const uint32_t *> (&from);
  std::copy (source, source + words, to.words (ref));
  return ref;
}

// The number by which messages name a constraint: its proof id, or 0 when
// ids are not stored.
inline uint64_t message_id (const Constraint &c) {
  return c.has_id () ? c.id () : 0;
}

} // namespace miniqu

#endif
