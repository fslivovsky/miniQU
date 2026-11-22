#ifndef MINIQU_ARENA_HPP_INCLUDED
#define MINIQU_ARENA_HPP_INCLUDED

#include "lit.hpp"

#include <cstdint>

namespace miniqu {

// A region of 32-bit words with bump allocation, MiniSat's
// 'RegionAllocator<uint32_t>' (ARCHITECTURE 5.1).  Constraints that are
// visited together are adjacent, and a reference is four bytes.  Freeing
// only accounts the words as wasted; memory is reclaimed by copying the
// live constraints into a fresh arena and calling 'move_to'.
//
// Any allocation may move the buffer, so a pointer obtained from 'words'
// is invalid after the next 'alloc'; hold the 'Ref' instead.

class Arena {
  uint32_t *memory = nullptr;
  uint32_t size_ = 0;
  uint32_t capacity_ = 0;
  uint32_t wasted_ = 0;

  void reserve (uint32_t min_capacity);

public:
  explicit Arena (uint32_t initial_capacity = 1u << 20);
  ~Arena ();
  Arena (const Arena &) = delete;
  Arena &operator= (const Arena &) = delete;

  [[nodiscard]] Ref alloc (uint32_t words);
  void free (uint32_t words) { wasted_ += words; }

  uint32_t size () const { return size_; }
  uint32_t wasted () const { return wasted_; }

  // Replace the contents of 'to' by this arena; this arena becomes empty.
  void move_to (Arena &to);

  // Raw word access.  Only 'constraint.hpp' may use it.
  uint32_t *words (Ref r);
  const uint32_t *words (Ref r) const;
};

} // namespace miniqu

#endif
