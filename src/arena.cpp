#include "arena.hpp"
#include "message.hpp"

#include <cassert>
#include <cstdlib>

namespace miniqu {

Arena::Arena (uint32_t initial_capacity) { reserve (initial_capacity); }

Arena::~Arena () { ::free (memory); }

void Arena::reserve (uint32_t min_capacity) {
  if (capacity_ >= min_capacity)
    return;
  const uint32_t previous = capacity_;
  while (capacity_ < min_capacity) {
    // Multiply by 13/8 without overflow, add 2 and clear the lowest bit
    // (MiniSat).  The sequence of capacities ends close to 2^32-1, so that
    // nearly the whole range of 32-bit references is usable.
    const uint32_t delta = ((capacity_ >> 1) + (capacity_ >> 3) + 2) & ~1u;
    capacity_ += delta;
    if (capacity_ <= previous)
      fatal ("out of memory: arena exceeds 2^32 words");
  }
  void *p = realloc (memory, sizeof (uint32_t) * (size_t) capacity_);
  if (!p)
    fatal ("out of memory: arena of %u words", capacity_);
  memory = static_cast<uint32_t *> (p);
}

Ref Arena::alloc (uint32_t words) {
  assert (words > 0);
  const uint32_t start = size_;
  if (words > UINT32_MAX - start)
    fatal ("out of memory: arena exceeds 2^32 words");
  reserve (start + words);
  size_ = start + words;
  return static_cast<Ref> (start);
}

void Arena::move_to (Arena &to) {
  ::free (to.memory);
  to.memory = memory;
  to.size_ = size_;
  to.capacity_ = capacity_;
  to.wasted_ = wasted_;
  memory = nullptr;
  size_ = capacity_ = wasted_ = 0;
}

uint32_t *Arena::words (Ref r) {
  assert (static_cast<uint32_t> (r) < size_);
  return memory + static_cast<uint32_t> (r);
}

const uint32_t *Arena::words (Ref r) const {
  assert (static_cast<uint32_t> (r) < size_);
  return memory + static_cast<uint32_t> (r);
}

} // namespace miniqu
