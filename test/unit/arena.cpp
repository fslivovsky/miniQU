#include "arena.hpp"
#include "test.hpp"

#include <vector>

using namespace miniqu;

int main () {
  Arena arena (16);
  CHECK_EQ (arena.size (), 0u);
  CHECK_EQ (arena.wasted (), 0u);

  const Ref a = arena.alloc (5);
  const Ref b = arena.alloc (7);
  CHECK_EQ (static_cast<uint32_t> (a), 0u);
  CHECK_EQ (static_cast<uint32_t> (b), 5u);
  CHECK_EQ (arena.size (), 12u);

  arena.free (5);
  CHECK_EQ (arena.wasted (), 5u);
  CHECK_EQ (arena.size (), 12u);

  // Growth across many reallocations; contents and references stay valid.
  for (uint32_t i = 0; i < 5; i++)
    arena.words (a)[i] = 100 + i;
  std::vector<Ref> refs;
  for (uint32_t i = 0; i < 10000; i++) {
    const Ref r = arena.alloc (3);
    for (uint32_t j = 0; j < 3; j++)
      arena.words (r)[j] = i * 3 + j;
    refs.push_back (r);
  }
  CHECK_EQ (arena.size (), 12u + 30000u);
  for (uint32_t i = 0; i < 5; i++)
    CHECK_EQ (arena.words (a)[i], 100 + i);
  for (uint32_t i = 0; i < refs.size (); i++)
    for (uint32_t j = 0; j < 3; j++)
      CHECK_EQ (arena.words (refs[i])[j], i * 3 + j);

  // 'move_to' transfers contents and accounting and empties the source.
  Arena other (16);
  const Ref junk = other.alloc (4);
  (void) junk;
  arena.move_to (other);
  CHECK_EQ (other.size (), 12u + 30000u);
  CHECK_EQ (other.wasted (), 5u);
  CHECK_EQ (other.words (refs[9999])[2], 29999u);
  CHECK_EQ (arena.size (), 0u);
  CHECK_EQ (arena.wasted (), 0u);

  // The emptied arena is usable again.
  const Ref c = arena.alloc (2);
  CHECK_EQ (static_cast<uint32_t> (c), 0u);

  return test_result ();
}
