#ifndef MINIQU_CONTRACT_HPP_INCLUDED
#define MINIQU_CONTRACT_HPP_INCLUDED

#include <cstdio>
#include <cstdlib>

// Contracts guard the public API against misuse and are active in every
// build; a violation is a bug of the caller, so we abort with the message.
// Internal invariants use 'assert' instead (ARCHITECTURE 9.6).

namespace miniqu {

// Whether 'assert' is active, for code that runs an expensive check only
// then.
#ifdef NDEBUG
inline constexpr bool assertions_enabled = false;
#else
inline constexpr bool assertions_enabled = true;
#endif

} // namespace miniqu

#define REQUIRE(COND, MSG) \
  do { \
    if (!(COND)) { \
      fprintf (stderr, "miniQU: API contract violated in '%s': %s\n", \
               __func__, (MSG)); \
      fflush (stderr); \
      abort (); \
    } \
  } while (0)

#endif
