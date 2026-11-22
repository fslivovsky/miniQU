#ifndef MINIQU_LIMIT_HPP_INCLUDED
#define MINIQU_LIMIT_HPP_INCLUDED

#include <cstdint>

namespace miniqu {

// Scheduling state (ARCHITECTURE 9.4).  Events fire only when the main loop
// compares 'stats' with 'lim'; no technique schedules itself.

// Conflict count at which each event fires next.  The user limits are -1
// while unset.
struct Limit {
  int64_t restart = 0;
  int64_t reduce = 0;
  int64_t conflicts = -1;
  int64_t decisions = -1;
};

// The growing intervals.
struct Inc {
  int64_t restart = 0;
  int64_t reduce = 0;
};

// Conflict count when each pass last ran, to compute the effort since.
struct Last {
  int64_t restart = 0;
  int64_t reduce = 0;
};

} // namespace miniqu

#endif
