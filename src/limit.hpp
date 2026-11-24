#ifndef MINIQU_LIMIT_HPP_INCLUDED
#define MINIQU_LIMIT_HPP_INCLUDED

#include <cstdint>

namespace miniqu {

// Scheduling state (ARCHITECTURE 9.4).  Events fire only when the main loop
// compares 'stats' with 'lim'; no technique schedules itself.

// Conflict count at which each event fires next.
struct Limit {
  int64_t restart = 0;
  int64_t reduce = 0;
  int64_t retier = 0;
  double max_learnts = 0; // size trigger of 'reduce' (old policy)
  int64_t adjust = 0;     // conflicts until 'max_learnts' grows
};

// The growing intervals.
struct Inc {
  double adjust = 0; // current conflicts between two growths
};

} // namespace miniqu

#endif
