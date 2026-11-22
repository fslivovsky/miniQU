#ifndef MINIQU_UTIL_HPP_INCLUDED
#define MINIQU_UTIL_HPP_INCLUDED

#include <ctime>

namespace miniqu {

// Small helpers for statistics and profiling.

// 'a / b', or 0 when 'b' is zero, so that tables never print nan.
inline double relative (double a, double b) { return b != 0 ? a / b : 0; }
inline double percent (double a, double b) { return 100 * relative (a, b); }

// CPU time of the process in seconds.
inline double process_time () {
  timespec t;
  clock_gettime (CLOCK_PROCESS_CPUTIME_ID, &t);
  return (double) t.tv_sec + 1e-9 * (double) t.tv_nsec;
}

} // namespace miniqu

#endif
