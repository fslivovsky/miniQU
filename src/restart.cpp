// Restarts on the old schedule (ARCHITECTURE 7.1, 9.4): the search goes
// back to the root when the conflicts since the last restart reach the
// current interval.  The k-th interval (k = 0, 1, ...) is
// 'rfirst * luby (rinc, k)' with '--luby' (the default), otherwise
// 'rfirst * rinc^k', with 'rinc' in percent; both truncated to an integer
// as the old 'search (rest_base * restart_first)' does.
//
// A restart keeps everything learnt and only undoes assignments, so it has
// no proof steps.

#include "internal.hpp"

#include <cmath>
#include <cstdint>

namespace miniqu {

// 'y' to the power of the k-th element (from 0) of the Luby sequence
// 0 0 1 0 0 1 2 0 0 1 0 0 1 2 3 ... (MiniSat's 'luby').  The sequence is
// made of finite prefixes of sizes 2^n - 1; find the one containing 'k',
// then descend into the left or right copy of the previous prefix.
static double luby (double y, int64_t k) {
  int64_t size = 1;
  int seq = 0;
  while (size < k + 1) {
    seq++;
    size = 2 * size + 1;
  }
  while (size - 1 != k) {
    size = (size - 1) >> 1;
    seq--;
    k = k % size;
  }
  return std::pow (y, seq);
}

int64_t Internal::restart_interval (int64_t restarts) const {
  const double base = opts.rinc / 100.0;
  const double factor = opts.luby ? luby (base, restarts)
                                  : std::pow (base, (double) restarts);
  const double interval = factor * opts.rfirst;
  // The geometric sequence leaves the integers after a few hundred
  // restarts; the old code would overflow there.
  return interval < (double) INT64_MAX / 2 ? (int64_t) interval
                                           : INT64_MAX / 2;
}

bool Internal::restarting () const {
  return stats.conflicts >= lim.restart;
}

void Internal::restart () {
  stats.restarts++;
  backtrack (0);
  lim.restart = stats.conflicts + restart_interval (stats.restarts);
  report ("restart");
}

} // namespace miniqu
