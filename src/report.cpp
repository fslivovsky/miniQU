// Progress lines (ARCHITECTURE 9.5), one per scheduled event at verbosity
// 2 and above.  Only reads counters and database sizes.

#include "internal.hpp"

#include <cinttypes>

namespace miniqu {

void Internal::report (const char *event) const {
  PHASE (event, stats.restarts,
         "conflicts %" PRId64 " decisions %" PRId64
         " learnt clauses %zu cubes %zu, trail at root %zu",
         stats.conflicts, stats.decisions,
         redundant[index (Kind::Clause)].size (),
         redundant[index (Kind::Cube)].size (), trail.size ());
}

} // namespace miniqu
