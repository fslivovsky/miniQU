#include "profile.hpp"
#include "util.hpp"

#include <cassert>

namespace miniqu {

void Profiles::start (Profile &p) {
  if (p.level > enabled || p.active)
    return;
  p.active = true;
  p.started = process_time ();
}

void Profiles::stop (Profile &p) {
  if (!p.active)
    return;
  p.total += process_time () - p.started;
  p.active = false;
}

void Profiles::print (FILE *file) const {
  const double total = process_time ();
  fprintf (file, "c\nc profile (CPU seconds, percent of total %.2f)\n",
           total);
#define PROFILE(NAME, LEVEL) \
  if (NAME.level <= enabled) \
    fprintf (file, "c %12.2f %6.2f%% " #NAME "\n", NAME.total, \
             percent (NAME.total, total));
  PROFILES
#undef PROFILE
}

} // namespace miniqu
