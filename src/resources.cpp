// Resource limits and usage of the process, through 'setrlimit' and
// 'getrusage' as in the old 'System.cc' and CaDiCaL's 'resources.cpp'.  A
// hard limit below the requested one is left alone, as in the old code.

#include "resources.hpp"

#include <cstdio>
#include <sys/resource.h>

namespace miniqu {

static void lower_soft_limit (int resource, rlim_t value,
                              const char *name) {
  rlimit limit;
  getrlimit (resource, &limit);
  if (limit.rlim_max != RLIM_INFINITY && value >= limit.rlim_max)
    return;
  limit.rlim_cur = value;
  if (setrlimit (resource, &limit))
    fprintf (stderr, "miniQU: warning: could not set the %s limit\n", name);
}

void limit_time (int seconds) {
  if (seconds > 0)
    lower_soft_limit (RLIMIT_CPU, (rlim_t) seconds, "CPU time");
}

void limit_memory (int megabytes) {
  if (megabytes > 0)
    lower_soft_limit (RLIMIT_AS, (rlim_t) megabytes << 20, "memory");
}

uint64_t maximum_resident_set_size () {
  rusage usage;
  getrusage (RUSAGE_SELF, &usage);
  return (uint64_t) usage.ru_maxrss << 10;
}

} // namespace miniqu
