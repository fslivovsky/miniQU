#include "logging.hpp"

#ifdef MINIQU_LOGGING

#include <cstdarg>
#include <cstdio>

namespace miniqu {

static bool logging_enabled = false;

void set_logging (bool enabled) { logging_enabled = enabled; }
bool logging () { return logging_enabled; }

void log (const char *fmt, ...) {
  fputs ("c LOG ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

} // namespace miniqu

#endif
