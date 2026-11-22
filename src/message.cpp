#include "message.hpp"

#include <cstdarg>
#include <cstdio>
#include <cstdlib>

namespace miniqu {

static int verbosity_level = 1;

void set_verbosity (int level) { verbosity_level = level; }
int verbosity () { return verbosity_level; }

static void print_line (const char *prefix, const char *fmt, va_list &ap) {
  fputs ("c ", stdout);
  fputs (prefix, stdout);
  vprintf (fmt, ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void message (const char *fmt, ...) {
  if (verbosity_level < 1)
    return;
  va_list ap;
  va_start (ap, fmt);
  print_line ("", fmt, ap);
  va_end (ap);
}

void verbose (int level, const char *fmt, ...) {
  if (verbosity_level < level)
    return;
  va_list ap;
  va_start (ap, fmt);
  print_line ("", fmt, ap);
  va_end (ap);
}

void phase (const char *name, long count, const char *fmt, ...) {
  if (verbosity_level < 2)
    return;
  char prefix[64];
  snprintf (prefix, sizeof prefix, "[%s-%ld] ", name, count);
  va_list ap;
  va_start (ap, fmt);
  print_line (prefix, fmt, ap);
  va_end (ap);
}

void fatal (const char *fmt, ...) {
  fflush (stdout);
  fputs ("miniQU: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

} // namespace miniqu
