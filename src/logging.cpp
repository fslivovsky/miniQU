#include "logging.hpp"

#ifdef MINIQU_LOGGING

#include "internal.hpp"

#include <cinttypes>
#include <cstdarg>
#include <cstdio>

namespace miniqu {

static bool logging_enabled = false;

void set_logging (bool enabled) { logging_enabled = enabled; }
bool logging () { return logging_enabled; }

static void vlog (const char *prefix, int level, const char *fmt,
                  va_list ap) {
  fputs (prefix, stdout);
  if (level >= 0)
    printf ("%d ", level);
  vprintf (fmt, ap);
}

void log (const char *fmt, ...) {
  va_list ap;
  va_start (ap, fmt);
  vlog ("c LOG ", -1, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void Internal::log (const char *fmt, ...) const {
  va_list ap;
  va_start (ap, fmt);
  vlog ("c LOG ", decision_level (), fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

// A literal as quantifier, internal variable number counted from 1, sign,
// and, if assigned, value and level: "e-3=-1@2".
void Internal::log (Ref ref, const char *fmt, ...) const {
  va_list ap;
  va_start (ap, fmt);
  vlog ("c LOG ", decision_level (), fmt, ap);
  va_end (ap);
  const Constraint &c = deref (arena, ref);
  printf (" %s%s %s[%" PRIu64 "] glue %u size %u:",
          c.redundant () ? "redundant" : "irredundant",
          c.garbage () ? " garbage" : "",
          c.kind () == Kind::Clause ? "clause" : "cube", c.id (), c.glue (),
          c.size ());
  for (Lit l : c) {
    const Var v = var (l);
    printf (" %c%s%u", prefix.quant (v) == Quant::Exists ? 'e' : 'a',
            sign (l) ? "-" : "", v + 1);
    if (val (l))
      printf ("=%d@%d", val (l), level (v));
  }
  fputc ('\n', stdout);
  fflush (stdout);
}

} // namespace miniqu

#endif
