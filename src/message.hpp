#ifndef MINIQU_MESSAGE_HPP_INCLUDED
#define MINIQU_MESSAGE_HPP_INCLUDED

namespace miniqu {

// Progress output.  Every line goes to stdout prefixed with "c ", so that
// stdout stays valid for the harness (ARCHITECTURE 9.5).  Verbosity is
// process-wide: there is one solver per process, and the printing helpers
// live below the layer that owns options.
//
//   0  nothing        2  progress ('PHASE' lines)
//   1  summary        3  detail

void set_verbosity (int level);
int verbosity ();

#if defined(__GNUC__)
#define MINIQU_PRINTF(FMT, ARGS) \
  __attribute__ ((format (printf, FMT, ARGS)))
#else
#define MINIQU_PRINTF(FMT, ARGS)
#endif

// Printed at verbosity >= 1.
void message (const char *fmt, ...) MINIQU_PRINTF (1, 2);

// Printed at verbosity >= level.
void verbose (int level, const char *fmt, ...) MINIQU_PRINTF (2, 3);

// '[name-count] text', printed at verbosity >= 2.
void phase (const char *name, long count, const char *fmt, ...)
    MINIQU_PRINTF (3, 4);

// Error message on stderr, then exit (1).  The solver uses no exceptions.
[[noreturn]] void fatal (const char *fmt, ...) MINIQU_PRINTF (1, 2);

} // namespace miniqu

#define MSG(...) ::miniqu::message (__VA_ARGS__)
#define VERBOSE(LEVEL, ...) ::miniqu::verbose ((LEVEL), __VA_ARGS__)
#define PHASE(NAME, COUNT, ...) \
  ::miniqu::phase ((NAME), (long) (COUNT), __VA_ARGS__)

#endif
