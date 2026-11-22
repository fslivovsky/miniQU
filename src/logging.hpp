#ifndef MINIQU_LOGGING_HPP_INCLUDED
#define MINIQU_LOGGING_HPP_INCLUDED

// 'LOG (...)' traces state changes.  It exists only when compiled with
// MINIQU_LOGGING and prints only when 'set_logging (true)' was called
// (option 'log'); otherwise it expands to nothing, so release code carries
// no trace of it.
//
// The call is unqualified on purpose: in the base layer it reaches the
// plain printf form below, inside member functions of 'Internal' it reaches
// the members 'Internal::log', which add the decision level and can print a
// constraint: 'LOG (ref, "propagating")' (ARCHITECTURE 9.5).

#ifdef MINIQU_LOGGING

namespace miniqu {

void set_logging (bool enabled);
bool logging ();
void log (const char *fmt, ...) __attribute__ ((format (printf, 1, 2)));

} // namespace miniqu

#define LOG(...) \
  do { \
    if (::miniqu::logging ()) \
      log (__VA_ARGS__); \
  } while (0)

#else

#define LOG(...) \
  do { \
  } while (0)

#endif

#endif
