#ifndef MINIQU_LOGGING_HPP_INCLUDED
#define MINIQU_LOGGING_HPP_INCLUDED

// 'LOG (...)' traces state changes.  It exists only when compiled with
// MINIQU_LOGGING and prints only when 'set_logging (true)' was called
// (option 'log'); otherwise it expands to nothing, so release code carries
// no trace of it.  Printing constraints with ids and levels is added with
// the constraint database; this is the plain printf form.

#ifdef MINIQU_LOGGING

namespace miniqu {

void set_logging (bool enabled);
bool logging ();
void log (const char *fmt, ...) __attribute__ ((format (printf, 1, 2)));

} // namespace miniqu

#define LOG(...) \
  do { \
    if (::miniqu::logging ()) \
      ::miniqu::log (__VA_ARGS__); \
  } while (0)

#else

#define LOG(...) \
  do { \
  } while (0)

#endif

#endif
