#ifndef MINIQU_TEST_HPP_INCLUDED
#define MINIQU_TEST_HPP_INCLUDED

// Minimal test support: failed checks are reported and make 'main' exit
// with a nonzero status ('return test_result ();').

#include <cstdio>

inline int test_failures = 0;

#define CHECK(COND) \
  do { \
    if (!(COND)) { \
      fprintf (stderr, "%s:%d: CHECK failed: %s\n", __FILE__, __LINE__, \
               #COND); \
      test_failures++; \
    } \
  } while (0)

#define CHECK_EQ(A, B) \
  do { \
    const auto a_ = (A); \
    const auto b_ = (B); \
    if (!(a_ == b_)) { \
      fprintf (stderr, "%s:%d: CHECK_EQ failed: %s == %s\n", __FILE__, \
               __LINE__, #A, #B); \
      test_failures++; \
    } \
  } while (0)

inline int test_result () {
  if (test_failures)
    fprintf (stderr, "%d check(s) failed\n", test_failures);
  return test_failures ? 1 : 0;
}

#endif
