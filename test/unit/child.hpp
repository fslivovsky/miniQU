#ifndef MINIQU_CHILD_HPP_INCLUDED
#define MINIQU_CHILD_HPP_INCLUDED

// Death tests: run a function in a child process and look at how it ended
// and what it wrote to standard error.

#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <sys/wait.h>
#include <unistd.h>

struct ChildResult {
  int status = 0; // as returned by 'waitpid'
  std::string error;
};

template <class F> ChildResult run_child (F function) {
  int fds[2];
  if (pipe (fds))
    abort ();
  fflush (nullptr);
  const pid_t pid = fork ();
  if (pid == 0) {
    close (fds[0]);
    dup2 (fds[1], 2);
    function ();
    _exit (0);
  }
  close (fds[1]);
  ChildResult result;
  char buffer[512];
  for (ssize_t n; (n = read (fds[0], buffer, sizeof buffer)) > 0;)
    result.error.append (buffer, static_cast<size_t> (n));
  close (fds[0]);
  waitpid (pid, &result.status, 0);
  return result;
}

inline bool child_ended (const ChildResult &result, bool ok,
                         const std::string &expected) {
  ok = ok && result.error.find (expected) != std::string::npos;
  if (!ok)
    fprintf (stderr,
             "expected failure containing '%s', got status %d: %s\n",
             expected.c_str (), result.status, result.error.c_str ());
  return ok;
}

// True if 'function' ends the process through 'fatal' (exit status 1) with
// a message containing 'expected'.
template <class F>
bool dies_with (F function, const std::string &expected) {
  const ChildResult result = run_child (function);
  return child_ended (
      result, WIFEXITED (result.status) && WEXITSTATUS (result.status) == 1,
      expected);
}

// True if 'function' violates an API contract: 'REQUIRE' aborts.
template <class F>
bool aborts_with (F function, const std::string &expected) {
  const ChildResult result = run_child (function);
  return child_ended (result,
                      WIFSIGNALED (result.status) &&
                          WTERMSIG (result.status) == SIGABRT,
                      expected);
}

#endif
