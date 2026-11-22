// Signal handling of the application (ARCHITECTURE 8.2).
//
// The handler writes nothing but one fixed line and touches no solver state
// besides the termination flag: everything else (flushing a proof,
// printing statistics and the result) happens in 'app.cpp' after 'solve'
// has returned.  This reproduces the old binary: a signal while parsing
// ends the run with exit code 1, a signal during the search ends it with
// "INDETERMINATE" and exit code 0, which is also how a CPU limit ends.

#include "signal.hpp"
#include "miniqu.hpp"

#include <atomic>
#include <csignal>
#include <unistd.h>

namespace miniqu {

namespace {

std::atomic<Solver *> target = nullptr;
std::atomic<int> caught = 0;

constexpr int signals[] = {SIGINT, SIGTERM, SIGXCPU};

extern "C" void handle (int) {
  Solver *solver = target.load ();
  if (!caught.fetch_add (1) && solver) {
    solver->terminate ();
    return;
  }
  static const char message[] = "c interrupted\n";
  [[maybe_unused]] const ssize_t ignored =
      write (STDOUT_FILENO, message, sizeof message - 1);
  _exit (1);
}

} // namespace

void catch_signals () {
  for (int sig : signals)
    signal (sig, handle);
}

void forward_signals (Solver &solver) { target = &solver; }

} // namespace miniqu
