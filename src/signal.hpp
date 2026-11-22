#ifndef MINIQU_SIGNAL_HPP_INCLUDED
#define MINIQU_SIGNAL_HPP_INCLUDED

namespace miniqu {

class Solver;

// Termination signals of the application: SIGINT, SIGTERM and SIGXCPU
// (sent by the kernel when '--cpulim' runs out).

// Installs the handler.  Until 'forward_signals' is called a signal ends
// the process at once (exit code 1).
void catch_signals ();

// From now on the first signal asks the solver to stop ('terminate' sets a
// flag, so that the run ends with "unknown" and statistics are printed);
// a second one ends the process at once.
void forward_signals (Solver &);

} // namespace miniqu

#endif
