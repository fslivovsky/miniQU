#ifndef MINIQU_MINIQU_HPP_INCLUDED
#define MINIQU_MINIQU_HPP_INCLUDED

#include "lit.hpp"
#include "tracer.hpp"

#include <memory>
#include <span>
#include <string_view>
#include <vector>

namespace miniqu {

struct Internal;

// The public interface of the solver (ARCHITECTURE 3.5).  It is
// single-shot: the formula is given once, in this order, then 'solve' is
// called once.
//
//   1. 'set' options,
//   2. 'add_var' for every variable, in prefix order (outermost first),
//   3. 'connect_tracer' (optional),
//   4. 'add_original' for every constraint,
//   5. 'solve', then 'val' / 'certificate'.
//
// User variables and literals are nonzero 'int's as in DIMACS: variable
// numbers are positive and need not be dense, a literal is the number or
// its negation.  Violations of the order or of the argument ranges abort
// through 'REQUIRE' in every build.
class Solver {
public:
  Solver ();
  ~Solver ();
  Solver (const Solver &) = delete;
  Solver &operator= (const Solver &) = delete;

  // Sets an option by name (one of 'option_table ()'); false if the value
  // is out of range.  Only before the first 'add_var'.
  bool set (std::string_view option, int value);

  // Declares variable 'var'.  Consecutive calls with the same quantifier
  // form one quantifier block.  A variable with 'decision' false is never
  // decided (gate variables of a circuit).  'proof_number' is the number
  // under which tracers see the variable, 0 if the input has none.
  void add_var (int var, Quant, bool decision = true, int proof_number = 0);

  // Adds a clause or cube over declared variables.  Duplicate literals are
  // removed and a constraint with a literal and its negation is dropped, so
  // callers can pass the raw encoding of a gate.  'proof_gate' is the proof
  // number of the gate whose definition the constraint belongs to, 0 for
  // the output or when there is none.
  void add_original (Kind, std::span<const int> lits, int proof_gate = 0);

  // Protects a variable from elimination.
  void freeze (int var);

  // The tracer receives every proof step from now on.
  void connect_tracer (std::unique_ptr<Tracer>);

  // 10: true, 20: false, 0: unknown (limit reached or 'terminate' called).
  int solve ();

  // Value (1, -1 or 0 = unassigned) of a variable of the certificate block,
  // the outermost block (ARCHITECTURE 10.4), after a definite answer.
  int val (int var) const;
  std::vector<int> certificate () const;

  // Asks 'solve' to return as soon as possible; async-signal-safe.
  void terminate ();

  // Flushes connected tracers; not async-signal-safe.
  void flush_proof ();

  // Prints the statistics table.
  void statistics () const;

private:
  struct Impl; // user <-> internal variable maps, call-order state,
               // Internal
  std::unique_ptr<Impl> impl;

  // The solver state behind the interface, for white-box tests only.
  friend Internal &internal_of (Solver &);
};

} // namespace miniqu

#endif
