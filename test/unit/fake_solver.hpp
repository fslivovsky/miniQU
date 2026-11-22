#ifndef MINIQU_FAKE_SOLVER_HPP_INCLUDED
#define MINIQU_FAKE_SOLVER_HPP_INCLUDED

#include "lit.hpp"

#include <string>
#include <vector>

// A link-time substitute for 'miniqu::Solver' (fake_solver.cpp) that
// records every call, so that the frontend can be tested without a solver.
// There is one global log, because the members of the fake keep no state of
// their own.

struct FakeCall {
  enum class Type {
    Set,
    AddVar,
    AddOriginal,
    Freeze,
    ConnectTracer,
    Solve,
    Terminate,
    FlushProof,
    Statistics
  };
  explicit FakeCall (Type t) : type (t) {}
  Type type;
  int var = 0; // also the value of 'set'
  miniqu::Quant quant = miniqu::Quant::Exists;
  bool decision = true;
  int proof_number = 0;
  miniqu::Kind kind = miniqu::Kind::Clause;
  std::vector<int> lits;
  int proof_gate = 0;
  std::string option;
};

std::vector<FakeCall> &fake_calls ();
void fake_reset ();

// For formulas too large to keep every call: without recording, only the
// totals are counted.
struct FakeCounts {
  size_t vars = 0, clauses = 0, cubes = 0, literals = 0;
};
extern bool fake_recording;
FakeCounts &fake_counts ();

// One line per call to 'add_var' ("var 5 e - 3": variable, quantifier
// e or a, decision flag d or -, proof number) and 'add_original' ("c 2: 1
// -4", kind c or t, proof gate, literals), in order.
std::vector<std::string> fake_trace ();

#endif
