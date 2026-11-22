// The public 'Solver' (ARCHITECTURE 3.5): checks the call order and the
// arguments of every call, translates user variables to internal ones and
// back, and forwards to 'Internal'.  It contains no solver logic.
//
// Internal variables are created in the order of the 'add_var' calls,
// which is prefix order, so the map is a renumbering and nothing else.

#include "contract.hpp"
#include "internal.hpp"
#include "message.hpp"
#include "miniqu.hpp"
#include "util.hpp"

#include <algorithm>
#include <climits>
#include <cstdio>
#include <cstdlib>

namespace miniqu {

namespace {

constexpr Var undeclared = UINT32_MAX;

// The calls must come in this order (miniqu.hpp).
enum class Stage { Options, Variables, Constraints, Solved };

} // namespace

struct Solver::Impl {
  Internal internal;
  Stage stage = Stage::Options;
  std::vector<Var> internal_of; // per user variable
  std::vector<int> user_of;     // per internal variable
  std::vector<Lit> lits;        // to translate a constraint

  bool declared (int var) const {
    return var > 0 && (size_t) var < internal_of.size () &&
           internal_of[(size_t) var] != undeclared;
  }

  Lit translate (int lit) const {
    REQUIRE (lit != 0 && lit != INT_MIN, "invalid literal");
    REQUIRE (declared (std::abs (lit)),
             "literal of an undeclared variable");
    return mk_lit (internal_of[(size_t) std::abs (lit)], lit < 0);
  }
};

Internal &internal_of (Solver &solver) { return solver.impl->internal; }

Solver::Solver () : impl (std::make_unique<Impl> ()) {}
Solver::~Solver () = default;

bool Solver::set (std::string_view option, int value) {
  REQUIRE (impl->stage == Stage::Options, "option set after add_var");
  Options &opts = impl->internal.opts;
  const std::span<const OptionInfo> table = option_table ();
  REQUIRE (std::any_of (
               table.begin (), table.end (),
               [option] (const OptionInfo &o) { return option == o.name; }),
           "unknown option");
  return opts.set (option, value);
}

void Solver::add_var (int var, Quant quant, bool decision,
                      int proof_number) {
  REQUIRE (impl->stage <= Stage::Variables, "add_var after add_original");
  REQUIRE (var > 0, "variable numbers are positive");
  REQUIRE (!impl->declared (var), "variable declared twice");
  REQUIRE (proof_number >= 0, "negative proof number");
  impl->stage = Stage::Variables;
  if ((size_t) var >= impl->internal_of.size ())
    impl->internal_of.resize ((size_t) var + 1, undeclared);
  impl->internal_of[(size_t) var] =
      impl->internal.add_var (quant, decision, proof_number);
  impl->user_of.push_back (var);
}

void Solver::add_original (Kind kind, std::span<const int> lits,
                           int proof_gate) {
  REQUIRE (impl->stage != Stage::Solved, "add_original after solve");
  REQUIRE (proof_gate >= 0, "negative proof gate");
  impl->stage = Stage::Constraints;
  impl->lits.clear ();
  for (int lit : lits)
    impl->lits.push_back (impl->translate (lit));
  impl->internal.add_original (kind, impl->lits, proof_gate);
}

void Solver::freeze (int var) {
  REQUIRE (impl->declared (var), "freeze of an undeclared variable");
}

void Solver::connect_tracer (std::unique_ptr<Tracer> tracer) {
  REQUIRE (impl->stage <= Stage::Variables,
           "connect_tracer after add_original");
  REQUIRE (tracer != nullptr, "no tracer");
  fatal ("proofs not implemented yet");
}

int Solver::solve () {
  REQUIRE (impl->stage != Stage::Solved, "solve called twice");
  impl->stage = Stage::Solved;
  switch (impl->internal.solve ()) {
  case Status::True:
    return 10;
  case Status::False:
    return 20;
  default:
    return 0;
  }
}

int Solver::val (int var) const {
  REQUIRE (impl->declared (var), "val of an undeclared variable");
  fatal ("certificates not implemented yet");
}

std::vector<int> Solver::certificate () const {
  fatal ("certificates not implemented yet");
}

void Solver::terminate () { impl->internal.terminated = true; }

void Solver::flush_proof () {}

void Solver::statistics () const {
  impl->internal.stats.print (stdout, process_time ());
}

} // namespace miniqu
