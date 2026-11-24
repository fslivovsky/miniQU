// The public 'Solver' (ARCHITECTURE 3.5): checks the call order and the
// arguments of every call, translates user variables to internal ones and
// back, and forwards to 'Internal'.  It contains no solver logic.
//
// Internal variables are created in the order of the 'add_var' calls,
// which is prefix order, so the map is a renumbering and nothing else.
//
// 'Impl' owns the 'Proof' and through it the tracers.  The internal
// 'Checker' is connected with the first original constraint, when the
// prefix is complete: always with '--check', and by default in builds with
// assertions when no tracer was connected by the caller (ARCHITECTURE
// 8.1).  Long-distance steps (mode 2) are
// not expressible in any tracer's format, so no tracer may be connected
// there.

#include "checker.hpp"
#include "contract.hpp"
#include "internal.hpp"
#include "message.hpp"
#include "miniqu.hpp"
#include "proof.hpp"
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
  std::unique_ptr<Proof> proof;
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

  void connect (std::unique_ptr<Tracer> tracer) {
    if (!proof) {
      proof = std::make_unique<Proof> (&internal);
      internal.proof = proof.get ();
    }
    proof->connect (std::move (tracer));
  }

  void connect_checker () {
    const Options &opts = internal.opts;
    if (opts.mode == 2) {
      REQUIRE (!proof, "no tracer can follow mode 2");
      return;
    }
    if (opts.check || (assertions_enabled && !proof))
      connect (std::make_unique<Checker> (internal));
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
  impl->internal_of[(size_t) var] = impl->internal.add_var (
      quant, decision, proof_number ? proof_number : var);
  impl->user_of.push_back (var);
}

void Solver::add_original (Kind kind, std::span<const int> lits,
                           int proof_gate) {
  REQUIRE (impl->stage != Stage::Solved, "add_original after solve");
  REQUIRE (proof_gate >= 0, "negative proof gate");
  if (impl->stage != Stage::Constraints) {
    impl->stage = Stage::Constraints;
    impl->connect_checker ();
  }
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
  impl->connect (std::move (tracer));
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
  REQUIRE (impl->stage == Stage::Solved, "val before solve");
  REQUIRE (impl->declared (var), "val of an undeclared variable");
  return impl->internal.certificate_value (impl->internal_of[(size_t) var]);
}

std::vector<int> Solver::certificate () const {
  REQUIRE (impl->stage == Stage::Solved, "certificate before solve");
  std::vector<int> result;
  for (Lit l : impl->internal.certificate) {
    const int user = impl->user_of[var (l)];
    result.push_back (sign (l) ? -user : user);
  }
  return result;
}

void Solver::terminate () { impl->internal.terminated = true; }

void Solver::flush_proof () {
  if (impl->proof)
    impl->proof->flush ();
}

void Solver::statistics () const {
  impl->internal.print_tier_limits ();
  impl->internal.stats.print (stdout, process_time ());
  if (impl->internal.opts.profile)
    impl->internal.profiles.print (stdout);
}

} // namespace miniqu
