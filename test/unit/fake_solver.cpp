#include "fake_solver.hpp"

#include "miniqu.hpp"

using namespace miniqu;

// The members of the solver that the frontend uses record their arguments;
// the others are never called by it and only return a neutral value.

std::vector<FakeCall> &fake_calls () {
  static std::vector<FakeCall> calls;
  return calls;
}

bool fake_recording = true;

FakeCounts &fake_counts () {
  static FakeCounts counts;
  return counts;
}

void fake_reset () {
  fake_calls ().clear ();
  fake_counts () = FakeCounts ();
}

static void record (FakeCall &&call) {
  if (fake_recording)
    fake_calls ().push_back (std::move (call));
}

std::vector<std::string> fake_trace () {
  std::vector<std::string> lines;
  for (const FakeCall &call : fake_calls ()) {
    std::string line;
    if (call.type == FakeCall::Type::AddVar) {
      line = "var " + std::to_string (call.var) +
             (call.quant == Quant::Exists ? " e " : " a ") +
             (call.decision ? "d " : "- ") +
             std::to_string (call.proof_number);
    } else if (call.type == FakeCall::Type::AddOriginal) {
      line = std::string (call.kind == Kind::Clause ? "c " : "t ") +
             std::to_string (call.proof_gate) + ":";
      for (int lit : call.lits)
        line += " " + std::to_string (lit);
    } else
      continue;
    lines.push_back (line);
  }
  return lines;
}

struct Solver::Impl {};

Solver::Solver () : impl (new Impl) {}
Solver::~Solver () = default;

bool Solver::set (std::string_view option, int value) {
  FakeCall call{FakeCall::Type::Set};
  call.var = value;
  call.option = option;
  record (std::move (call));
  return true;
}

void Solver::add_var (int var, Quant quant, bool decision,
                      int proof_number) {
  FakeCall call{FakeCall::Type::AddVar};
  call.var = var;
  call.quant = quant;
  call.decision = decision;
  call.proof_number = proof_number;
  fake_counts ().vars++;
  record (std::move (call));
}

void Solver::add_original (Kind kind, std::span<const int> lits,
                           int proof_gate) {
  (kind == Kind::Clause ? fake_counts ().clauses : fake_counts ().cubes)++;
  fake_counts ().literals += lits.size ();
  if (!fake_recording)
    return;
  FakeCall call{FakeCall::Type::AddOriginal};
  call.kind = kind;
  call.lits.assign (lits.begin (), lits.end ());
  call.proof_gate = proof_gate;
  record (std::move (call));
}

void Solver::declare_complete_encoding () {
  record (FakeCall{FakeCall::Type::DeclareComplete});
}

void Solver::freeze (int var) {
  FakeCall call{FakeCall::Type::Freeze};
  call.var = var;
  record (std::move (call));
}

void Solver::connect_tracer (std::unique_ptr<Tracer>) {
  record (FakeCall{FakeCall::Type::ConnectTracer});
}

int Solver::solve () {
  record (FakeCall{FakeCall::Type::Solve});
  return 0;
}

int Solver::val (int) const { return 0; }
std::vector<int> Solver::certificate () const { return {}; }

void Solver::terminate () { record (FakeCall{FakeCall::Type::Terminate}); }
void Solver::flush_proof () {
  record (FakeCall{FakeCall::Type::FlushProof});
}
void Solver::statistics () const {
  record (FakeCall{FakeCall::Type::Statistics});
}
