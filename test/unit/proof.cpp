// Proof logging (proof.cpp and the logging points of ARCHITECTURE 8.2):
// which steps the solver emits, with which ids, and that the internal
// checker accepts them; 'Proof::strengthen'.

#include "proof.hpp"
#include "checker.hpp"
#include "child.hpp"
#include "internal_test.hpp"
#include "miniqu.hpp"
#include "test.hpp"

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// Records every step as one line: "o ID KIND GATE: LITS", "a ID KIND: LITS
// : CHAIN", "d ID", "m ID: LITS", "e KIND ID" (conclude).
class Recorder : public Tracer {
  static std::string kind (Kind k) { return k == Clause ? "c" : "t"; }
  template <class T> static std::string list (std::span<const T> xs) {
    std::string s;
    for (T x : xs)
      s += " " + std::to_string (x);
    return s;
  }

public:
  std::vector<std::string> steps;

  void add_original (uint64_t id, Kind k, int gate,
                     std::span<const int> lits) override {
    steps.push_back ("o " + std::to_string (id) + " " + kind (k) + " " +
                     std::to_string (gate) + ":" + list (lits));
  }
  void add_derived (uint64_t id, Kind k, std::span<const int> lits,
                    std::span<const uint64_t> chain) override {
    steps.push_back ("a " + std::to_string (id) + " " + kind (k) + ":" +
                     list (lits) + " :" + list (chain));
  }
  void delete_constraint (uint64_t id, Kind,
                          std::span<const int>) override {
    steps.push_back ("d " + std::to_string (id));
  }
  void add_model_cube (uint64_t id, std::span<const int> lits) override {
    steps.push_back ("m " + std::to_string (id) + ":" + list (lits));
  }
  void conclude (Kind k, uint64_t id) override {
    steps.push_back ("e " + kind (k) + " " + std::to_string (id));
  }
};

// An 'Internal' with a recorder and the checker connected.
struct Logged {
  Internal internal;
  Proof proof{&internal};
  Recorder *recorder;

  explicit Logged (const char *prefix) {
    declare (internal, prefix);
    auto owned = std::make_unique<Recorder> ();
    recorder = owned.get ();
    proof.connect (std::move (owned));
    proof.connect (std::make_unique<Checker> (internal));
    internal.proof = &proof;
  }
};

// Variables 1 e, 2 a, 3 e.  Used with and without a proof: the ids must be
// the same.
static void add_originals (Internal &internal) {
  add (internal, Clause, {1, -1}); // tautology: no step, no id
  add (internal, Clause, {2, 1, 2});
  add (internal, Cube, {3, 2});
  add (internal, Clause, {-1, 3});
  add (internal, Clause, {-1});
}

static void test_originals () {
  Logged l ("eae");
  add_originals (l.internal);
  // (1 2) loses the universal 2 and (2 3) the existential 3: each
  // reduction is derived from the original alone, which is then deleted.
  // The units (1) and (-1) resolve to the empty clause, the new one first.
  const std::vector<std::string> expected = {
      "o 1 c 0: 1 2", "a 2 c: 1 : 1", "d 1",           "o 3 t 0: 2 3",
      "a 4 t: 2 : 3", "d 3",          "o 5 c 0: -1 3", "o 6 c 0: -1",
      "a 7 c: : 6 2", "e c 7"};
  CHECK (l.recorder->steps == expected);
  CHECK (l.internal.status == Status::False);

  Internal unlogged;
  declare (unlogged, "eae");
  add_originals (unlogged);
  CHECK_EQ (unlogged.next_id, l.internal.next_id);
}

// 'strengthen' derives the shorter constraint under a fresh id and deletes
// the old one; the checker sees both.
static void test_strengthen () {
  Logged l ("ee");
  const Ref ref = add (l.internal, Clause, {1, 2});
  add (l.internal, Clause, {-2});
  Constraint &c = deref (l.internal.arena, ref);
  const std::vector<Lit> shorter = lits ({1});
  const uint64_t chain[] = {1, 2};
  l.proof.strengthen (c, shorter, chain);
  CHECK_EQ (c.id (), 3u);
  CHECK_EQ (l.internal.next_id, 4u);
  const std::vector<std::string> expected = {"o 1 c 0: 1 2", "o 2 c 0: -2",
                                             "a 3 c: 1 : 1 2", "d 1"};
  CHECK (l.recorder->steps == expected);
  CHECK_EQ (l.internal.stats.checked, 1);
  // The old id is gone, the new one can be used.
  const uint64_t old_id[] = {1}, new_id[] = {3};
  CHECK (
      dies_with ([&] { l.proof.add_derived (4, Clause, shorter, old_id); },
                 "id 1 is not live"));
  l.proof.add_derived (4, Clause, shorter, new_id);
  CHECK_EQ (l.internal.stats.checked, 2);
}

// A formula with learning, through the API: the steps end with the empty
// constraint, and the ids are those of a run without a proof.
static int solve (const std::vector<std::vector<int>> &clauses,
                  std::unique_ptr<Recorder> recorder, Solver &solver) {
  const bool logged = recorder != nullptr;
  if (logged)
    solver.set ("check", 1);
  solver.add_var (1, Quant::Exists);
  solver.add_var (2, Quant::Forall);
  solver.add_var (3, Quant::Exists);
  solver.add_var (4, Quant::Exists);
  if (logged)
    solver.connect_tracer (std::move (recorder));
  for (const auto &clause : clauses)
    solver.add_original (Clause, clause);
  return solver.solve ();
}

static void test_search () {
  // False: all eight clauses over 1, 3, 4, two of them weakened by the
  // universal 2, which the adversary sets against the choice for 1.
  const std::vector<std::vector<int>> unsat = {
      {1, 3, 4},  {1, 3, -4},  {1, -3, 4, 2}, {1, -3, -4},
      {-1, 3, 4}, {-1, 3, -4}, {-1, -3, 4},   {-1, -3, -4, -2}};
  // True (the regression prenex-pair); there is no cube encoding, so the
  // cubes come from models.
  const std::vector<std::vector<int>> sat = {
      {-1, 2, 3}, {-1, -2, -3}, {1, 2, -3}, {1, -2, 3}};
  for (const auto *clauses : {&unsat, &sat}) {
    const bool expect_false = clauses == &unsat;
    Solver logged, plain;
    auto owned = std::make_unique<Recorder> ();
    const Recorder *recorder = owned.get ();
    const int result = solve (*clauses, std::move (owned), logged);
    CHECK_EQ (result, expect_false ? 20 : 10);
    CHECK_EQ (solve (*clauses, nullptr, plain), result);
    CHECK_EQ (internal_of (logged).next_id, internal_of (plain).next_id);
    CHECK (internal_of (logged).stats.checked > 0);
    CHECK (internal_of (logged).stats.learned[0] +
               internal_of (logged).stats.learned[1] >
           0);
    const std::vector<std::string> &steps = recorder->steps;
    CHECK (steps.back () ==
           (expect_false ? "e c " : "e t ") +
               std::to_string (internal_of (logged).next_id - 1));
    if (!expect_false)
      CHECK (
          std::any_of (steps.begin (), steps.end (),
                       [] (const std::string &s) { return s[0] == 'm'; }));
  }
}

int main () {
  test_originals ();
  test_strengthen ();
  test_search ();
  return test_result ();
}
