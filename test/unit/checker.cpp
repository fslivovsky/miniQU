// The internal proof checker (checker.cpp): correct steps are accepted,
// corrupted ones end the run with the offending step.  Literals are proof
// numbers; 'declare' gives variable i the proof number i.

#include "checker.hpp"
#include "child.hpp"
#include "internal_test.hpp"
#include "test.hpp"

#include <cstdint>
#include <initializer_list>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// Variables 1 e, 2 a, 3 e, 4 a: the clauses of 'start' are
//   1: (1 3)   2: (-3 2)   3: (1 2)   4: (-1 3)   5: (-1 -3)
// and the cube 6: (2 4).
struct Fixture {
  Internal internal;
  Checker checker;

  Fixture () : checker ((declare (internal, "eaea"), internal)) {
    original (1, Clause, {1, 3});
    original (2, Clause, {-3, 2});
    original (3, Clause, {1, 2});
    original (4, Clause, {-1, 3});
    original (5, Clause, {-1, -3});
    original (6, Cube, {2, 4});
  }

  void original (uint64_t id, Kind kind, std::initializer_list<int> lits) {
    checker.add_original (id, kind, 0, std::vector<int> (lits));
  }
  void derive (uint64_t id, Kind kind, std::initializer_list<int> lits,
               std::initializer_list<uint64_t> chain) {
    checker.add_derived (id, kind, std::vector<int> (lits),
                         std::vector<uint64_t> (chain));
  }
};

static void test_accepted () {
  Fixture f;
  // (1 3) and (-3 2) give (1 2); the universal 2 is right of the
  // existential 1 and goes.  Any superset of the result is fine.
  f.derive (10, Clause, {1}, {1, 2});
  f.derive (11, Clause, {1, 2}, {1, 2});
  // A premise without a clashing literal leaves the resolvent alone.
  f.derive (12, Clause, {1, 3}, {1, 3});
  // (1 2) reduces to (1) only before it meets (-1 3): with the
  // existential 3 the universal 2 stays.  Only the variant with reduction
  // after every step derives (3).
  f.derive (13, Clause, {3}, {3, 4});
  // Down to the empty clause: (1) and (-1 -3) give (-3), then (-1 3) and
  // (1) resolve it away.
  f.derive (14, Clause, {-3}, {10, 5});
  f.derive (15, Clause, {}, {14, 4, 10});
  f.checker.conclude (Clause, 15);
  f.checker.delete_constraint (11, Clause, std::vector<int>{2, 1});
  f.derive (11, Clause, {1}, {1, 2}); // a deleted id may be used again
  // A cube from a model, then used as a premise; existential 3 is
  // reduced away right of every universal.
  f.checker.add_model_cube (20, std::vector<int>{-2, 3});
  f.derive (21, Cube, {-2}, {20});
  CHECK_EQ (f.internal.stats.checked, 8);
}

template <class F> static void rejected (F step, const char *message) {
  CHECK (dies_with (
      [&] {
        Fixture f;
        step (f);
      },
      message));
}

static void test_rejected () {
  rejected (
      [] (Fixture &f) {
        f.derive (10, Clause, {3}, {1, 2});
      },
      "literal 1 of the resolvent is missing");
  rejected (
      [] (Fixture &f) {
        f.derive (10, Clause, {1}, {1, 99});
      },
      "id 99 is not live");
  rejected (
      [] (Fixture &f) {
        f.checker.delete_constraint (2, Clause, std::vector<int>{-3, 2});
        f.derive (10, Clause, {1}, {1, 2});
      },
      "id 2 is not live");
  rejected (
      [] (Fixture &f) {
        f.derive (10, Clause, {1}, {1, 6});
      },
      "id 6 has the other kind");
  // (1 3) and (-1 -3) clash twice: the resolvent would be tautological.
  rejected (
      [] (Fixture &f) {
        f.derive (10, Clause, {}, {1, 5});
      },
      "premise 5 clashes in more than one literal");
  rejected (
      [] (Fixture &f) {
        f.derive (3, Clause, {1, 2}, {3});
      },
      "id 3 is in use");
  rejected ([] (Fixture &f) { f.derive (10, Clause, {1}, {}); },
            "no premises");
  rejected (
      [] (Fixture &f) {
        f.derive (10, Clause, {1, -1}, {1, 2});
      },
      "complementary literals");
  rejected ([] (Fixture &f) { f.original (10, Clause, {5}); },
            "literal 5 has no variable in clauses");
  rejected (
      [] (Fixture &f) {
        f.checker.delete_constraint (1, Clause, std::vector<int>{1});
      },
      "deleted literals differ");
  rejected (
      [] (Fixture &f) {
        f.checker.delete_constraint (6, Clause, std::vector<int>{2, 4});
      },
      "deleted id has the other kind");
  rejected ([] (Fixture &f) { f.checker.conclude (Clause, 1); },
            "not a live empty constraint");
  // The offending step is printed.
  rejected (
      [] (Fixture &f) {
        f.derive (10, Clause, {3}, {1, 2});
      },
      "step: derived 10 c 3 0 1 2 0");
}

// A gate number has an existential variable in clauses and a universal one
// in cubes, each at its own place in the prefix: here the universal one
// right of variable 1, the existential one left of variable 3.
static void test_gate_variables () {
  Internal internal;
  internal.add_var (Quant::Exists, true, 1);
  internal.add_var (Quant::Forall, false, 2);
  internal.add_var (Quant::Exists, false, 2);
  internal.add_var (Quant::Forall, true, 3);
  Checker checker (internal);
  checker.add_original (1, Clause, 0, std::vector<int>{2, 3});
  checker.add_original (2, Cube, 0, std::vector<int>{1, 2});
  checker.add_derived (3, Clause, std::vector<int>{2},
                       std::vector<uint64_t>{1});
  checker.add_derived (4, Cube, std::vector<int>{1, 2},
                       std::vector<uint64_t>{2});
  CHECK_EQ (internal.stats.checked, 2);
  // With the two variables of gate 2 swapped both would reduce to the
  // empty constraint.
  CHECK (dies_with (
      [&] {
        checker.add_derived (5, Clause, {}, std::vector<uint64_t>{1});
      },
      "literal 2 of the resolvent is missing"));
  CHECK (dies_with (
      [&] { checker.add_derived (5, Cube, {}, std::vector<uint64_t>{2}); },
      "literal 1 of the resolvent is missing"));
}

int main () {
  test_accepted ();
  test_rejected ();
  test_gate_variables ();
  return test_result ();
}
