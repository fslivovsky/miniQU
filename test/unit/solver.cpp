// The public 'Solver': translation of user variables and the contracts of
// the call order and the arguments (solver.cpp).

#include "child.hpp"
#include "internal.hpp"
#include "miniqu.hpp"
#include "test.hpp"

#include <vector>

using namespace miniqu;

static void test_translation () {
  Solver solver;
  CHECK (solver.set ("mode", 1));
  CHECK (!solver.set ("mode", 3));
  // User numbers need not be dense or increasing; internal variables are
  // numbered in the order of the calls.
  solver.add_var (7, Quant::Exists);
  solver.add_var (3, Quant::Forall);
  solver.add_var (12, Quant::Exists, false, 5);
  const Internal &internal = internal_of (solver);
  CHECK_EQ (internal.opts.mode, 1);
  CHECK_EQ (internal.prefix.size (), 3u);
  CHECK (internal.prefix.quant (1) == Quant::Forall);
  CHECK (!internal.prefix.vars[2].decision);
  CHECK_EQ (internal.prefix.vars[2].proof, 5);
  const std::vector<int> clause = {-12, 3, 7};
  solver.add_original (Kind::Clause, clause);
  const Constraint &c = deref (internal.arena, internal.irredundant[0][0]);
  CHECK_EQ (c.size (), 3u);
  CHECK (c[0] == mk_lit (0) && c[1] == mk_lit (1) &&
         c[2] == mk_lit (2, true));
  CHECK_EQ (solver.solve (), 0);
}

static void test_decided () {
  Solver solver;
  solver.add_var (1, Quant::Exists);
  const std::vector<int> unit = {1}, negated = {-1};
  solver.add_original (Kind::Clause, unit);
  solver.add_original (Kind::Clause, negated);
  CHECK_EQ (solver.solve (), 20);

  Solver other;
  other.add_var (1, Quant::Exists);
  other.add_original (Kind::Cube, unit);
  CHECK_EQ (other.solve (), 10);
}

static void test_contracts () {
  const std::vector<int> one = {1}, two = {2}, zero = {0};
  CHECK (aborts_with (
      [] {
        Solver s;
        s.add_var (1, Quant::Exists);
        (void) s.set ("mode", 1);
      },
      "option set after add_var"));
  CHECK (aborts_with ([] { (void) Solver ().set ("nosuchoption", 1); },
                      "unknown option"));
  CHECK (aborts_with (
      [&] {
        Solver s;
        s.add_var (1, Quant::Exists);
        s.add_original (Kind::Clause, one);
        s.add_var (2, Quant::Exists);
      },
      "add_var after add_original"));
  CHECK (aborts_with (
      [] {
        Solver s;
        s.add_var (1, Quant::Exists);
        s.add_var (1, Quant::Forall);
      },
      "variable declared twice"));
  CHECK (aborts_with ([] { Solver ().add_var (0, Quant::Exists); },
                      "variable numbers are positive"));
  CHECK (aborts_with (
      [&] {
        Solver s;
        s.add_var (1, Quant::Exists);
        s.add_original (Kind::Cube, two);
      },
      "literal of an undeclared variable"));
  CHECK (aborts_with (
      [&] {
        Solver s;
        s.add_var (1, Quant::Exists);
        s.add_original (Kind::Clause, zero);
      },
      "invalid literal"));
  CHECK (aborts_with (
      [&] {
        Solver s;
        (void) s.solve ();
        (void) s.solve ();
      },
      "solve called twice"));
  CHECK (aborts_with (
      [&] {
        Solver s;
        s.add_var (1, Quant::Exists);
        (void) s.solve ();
        s.add_original (Kind::Clause, one);
      },
      "add_original after solve"));
  CHECK (aborts_with ([] { Solver ().freeze (1); },
                      "freeze of an undeclared variable"));
}

int main () {
  test_translation ();
  test_decided ();
  test_contracts ();
  return test_result ();
}
