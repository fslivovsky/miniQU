// Mode-0 search: decisions, scores, analysis and learning, restarts,
// initial cubes, certificates, and whole runs through the 'Solver' API.

#include "internal_test.hpp"
#include "miniqu.hpp"
#include "random.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <algorithm>
#include <memory>
#include <string>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// Propagates and expects a conflict, which it returns.
static Ref conflict_of (Internal &internal) {
  const Ref conflict = internal.propagate ();
  CHECK (conflict != Ref::none);
  return conflict;
}

static void test_luby () {
  Internal internal;
  internal.opts.rfirst = 1;
  const std::vector<int64_t> luby = {1, 1, 2, 1, 1, 2, 4, 1,
                                     1, 2, 1, 1, 2, 4, 8, 1};
  for (size_t k = 0; k < luby.size (); k++)
    CHECK_EQ (internal.restart_interval ((int64_t) k), luby[k]);
  internal.opts.rfirst = 100;
  CHECK_EQ (internal.restart_interval (6), 400);
  internal.opts.luby = 0;
  internal.opts.rinc = 150;
  CHECK_EQ (internal.restart_interval (0), 100);
  CHECK_EQ (internal.restart_interval (1), 150);
  CHECK_EQ (internal.restart_interval (2), 225);
  // The stress configuration: restart after every conflict.
  internal.opts.rfirst = 1;
  internal.opts.rinc = 100;
  CHECK_EQ (internal.restart_interval (1000), 1);
}

static void test_glue () {
  Internal internal;
  declare (internal, "eeee");
  add (internal, Clause, {1});
  decide (internal, 2);
  decide (internal, 3);
  // Levels 0, 1, 2 and an unassigned literal, which does not count.
  CHECK_EQ (internal.compute_glue (lits ({-1, -2, 3, 4})), 3u);
  CHECK_EQ (internal.compute_glue (lits ({-2, 3})), 2u);
  CHECK_EQ (internal.compute_glue (lits ({4})), 0u);
}

// Universal 1 on level 1 is left of the asserting literal 2 and stays;
// the clause is learnt with glue 2 and asserts -2 on level 1.
static void test_learn_clause () {
  Internal internal;
  declare (internal, "aee");
  add (internal, Clause, {1, -2, 3});
  add (internal, Clause, {1, -2, -3});
  decide (internal, -1);
  decide (internal, 2);
  internal.analyze (conflict_of (internal));
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK_EQ (internal.stats.learned[0], 1);
  CHECK_EQ (internal.redundant[0].size (), 1u);
  const Ref learnt = internal.redundant[0][0];
  CHECK (stored (internal, learnt) == lits ({-2, 1}));
  CHECK_EQ (deref (internal.arena, learnt).glue (), 2u);
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.val (L (-2)) > 0 && internal.reason (1) == learnt);
  internal.check_invariants ();
}

// The dual cube: existential 1 stays, the cube asserts -2 on level 1.
static void test_learn_cube () {
  Internal internal;
  declare (internal, "eaa");
  add (internal, Cube, {-1, 2, -3});
  add (internal, Cube, {-1, 2, 3});
  decide (internal, -1);
  decide (internal, 2);
  internal.analyze (conflict_of (internal));
  CHECK_EQ (internal.stats.learned[1], 1);
  const Ref learnt = internal.redundant[1][0];
  CHECK (stored (internal, learnt) == lits ({2, -1}));
  CHECK (deref (internal.arena, learnt).kind () == Cube);
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.val (L (-2)) > 0 && internal.reason (1) == learnt);
  internal.check_invariants ();
}

// The asserting literal 2 is found while the universal 3 on its level is
// blocked; 4, to the right of 3, must then be resolved away (with its
// reason (-1 4)) so that 3 can be reduced: (-2 3 -4) becomes (-2 -1).
// Variable 2 is not a decision variable, as a gate.
static void test_resolve_right_of_blocked () {
  Internal internal;
  declare (internal, "eEae");
  add (internal, Clause, {-1, 4});
  add (internal, Clause, {2, 3, -4});
  add (internal, Clause, {-2, 3, -4});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, -3);
  internal.analyze (conflict_of (internal));
  const Ref learnt = internal.redundant[0][0];
  CHECK (stored (internal, learnt) == lits ({-2, -1}));
  CHECK_EQ (internal.decision_level (), 1);
  CHECK (internal.val (L (-2)) > 0);
  // Every variable of the resolvent was bumped once.
  for (Var v = 0; v < 4; v++)
    CHECK (internal.scores[v] == 1.0);
}

// Reduction leaves a unit: it is stored irredundant and the search
// backjumps to the root.
static void test_learn_unit () {
  Internal internal;
  declare (internal, "eae");
  add (internal, Clause, {-1, 2, 3});
  add (internal, Clause, {-1, 2, -3});
  decide (internal, 1);
  decide (internal, -2);
  internal.analyze (conflict_of (internal));
  CHECK (internal.redundant[0].empty ());
  CHECK (stored (internal, internal.irredundant[0].back ()) == lits ({-1}));
  CHECK_EQ (internal.decision_level (), 0);
  CHECK (internal.val (L (-1)) > 0);
  CHECK_EQ (internal.stats.learned[0], 1);
}

// Under the decision -1 the clauses force 2 and -2; resolving them leaves
// the universal 1, which reduction removes: the empty clause.
// The root-level literal -1 stays in the learnt clause (porting note 5),
// which counts level 0 in its glue and backjumps to the root.
static void test_root_literal_stays () {
  Internal internal;
  declare (internal, "eee");
  add (internal, Clause, {1});
  add (internal, Clause, {-1, -2, 3});
  add (internal, Clause, {-1, -2, -3});
  decide (internal, 2);
  internal.analyze (conflict_of (internal));
  const Ref learnt = internal.redundant[0][0];
  CHECK (stored (internal, learnt) == lits ({-2, -1}));
  CHECK_EQ (deref (internal.arena, learnt).glue (), 2u);
  CHECK_EQ (internal.decision_level (), 0);
  CHECK (internal.val (L (-2)) > 0 && internal.reason (1) == learnt);
}

static void test_empty () {
  Internal internal;
  declare (internal, "ae");
  add (internal, Clause, {1, 2});
  add (internal, Clause, {1, -2});
  CHECK (internal.solve () == Status::False);
  CHECK_EQ (internal.stats.conflicts, 1);
  CHECK_EQ (internal.stats.learned[0], 0);
  CHECK_EQ (internal.decision_level (), 0);
}

static void test_decide () {
  Internal internal;
  declare (internal, "eEa");
  CHECK (internal.decide ());
  // Initial phase false; the gate variable 2 is never decided.
  CHECK (internal.trail == lits ({-1}));
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({-1, -3}));
  CHECK (!internal.decide ());
  CHECK_EQ (internal.stats.decisions, 2);
  internal.backtrack (0);
  // Saved phases, and the higher score wins within a block.
  internal.phases[0] = 1;
  CHECK (internal.decide ());
  CHECK (internal.trail == lits ({1}));
  internal.backtrack (0);
  Internal scored;
  declare (scored, "ee");
  scored.bump_variable (1);
  CHECK (scored.decide ());
  CHECK (scored.trail == lits ({-2}));
}

static void test_seed () {
  for (int seed : {0, 7}) {
    Internal internal;
    internal.opts.seed = seed;
    declare (internal, "eaEe");
    Random random (seed ? seed : 1);
    for (Var v = 0; v < 4; v++)
      CHECK (internal.scores[v] == (seed ? random.drand () * 1e-5 : 0.0));
  }
}

// Clauses (-1 2) (2 3) (1 3) under 1, 2, -3: the hitting set {2, 1} loses
// the existential 2 by reduction, which is bumped.
static void test_initial_cube () {
  Internal internal;
  declare (internal, "aee");
  add (internal, Clause, {-1, 2});
  add (internal, Clause, {2, 3});
  add (internal, Clause, {1, 3});
  internal.init_model_cube ();
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, -3);
  CHECK (internal.propagate () == Ref::none);
  const Ref cube = internal.initial_cube ();
  CHECK (stored (internal, cube) == lits ({1}));
  CHECK (deref (internal.arena, cube).kind () == Cube);
  CHECK_EQ (internal.stats.modelcubes, 1);
  CHECK (internal.scores[1] == 1.0 && internal.scores[2] == 0.0);
  internal.analyze (cube);
  CHECK (stored (internal, internal.irredundant[1].back ()) == lits ({1}));
  CHECK (internal.val (L (-1)) > 0 && internal.decision_level () == 0);
}

// With 'complete' set, a complete assignment without conflict ends the
// search with status Unknown: no cube, no model-cube step, no conclusion.
// Without it the same formula is solved through the initial cube.
static void test_missing_cube (bool complete) {
  Solver solver;
  solver.add_var (1, Quant::Exists);
  solver.add_var (2, Quant::Exists);
  auto owned = std::make_unique<Recorder> ();
  const Recorder *recorder = owned.get ();
  solver.connect_tracer (std::move (owned));
  if (complete)
    solver.declare_complete_encoding ();
  solver.add_original (Clause, std::vector<int>{1, 2});
  const int result = solver.solve ();
  const Internal &internal = internal_of (solver);
  CHECK_EQ (internal.stats.modelcubes, 1);
  if (complete) {
    CHECK_EQ (result, 0);
    CHECK (internal.status == Status::Unknown);
    CHECK (internal.irredundant[1].empty ());
    for (const std::string &step : recorder->steps)
      CHECK (step[0] == 'o');
  } else {
    CHECK_EQ (result, 10);
    CHECK (recorder->steps.back ()[0] == 'e');
    CHECK (std::any_of (recorder->steps.begin (), recorder->steps.end (),
                        [] (const std::string &s) { return s[0] == 'm'; }));
  }
}

// Formulas over 'Solver': 'Qx Qy. (x | y) & (-x | -y)'.
static int solve_xor (Quant outer, Quant inner, std::vector<int> &cert) {
  Solver solver;
  solver.add_var (1, outer);
  solver.add_var (2, inner);
  solver.add_original (Clause, std::vector<int>{1, 2});
  solver.add_original (Clause, std::vector<int>{-1, -2});
  const int result = solver.solve ();
  cert = solver.certificate ();
  CHECK_EQ (solver.val (2), outer != inner ? 0 : cert[1] > 0 ? 1 : -1);
  CHECK (solver.val (1) == (cert[0] > 0 ? 1 : -1));
  return result;
}

static void test_solver () {
  std::vector<int> cert;
  CHECK_EQ (solve_xor (Quant::Forall, Quant::Exists, cert), 10);
  CHECK_EQ (solve_xor (Quant::Exists, Quant::Forall, cert), 20);
  CHECK_EQ (cert.size (), 1u);
  CHECK_EQ (solve_xor (Quant::Exists, Quant::Exists, cert), 10);
  // The certificate block holds both variables, which satisfy the clauses.
  CHECK_EQ (cert.size (), 2u);
  CHECK ((cert[0] > 0) != (cert[1] > 0));
}

int main () {
  test_luby ();
  test_glue ();
  test_learn_clause ();
  test_learn_cube ();
  test_resolve_right_of_blocked ();
  test_learn_unit ();
  test_root_literal_stays ();
  test_empty ();
  test_decide ();
  test_seed ();
  test_initial_cube ();
  test_missing_cube (false);
  test_missing_cube (true);
  test_solver ();
  return test_result ();
}
