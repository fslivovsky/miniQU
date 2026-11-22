#include "encode.hpp"
#include "fake_solver.hpp"
#include "frontend_test.hpp"
#include "message.hpp"
#include "test.hpp"

#include <string>
#include <vector>

using namespace miniqu;

using Trace = std::vector<std::string>;

static Trace encoded (const std::string &text, bool early_tseitin) {
  const Circuit circuit = parse_qcir (write_file ("input.qcir", text));
  fake_reset ();
  Solver solver;
  encode (circuit, solver, early_tseitin);
  return fake_trace ();
}

// Variables of the gate with proof number p, for n quantified variables:
// existential n + 2 (p - n) - 1, universal n + 2 (p - n).

static const char *plain = "exists(a)\n"
                           "forall(u)\n"
                           "exists(b)\n"
                           "output(g3)\n"
                           "g1 = and(a, u)\n"
                           "g2 = or(g1, -b)\n"
                           "g3 = and(g2, a)\n";

static void test_early () {
  // g1 depends on u, so its variables follow the block {u}, the universal
  // one first; g2 and g3 follow {b}, the existential ones first.  All gates
  // occur positively.
  CHECK (encoded (plain, true) ==
         (Trace{
             "var 1 e d 1", "var 2 a d 2", "var 5 a - 4", "var 4 e - 4",
             "var 3 e d 3", "var 6 e - 5", "var 8 e - 6", "var 7 a - 5",
             "var 9 a - 6", "c 4: -4 1",   "c 4: -4 2",   "c 5: -6 4 -3",
             "c 6: -8 6",   "c 6: -8 1",   "c 0: 8",      "t 4: -5 1 2",
             "t 5: -7 5",   "t 5: -7 -3",  "t 6: -9 7 1", "t 0: 9",
         }));
}

static void test_late () {
  CHECK (encoded (plain, false) ==
         (Trace{
             "var 1 e d 1", "var 2 a d 2", "var 3 e d 3", "var 4 e - 4",
             "var 6 e - 5", "var 8 e - 6", "var 5 a - 4", "var 7 a - 5",
             "var 9 a - 6", "c 4: -4 1",   "c 4: -4 2",   "c 5: -6 4 -3",
             "c 6: -8 6",   "c 6: -8 1",   "c 0: 8",      "t 4: -5 1 2",
             "t 5: -7 5",   "t 5: -7 -3",  "t 6: -9 7 1", "t 0: 9",
         }));
}

static void test_first_block_universal () {
  // g1 depends on nothing and comes before the first block, the existential
  // variable first because the first block is universal; g2 depends on u.
  const char *text = "forall(u)\n"
                     "exists(e)\n"
                     "output(g2)\n"
                     "g1 = and()\n"
                     "g2 = or(g1, u)\n";
  CHECK (encoded (text, true) == (Trace{
                                     "var 3 e - 3",
                                     "var 4 a - 3",
                                     "var 1 a d 1",
                                     "var 6 a - 4",
                                     "var 5 e - 4",
                                     "var 2 e d 2",
                                     // An and without inputs needs no
                                     // clause for positive polarity.
                                     "c 4: -5 3 1",
                                     "c 0: 5",
                                     "t 3: -4",
                                     "t 4: -6 4",
                                     "t 4: -6 1",
                                     "t 0: 6",
                                 }));
  CHECK (encoded (text, false) ==
         (Trace{"var 1 a d 1", "var 2 e d 2", "var 3 e - 3", "var 5 e - 4",
                "var 4 a - 3", "var 6 a - 4", "c 4: -5 3 1", "c 0: 5",
                "t 3: -4", "t 4: -6 4", "t 4: -6 1", "t 0: 6"}));
}

static void test_input_output () {
  // The output is an input literal; the unused gate keeps its variables.
  // The free block merges with the existential one.
  const char *text = "free(f)\n"
                     "exists(a)\n"
                     "forall(u)\n"
                     "output(-u)\n"
                     "g = and(f, a)\n";
  CHECK (encoded (text, true) ==
         (Trace{"var 1 e d 1", "var 2 e d 2", "var 4 e - 4", "var 5 a - 4",
                "var 3 a d 3", "c 0: -3", "t 0: -3"}));
}

static void test_no_variables () {
  // No block at all: gates without dependencies, universal group first.  An
  // or without inputs gives the clause (-g) and, for positive polarity, no
  // cube.
  CHECK (
      encoded ("output(g)\ng = or()\n", true) ==
      (Trace{"var 2 a - 1", "var 1 e - 1", "c 1: -1", "c 0: 1", "t 0: 2"}));
}

static void test_raw_constraints () {
  // Duplicates and complementary literals are passed on, the solver removes
  // them.  g occurs in both polarities.
  const char *text = "exists(a)\n"
                     "output(h)\n"
                     "g = and(a, -a, a)\n"
                     "h = or(g, -g)\n";
  CHECK (encoded (text, true) ==
         (Trace{"var 1 e d 1", "var 2 e - 2", "var 4 e - 3", "var 3 a - 2",
                "var 5 a - 3", "c 2: -2 1", "c 2: -2 -1", "c 2: -2 1",
                "c 2: 2 -1 1 -1", "c 3: -4 2 -2", "c 0: 4", "t 2: 3 -1",
                "t 2: 3 1", "t 2: 3 -1", "t 2: -3 1 -1 1", "t 3: -5 3",
                "t 3: -5 -3", "t 0: 5"}));
}

static void test_qdimacs () {
  const Qdimacs q = parse_qdimacs (write_file (
      "a.qdimacs", "p cnf 4 2\na 1 0\ne 2 0\n1 -2 4 0\n-1 2 0\n"));
  fake_reset ();
  Solver solver;
  encode_qdimacs (q, solver);
  CHECK (fake_trace () ==
         (Trace{"var 4 e d 0", "var 1 a d 0", "var 2 e d 0", "c 0: 1 -2 4",
                "c 0: -1 2"}));
}

int main () {
  set_verbosity (0);
  test_early ();
  test_late ();
  test_first_block_universal ();
  test_input_output ();
  test_no_variables ();
  test_raw_constraints ();
  test_qdimacs ();
  return test_result ();
}
