// Restarts on glue averages and trail reuse (restart.cpp).  The luby and
// geometric intervals of mode 0 are tested in search.cpp.

#include "internal_test.hpp"
#include "test.hpp"

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

static Internal &ema_mode (Internal &internal) {
  internal.opts.restartmode = 1;
  internal.opts.restartint = 3;
  internal.opts.restartmargin = 10;
  internal.opts.emagluefast = 2;
  internal.opts.emaglueslow = 1000;
  internal.init_restart ();
  return internal;
}

static void learn_glues (Internal &internal, Kind kind, uint32_t glue,
                         int times) {
  for (int i = 0; i < times; i++)
    internal.update_averages (kind, glue);
}

static void test_ema_restarts () {
  Internal internal;
  declare (internal, "ee");
  ema_mode (internal);
  CHECK_EQ (internal.lim.restart, 3);

  // Nothing learnt: both averages are 0, which is not above the margin.
  internal.stats.conflicts = 3;
  CHECK (!internal.restarting ());

  // Constant glues: the fast average does not exceed the slow one.
  learn_glues (internal, Clause, 4, 50);
  CHECK (!internal.restarting ());

  // A jump in the glue lifts the fast average (window 2) above the slow.
  learn_glues (internal, Clause, 7, 1);
  CHECK (internal.restarting ());

  // The margin: 10% above the slow average is not enough when 100% is
  // asked.
  internal.opts.restartmargin = 100;
  CHECK (!internal.restarting ());
  internal.opts.restartmargin = 10;

  // Only the kind learnt last counts: cube glues are flat.
  learn_glues (internal, Cube, 3, 50);
  CHECK (!internal.restarting ());
  learn_glues (internal, Clause, 40, 1);
  CHECK (internal.restarting ());

  // restartint is respected, also by the restart itself.
  internal.stats.conflicts = 2;
  CHECK (!internal.restarting ());
  internal.stats.conflicts = 7;
  internal.restart ();
  CHECK_EQ (internal.stats.restarts, 1);
  CHECK_EQ (internal.lim.restart, 10);
}

static void test_mode_0_ignores_averages () {
  Internal internal;
  declare (internal, "ee");
  internal.opts.rfirst = 5;
  internal.init_restart ();
  CHECK_EQ (internal.lim.restart, 5);
  learn_glues (internal, Clause, 4, 10);
  learn_glues (internal, Clause, 40, 1);
  internal.stats.conflicts = 4;
  CHECK (!internal.restarting ());
  internal.stats.conflicts = 5;
  CHECK (internal.restarting ());
  internal.restart ();
  CHECK_EQ (internal.lim.restart, 10);
}

// Decisions 1, 2, 3 (variables 0, 1, 2) on levels 1, 2, 3; variable 3 is
// the only unassigned one.  Assigned variables stay in the heap, so the
// candidate is found past them without popping anything.
static void test_reuse_prefix () {
  Internal internal;
  declare (internal, "eeee");
  for (int i = 0; i < 3; i++)
    internal.bump_variable (0);
  internal.bump_variable (3);
  decide (internal, 1);
  decide (internal, 2);
  decide (internal, 3);
  const size_t size = internal.heaps[0].size ();

  // Level 1 beats the candidate (3 > 1), level 2 does not (0 < 1).
  CHECK_EQ (internal.reuse_level (), 1);
  CHECK_EQ (internal.heaps[0].size (), size);

  // A tie counts as not lower.
  internal.bump_variable (1);
  CHECK_EQ (internal.reuse_level (), 2);
  internal.bump_variable (2);
  CHECK_EQ (internal.reuse_level (), 3);

  internal.opts.reusetrail = 0;
  CHECK_EQ (internal.reuse_level (), 0);
  internal.opts.reusetrail = 1;

  internal.restart ();
  CHECK_EQ (internal.stats.reused, 1);
  CHECK_EQ (internal.decision_level (), 3);
  CHECK_EQ (internal.heaps[0].size (), size);

  // With every variable assigned there is no candidate: all is kept.
  decide (internal, 4);
  CHECK_EQ (internal.reuse_level (), 4);
}

// Each block has its own heap: the candidate of a decision is a variable
// of its block, whatever the other blocks hold.
static void test_reuse_blocks () {
  Internal internal;
  declare (internal, "eaae");
  internal.bump_variable (3);
  internal.bump_variable (3);
  internal.bump_variable (2);
  decide (internal, 1);
  decide (internal, 2);
  // Variable 3 (block 2) is unassigned but 2 (block 1) has the same block
  // as the decision of level 2 and a higher score.
  CHECK_EQ (internal.reuse_level (), 1);
  decide (internal, 3);
  CHECK_EQ (internal.reuse_level (), 3);
}

static void test_reuse_dl () {
  Internal internal;
  internal.opts.dl = 1;
  declare (internal, "eee");
  internal.bump_variable (0);
  internal.bump_variable (2);
  internal.bump_variable (2);
  decide (internal, 1);
  decide (internal, 2);
  // One heap over all blocks: variable 2 (score 2) outscores the
  // decision of level 1 (score 1), so nothing is kept.
  CHECK_EQ (internal.reuse_level (), 0);
  decide (internal, 3);
  CHECK_EQ (internal.reuse_level (), 3);
}

// A due dependency reset needs level 0, both schedules.
static void test_reuse_reset () {
  Internal internal;
  internal.opts.dl = 1;
  declare (internal, "eee");
  decide (internal, 1);
  decide (internal, 2);
  CHECK_EQ (internal.reuse_level (), 2);
  internal.stats.learned[0] = 1;
  CHECK (internal.resetting_dependencies () == false);
  internal.opts.depreset = 1;
  internal.stats.restarts = 0;
  CHECK (internal.resetting_dependencies ());
  CHECK_EQ (internal.reuse_level (), 0);

  internal.opts.depreset = 20;
  ema_mode (internal);
  internal.opts.depresetint = 10;
  internal.init_restart ();
  internal.stats.conflicts = 9;
  CHECK (!internal.resetting_dependencies ());
  CHECK_EQ (internal.reuse_level (), 2);
  internal.stats.conflicts = 10;
  CHECK (internal.resetting_dependencies ());
  CHECK_EQ (internal.reuse_level (), 0);
  internal.backtrack (0);
  internal.reset_dependencies ();
  CHECK_EQ (internal.lim.depreset, 20);
  CHECK (!internal.resetting_dependencies ());
}

int main () {
  test_ema_restarts ();
  test_mode_0_ignores_averages ();
  test_reuse_prefix ();
  test_reuse_blocks ();
  test_reuse_dl ();
  test_reuse_reset ();
  return test_result ();
}
