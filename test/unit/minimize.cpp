// Learnt-constraint minimisation (minimize.cpp), called by 'learn' after
// the mode-0 analysis.  Each case states which of the ccminmodes remove
// which literal; the decision literal -1 is never redundant.

#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <algorithm>
#include <memory>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause;

// The learnt clause, sorted.
static std::vector<Lit> learnt (const Internal &internal) {
  const std::vector<Ref> &list = internal.redundant[0];
  CHECK (!list.empty ());
  std::vector<Lit> result = stored (internal, list.back ());
  std::sort (result.begin (), result.end ());
  return result;
}

// 'exists 1 2 3 4' with (-1 2), (-3 4) and (-1 -2 -3 -4): the decision 1
// forces 2, the decision 3 forces 4 and the last clause conflicts.  The
// analysis learns (-1 -2 -3); the reason of 2 contains only -1, which is
// in the clause, so every mode removes -2.
static void test_basic (int mode) {
  Internal internal;
  internal.opts.ccminmode = mode;
  declare (internal, "eeee");
  add (internal, Clause, {-1, 2});
  add (internal, Clause, {-3, 4});
  add (internal, Clause, {-1, -2, -3, -4});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, 3);
  internal.analyze (internal.propagate ());
  CHECK (learnt (internal) == lits ({-1, -3}));
  CHECK_EQ (internal.stats.minimized, 1);
  internal.check_invariants ();
}

// 'exists 1 2 3 4 5' with (-1 2), (-2 3), (-4 5) and (-1 -3 -4 -5): 1
// forces 2 and 3, the decision 4 forces 5 and the last clause conflicts;
// the analysis learns (-1 -3 -4).  The
// reason of 3 brings in -2, which is not in the clause: basic minimisation
// keeps -3, the deep modes follow the reason of 2 back to -1 and remove it.
static void test_deep (int mode) {
  Internal internal;
  internal.opts.ccminmode = mode;
  declare (internal, "eeeee");
  add (internal, Clause, {-1, 2});
  add (internal, Clause, {-2, 3});
  add (internal, Clause, {-4, 5});
  add (internal, Clause, {-1, -3, -4, -5});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, 4);
  internal.analyze (internal.propagate ());
  if (mode == 1) {
    CHECK (learnt (internal) == lits ({-1, -3, -4}));
    CHECK_EQ (internal.stats.minimized, 0);
  } else {
    CHECK (learnt (internal) == lits ({-1, -4}));
    CHECK_EQ (internal.stats.minimized, 1);
  }
  internal.check_invariants ();
}

// 'exists 1 2 forall 3 exists 4 5' with (-1 3 4), (-2 5) and
// (-1 -2 -4 -5): the decisions 1 and -3 force 4, the decision 2 forces 5
// and the last clause conflicts; the analysis learns (-1 -2 -4).  Removing
// -4 brings in the universal 3, which is not in the clause: modes 1 and 2
// keep -4, mode 3 removes it because 3 is right of every primary literal
// left (-1 and -2), so reduction would drop it from the resolvent.
static void test_with_reduction (int mode) {
  Internal internal;
  internal.opts.ccminmode = mode;
  declare (internal, "eeaee");
  add (internal, Clause, {-1, 3, 4});
  add (internal, Clause, {-2, 5});
  add (internal, Clause, {-1, -2, -4, -5});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, -3);
  CHECK (internal.propagate () == Ref::none);
  CHECK (internal.val (L (4)) > 0);
  decide (internal, 2);
  internal.analyze (internal.propagate ());
  if (mode == 3) {
    CHECK (learnt (internal) == lits ({-1, -2}));
    CHECK_EQ (internal.stats.minimized, 1);
  } else {
    CHECK (learnt (internal) == lits ({-1, -2, -4}));
    CHECK_EQ (internal.stats.minimized, 0);
  }
  internal.check_invariants ();
}

// The first case with a tracer connected: minimisation is off (M1), the
// chain would not cover the reasons it uses.
static void test_off_with_tracer () {
  Internal internal;
  internal.opts.ccminmode = 3;
  declare (internal, "eeee");
  Proof proof{&internal};
  proof.connect (std::make_unique<Recorder> ());
  internal.proof = &proof;
  add (internal, Clause, {-1, 2});
  add (internal, Clause, {-3, 4});
  add (internal, Clause, {-1, -2, -3, -4});
  decide (internal, 1);
  CHECK (internal.propagate () == Ref::none);
  decide (internal, 3);
  internal.analyze (internal.propagate ());
  CHECK (learnt (internal) == lits ({-1, -2, -3}));
  CHECK_EQ (internal.stats.minimized, 0);
  internal.proof = nullptr;
}

int main () {
  for (int mode : {1, 2, 3}) {
    test_basic (mode);
    test_deep (mode);
    test_with_reduction (mode);
  }
  test_off_with_tracer ();
  return test_result ();
}
