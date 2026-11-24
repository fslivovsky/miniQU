// Learnt-constraint minimisation (minimize.cpp), called by 'learn' after
// the analyses of modes 0 and 1.  Each case states which of the ccminmodes
// remove which literal, and, with a proof, which reasons follow the chain
// of the analysis: those of the variables resolved away, in reverse trail
// order.  The internal checker replays every learnt step.
//
// Every case is written for clauses.  The cube version swaps the
// quantifiers and negates every literal: a decision then makes the same
// literals vanish, the same constraints propagate the same variables and
// the learnt cube is the negated learnt clause, with the same chain.

#include "checker.hpp"
#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <algorithm>
#include <memory>
#include <string>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

struct Fixture {
  Internal internal;
  Proof proof{&internal};
  Recorder *recorder = nullptr;
  const Kind kind;

  // 'prefix' and the literals of 'add' and 'learnt' as for clauses.
  Fixture (std::string prefix, Kind k, int ccminmode, bool traced,
           bool legacy = false)
      : kind (k) {
    internal.opts.ccminmode = ccminmode;
    internal.opts.legacyanalyze = legacy;
    if (kind == Cube)
      for (char &c : prefix)
        c = c == 'e' ? 'a' : c == 'a' ? 'e' : c;
    declare (internal, prefix.c_str ());
    if (!traced)
      return;
    auto owned = std::make_unique<Recorder> ();
    recorder = owned.get ();
    proof.connect (std::move (owned));
    proof.connect (std::make_unique<Checker> (internal));
    internal.proof = &proof;
  }
  ~Fixture () { internal.proof = nullptr; }

  int sign () const { return kind == Clause ? 1 : -1; }

  void add (std::initializer_list<int> clause) {
    std::vector<int> dimacs;
    for (int d : clause)
      dimacs.push_back (sign () * d);
    std::vector<Lit> ls;
    for (int d : dimacs)
      ls.push_back (L (d));
    internal.add_original (kind, ls, 0);
  }

  void decide (int dimacs) {
    ::decide (internal, dimacs);
    CHECK (internal.propagate () == Ref::none);
  }

  // Decides 'dimacs', analyses the conflict it leads to and learns.
  void conflict (int dimacs) {
    ::decide (internal, dimacs);
    const Ref conflict = internal.propagate ();
    CHECK (conflict != Ref::none);
    internal.analyze (conflict);
  }

  // The constraint learnt last, in clause form, sorted.
  std::vector<Lit> learnt () const {
    const std::vector<Ref> &units = internal.irredundant[index (kind)];
    const std::vector<Ref> &list = internal.redundant[index (kind)];
    // A learnt unit is stored irredundant.
    const Ref ref = list.empty () ? units.back () : list.back ();
    std::vector<Lit> result;
    for (Lit l : stored (internal, ref))
      result.push_back (kind == Clause ? l : ~l);
    std::sort (result.begin (), result.end ());
    return result;
  }

  // The chain of the last derived step, e.g. " 5 4 2".
  std::string chain () const {
    for (auto it = recorder->steps.rbegin (); it != recorder->steps.rend ();
         ++it)
      if (it->front () == 'a')
        return it->substr (it->rfind (" :") + 2);
    return "none";
  }
};

// 'exists 1 2 3 4' with (-1 2), (-3 4) and (-1 -2 -3 -4): the decision 1
// forces 2, the decision 3 forces 4 and the last clause conflicts.  The
// analysis learns (-1 -2 -3) with chain 3 2; the reason of 2 (id 1)
// contains only -1, which is in the clause, so every mode removes -2 and
// appends 1.
static void test_one_reason (Kind kind, int mode, bool traced,
                             bool legacy) {
  Fixture f ("eeee", kind, mode, traced, legacy);
  f.add ({-1, 2});
  f.add ({-3, 4});
  f.add ({-1, -2, -3, -4});
  f.decide (1);
  f.conflict (3);
  CHECK (f.learnt () == lits ({-1, -3}));
  CHECK_EQ (f.internal.stats.minimized, 1);
  if (traced) {
    CHECK_EQ (f.chain (), std::string (" 3 2 1"));
    CHECK_EQ (f.internal.stats.checked, 1);
    CHECK_EQ (f.internal.stats.minimizedchain, 1);
  }
  f.internal.check_invariants ();
}

// 'exists 1 2 3 4 5' with (-1 2), (-2 3), (-4 5) and (-1 -3 -4 -5): 1
// forces 2 and 3, the decision 4 forces 5 and the last clause conflicts;
// the analysis learns (-1 -3 -4) with chain 4 3.  The reason of 3 brings in
// -2, which is not in the clause: basic minimisation keeps -3, the deep
// modes follow the reason of 2 back to -1, remove -3 and append the
// reasons of 3 and 2 in reverse trail order.
static void test_chain_of_reasons (Kind kind, int mode, bool traced,
                                   bool legacy) {
  Fixture f ("eeeee", kind, mode, traced, legacy);
  f.add ({-1, 2});
  f.add ({-2, 3});
  f.add ({-4, 5});
  f.add ({-1, -3, -4, -5});
  f.decide (1);
  f.conflict (4);
  const bool removed = mode > 1;
  CHECK (f.learnt () == (removed ? lits ({-1, -4}) : lits ({-1, -3, -4})));
  CHECK_EQ (f.internal.stats.minimized, removed ? 1 : 0);
  if (traced)
    CHECK_EQ (f.chain (), std::string (removed ? " 4 3 2 1" : " 4 3"));
  f.internal.check_invariants ();
}

// 'exists 1 2 3' with the unit (2), (-1 3) and (-2 -1 -3): the decision 1
// forces 3 and the last clause conflicts; the analysis learns (-1 -2) with
// chain 3 2.  -2 is a root literal whose reason is the unit (id 1) of the
// same kind, so every mode removes it, appends the unit and learns the
// unit (-1).
static void test_root_unit (Kind kind, int mode, bool traced, bool legacy) {
  Fixture f ("eee", kind, mode, traced, legacy);
  f.add ({2});
  f.add ({-1, 3});
  f.add ({-2, -1, -3});
  f.conflict (1);
  CHECK (f.learnt () == lits ({-1}));
  CHECK_EQ (f.internal.stats.minimized, 1);
  if (traced)
    CHECK_EQ (f.chain (), std::string (" 3 2 1"));
  f.internal.check_invariants ();
}

// 'exists 1 2 3 4 5 6' with the unit (2), (-1 3), (-2 -3 4), (-5 6) and
// (-1 -4 -5 -6): 1 forces 3 and 4, 5 forces 6, and the last clause
// conflicts; the analysis learns (-1 -4 -5) with chain 5 4.  The reason of
// 4 holds the root literal -2 (free: unit 1) and -3, whose reason (id 2)
// holds only -1.  The deep modes remove -4 and append, in reverse trail
// order, the reasons of 4 (id 3), of 3 (id 2) and the unit of 2 (id 1).
static void test_chain_to_root (Kind kind, int mode, bool traced,
                                bool legacy) {
  Fixture f ("eeeeee", kind, mode, traced, legacy);
  f.add ({2});
  f.add ({-1, 3});
  f.add ({-2, -3, 4});
  f.add ({-5, 6});
  f.add ({-1, -4, -5, -6});
  f.decide (1);
  f.conflict (5);
  const bool removed = mode > 1;
  CHECK (f.learnt () == (removed ? lits ({-1, -5}) : lits ({-1, -4, -5})));
  if (traced)
    CHECK_EQ (f.chain (), std::string (removed ? " 5 4 3 2 1" : " 5 4"));
  f.internal.check_invariants ();
}

// 'exists 1 2 forall 3 exists 4 5' with (-1 3 4), (-2 5) and
// (-1 -2 -4 -5): the decisions 1 and -3 force 4, the decision 2 forces 5
// and the last clause conflicts; the analysis learns (-1 -2 -4) with chain
// 3 2.  Removing -4 brings in the universal 3, which is not in the clause:
// modes 1 and 2 keep -4 (the exploration fails at the decision 3 and adds
// nothing to the chain), mode 3 removes it and appends the reason of 4,
// since 3 is right of every primary literal left (-1 and -2) and the
// reduction at the end of the step drops it from the resolvent.
static void test_with_reduction (Kind kind, int mode, bool traced,
                                 bool legacy) {
  Fixture f ("eeaee", kind, mode, traced, legacy);
  f.add ({-1, 3, 4});
  f.add ({-2, 5});
  f.add ({-1, -2, -4, -5});
  f.decide (1);
  f.decide (-3);
  CHECK (f.internal.val (L (4)) > 0);
  f.conflict (2);
  const bool removed = mode == 3;
  CHECK (f.learnt () == (removed ? lits ({-1, -2}) : lits ({-1, -2, -4})));
  CHECK_EQ (f.internal.stats.minimized, removed ? 1 : 0);
  if (traced)
    CHECK_EQ (f.chain (), std::string (removed ? " 3 2 1" : " 3 2"));
  f.internal.check_invariants ();
}

// 'exists 1 ... 7' with (-1 2), (-1 7), (-2 -3 4), (-5 6) and
// (-1 -4 -5 -6 -7): 1 forces 2 and 7, 3 forces 4, 5 forces 6, and the
// last clause conflicts; the analysis learns (-1 -4 -5 -7) with chain 5 4.
// -7 goes in every mode through its reason (id 2).  The reason of 4 holds
// -3, a decision that is not in the clause, so -4 stays, although the deep
// modes may have shown 2 removable on the way: neither the reason of 4 nor
// that of 2 may be appended.
static void test_failed_exploration (Kind kind, int mode, bool traced,
                                     bool legacy) {
  Fixture f ("eeeeeee", kind, mode, traced, legacy);
  f.add ({-1, 2});
  f.add ({-1, 7});
  f.add ({-2, -3, 4});
  f.add ({-5, 6});
  f.add ({-1, -4, -5, -6, -7});
  f.decide (1);
  f.decide (3);
  f.conflict (5);
  CHECK (f.learnt () == lits ({-1, -4, -5}));
  CHECK_EQ (f.internal.stats.minimized, 1);
  if (traced)
    CHECK_EQ (f.chain (), std::string (" 5 4 2"));
  f.internal.check_invariants ();
}

// Mode 1, 'exists 1 forall 2 exists 3 4' with (-1 3), (2 4) and
// (-1 -3 -4 2): the decision 1 forces 3, the decision -2 forces 4 (or -4)
// and the other clause conflicts.  The analysis stops with the secondary 2
// alone on level 2 and learns (-1 2 -3).  Every mode could remove -3
// through (-1 3), but the reduction would then drop the asserting 2 with
// it, so the constraint is learnt unminimised.
static void test_secondary_asserting (Kind kind, int mode, bool traced) {
  Fixture f ("eaee", kind, mode, traced);
  f.internal.opts.mode = 1;
  f.add ({-1, 3});
  f.add ({2, 4});
  f.add ({-1, -3, -4, 2});
  f.decide (1);
  f.conflict (-2);
  CHECK (f.learnt () == lits ({-1, 2, -3}));
  CHECK_EQ (f.internal.stats.minimized, 0);
  if (traced)
    CHECK_EQ (f.internal.stats.checked, 1);
  f.internal.check_invariants ();
}

// Without a proof the same constraints are learnt (checked by every case
// untraced) and nothing is counted as appended.
static void test_untraced_counts_nothing () {
  Fixture f ("eeee", Clause, 3, false);
  f.add ({-1, 2});
  f.add ({-3, 4});
  f.add ({-1, -2, -3, -4});
  f.decide (1);
  f.conflict (3);
  CHECK_EQ (f.internal.stats.minimized, 1);
  CHECK_EQ (f.internal.stats.minimizedchain, 0);
}

int main () {
  for (Kind kind : {Clause, Cube})
    for (int mode : {1, 2, 3})
      for (bool traced : {false, true})
        for (bool legacy : {false, true}) {
          test_one_reason (kind, mode, traced, legacy);
          test_chain_of_reasons (kind, mode, traced, legacy);
          test_root_unit (kind, mode, traced, legacy);
          test_chain_to_root (kind, mode, traced, legacy);
          test_with_reduction (kind, mode, traced, legacy);
          test_failed_exploration (kind, mode, traced, legacy);
          if (!legacy)
            test_secondary_asserting (kind, mode, traced);
        }
  test_untraced_counts_nothing ();
  return test_result ();
}
