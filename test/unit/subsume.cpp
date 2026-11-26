// Subsumption and strengthening (subsume.cpp) and backward subsumption
// with the resolvents of an elimination (elim.cpp): both kinds, the side
// conditions, the marks, the schedule, and the proof steps, which the
// internal checker replays.

#include "checker.hpp"
#include "child.hpp"
#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// An 'Internal' with subsumption on (and elimination, for QCIR input, if
// asked), with the recorder and the checker connected if traced.
struct Fixture {
  Internal internal;
  Proof proof{&internal};
  Recorder *recorder = nullptr;

  Fixture (const char *prefix, bool traced = false, bool elim = false) {
    internal.complete = true;
    internal.opts.subsume = 1;
    internal.opts.elim = elim;
    internal.opts.gcfrac = 100;
    internal.init_tiers ();
    declare (internal, prefix);
    if (!traced)
      return;
    auto owned = std::make_unique<Recorder> ();
    recorder = owned.get ();
    proof.connect (std::move (owned));
    proof.connect (std::make_unique<Checker> (internal));
    internal.proof = &proof;
  }
  ~Fixture () { internal.proof = nullptr; }

  Ref add (Kind kind, std::initializer_list<int> dimacs) {
    return ::add (internal, kind, dimacs);
  }
  Ref learn (Kind kind, std::initializer_list<int> dimacs,
             uint32_t glue = 2) {
    const std::vector<Lit> ls = lits (dimacs);
    internal.size_watches (); // 'add_original' does it, a test may not
    return internal.new_constraint (internal.next_id++, kind, ls, true,
                                    glue);
  }
  bool garbage_free () const {
    for (const auto *lists : {&internal.irredundant, &internal.redundant})
      for (const auto &list : *lists)
        for (const Ref ref : list)
          if (deref (internal.arena, ref).garbage ())
            return false;
    return true;
  }

  // Propagates, then runs one round; returns the root conflict.
  Ref subsume () {
    if (internal.model_cube == Ref::none)
      internal.init_model_cube ();
    CHECK (internal.propagate () == Ref::none);
    internal.lim.subsume = 0;
    CHECK (internal.subsuming ());
    const Ref conflict = internal.subsume ();
    CHECK (!internal.subsuming ());
    return conflict;
  }
  Ref eliminate () {
    if (internal.model_cube == Ref::none)
      internal.init_model_cube ();
    CHECK (internal.propagate () == Ref::none);
    CHECK (internal.eliminating ());
    return internal.eliminate ();
  }

  // Whether a live constraint of that kind and status has exactly these
  // literals.
  bool has (Kind kind, std::initializer_list<int> dimacs,
            bool learnt = false) const {
    std::vector<Lit> wanted = lits (dimacs);
    std::sort (wanted.begin (), wanted.end ());
    const auto &lists = learnt ? internal.redundant : internal.irredundant;
    for (const Ref ref : lists[index (kind)]) {
      if (deref (internal.arena, ref).garbage ())
        continue;
      std::vector<Lit> got = stored (internal, ref);
      std::sort (got.begin (), got.end ());
      if (got == wanted)
        return true;
    }
    return false;
  }
  size_t live (Kind kind, bool learnt = false) const {
    const auto &lists = learnt ? internal.redundant : internal.irredundant;
    size_t n = 0;
    for (const Ref ref : lists[index (kind)])
      n += !deref (internal.arena, ref).garbage ();
    return n;
  }
};

// (1 2) subsumes (1 2 3) and (1 2 3 4); (1 3) and (2 3 4) stay.
static void test_subsumed () {
  Fixture f ("eeee", true);
  f.add (Clause, {1, 2});
  f.add (Clause, {1, 2, 3});
  f.add (Clause, {1, 2, 3, 4});
  f.add (Clause, {1, 3});
  f.add (Clause, {2, 3, 4});
  const size_t before = f.recorder->steps.size ();
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.live (Clause), 3u);
  CHECK (f.has (Clause, {1, 2}) && f.has (Clause, {1, 3}) &&
         f.has (Clause, {2, 3, 4}));
  CHECK_EQ (f.internal.stats.subsumed[0], 2);
  CHECK_EQ (f.internal.stats.strengthened[0], 0);
  CHECK_EQ (f.internal.stats.subsumerounds, 1);
  CHECK (f.garbage_free ());
  const std::vector<std::string> expected = {"d 2", "d 3"};
  const std::vector<std::string> steps (
      f.recorder->steps.begin () + (long) before, f.recorder->steps.end ());
  CHECK (steps == expected);
}

// A learnt constraint does not delete an irredundant one, but an
// irredundant or a learnt one deletes a learnt one; a learnt constraint
// above tier 2 is no candidate.
static void test_status () {
  {
    Fixture f ("eee");
    f.learn (Clause, {1, 2});
    f.add (Clause, {1, 2, 3});
    CHECK (f.subsume () == Ref::none);
    CHECK (f.has (Clause, {1, 2, 3}));
    CHECK_EQ (f.internal.stats.subsumed[0], 0);
  }
  {
    Fixture f ("eeee");
    f.add (Clause, {1, 2});
    f.learn (Clause, {1, 2, 3});
    f.learn (Clause, {2, 4});
    f.learn (Clause, {2, 3, 4});
    CHECK (f.subsume () == Ref::none);
    CHECK_EQ (f.live (Clause, true), 1u);
    CHECK (f.has (Clause, {2, 4}, true));
    CHECK_EQ (f.internal.stats.subsumed[0], 2);
  }
  {
    Fixture f ("eee");
    f.add (Clause, {1, 2});
    f.learn (Clause, {1, 2, 3}, 100);
    CHECK (f.subsume () == Ref::none);
    CHECK (f.has (Clause, {1, 2, 3}, true));
    CHECK_EQ (f.internal.stats.subsumetried[0], 0);
  }
}

// Self-subsuming resolution: (1 2) and (-1 2 3) give (2 3), which replaces
// (-1 2 3); the chain is the strengthened constraint, then the other one.
static void test_strengthened () {
  Fixture f ("eee", true);
  f.add (Clause, {1, 2});
  f.add (Clause, {-1, 2, 3});
  const size_t before = f.recorder->steps.size ();
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.live (Clause), 2u);
  CHECK (f.has (Clause, {1, 2}) && f.has (Clause, {2, 3}));
  CHECK_EQ (f.internal.stats.strengthened[0], 1);
  CHECK_EQ (f.internal.stats.strengthenedlits[0], 1);
  const std::vector<std::string> expected = {"a 3 c: 2 3 : 2 1", "d 2"};
  const std::vector<std::string> steps (
      f.recorder->steps.begin () + (long) before, f.recorder->steps.end ());
  CHECK (steps == expected);
  CHECK_EQ (f.internal.stats.checked, 1);
  f.internal.check_invariants ();
}

// Switched off, and a secondary pivot: nothing is strengthened.
static void test_not_strengthened () {
  {
    Fixture f ("eee");
    f.internal.opts.subsumestr = 0;
    f.add (Clause, {1, 2});
    f.add (Clause, {-1, 2, 3});
    CHECK (f.subsume () == Ref::none);
    CHECK (f.has (Clause, {-1, 2, 3}));
    CHECK_EQ (f.internal.stats.strengthened[0], 0);
  }
  {
    // The pivot 1 is universal: not a Q-resolution step for clauses.
    Fixture f ("aee");
    f.add (Clause, {1, 2});
    f.add (Clause, {-1, 2, 3});
    CHECK (f.subsume () == Ref::none);
    CHECK (f.has (Clause, {-1, 2, 3}));
    CHECK_EQ (f.internal.stats.strengthened[0], 0);
  }
}

// Reduction after the step: (1 2 -3) with the universal 2 loses -3 to
// (1 3) and then 2, which leaves the unit (1); it is assigned after the
// round and the strengthened constraint is gone.
static void test_reduced_to_unit () {
  Fixture f ("eae", true);
  f.add (Clause, {1, 3});
  f.add (Clause, {1, 2, -3});
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.stats.strengthened[0], 1);
  CHECK_EQ (f.internal.stats.strengthenedlits[0], 2);
  CHECK_EQ (f.internal.stats.subsumeunits, 1);
  CHECK (f.internal.val (L (1)) > 0);
  CHECK (!f.has (Clause, {1, 2, -3}));
  CHECK (f.garbage_free ());
}

// The dual: cubes, with a universal pivot.
static void test_cubes () {
  Fixture f ("aaaa", true);
  f.add (Cube, {1, 2});
  f.add (Cube, {1, 2, 3});
  f.add (Cube, {-1, 2, 4});
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.live (Cube), 2u);
  CHECK (f.has (Cube, {1, 2}) && f.has (Cube, {2, 4}));
  CHECK_EQ (f.internal.stats.subsumed[1], 1);
  CHECK_EQ (f.internal.stats.strengthened[1], 1);
  // A clause and a cube with the same literals do not meet.
  Fixture g ("eee");
  g.add (Clause, {1, 2});
  g.add (Cube, {1, 2, 3});
  CHECK (g.subsume () == Ref::none);
  CHECK_EQ (g.internal.stats.subsumed[0] + g.internal.stats.subsumed[1], 0);
}

// A constraint with a literal assigned at the root is left alone.
static void test_fixed () {
  Fixture f ("eeee");
  f.add (Clause, {4});
  f.add (Clause, {1, 2});
  f.add (Clause, {1, 2, 3, -4});
  CHECK (f.subsume () == Ref::none);
  CHECK (f.has (Clause, {1, 2, 3, -4}));
  CHECK_EQ (f.internal.stats.subsumetried[0], 0);
}

// Marks: after a complete round nothing is scheduled until a constraint is
// added; the new constraint then subsumes an old one.
static void test_marks () {
  Fixture f ("eeee");
  f.add (Clause, {1, 4});
  f.learn (Clause, {1, 2, 3});
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.stats.subsumetried[0], 1);
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.stats.subsumetried[0], 1);
  f.learn (Clause, {1, 2});
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.stats.subsumetried[0], 2);
  CHECK_EQ (f.internal.stats.subsumed[0], 1);
  CHECK (!f.has (Clause, {1, 2, 3}, true));
  CHECK (f.has (Clause, {1, 2}, true));
}

// Out of ticks: the round is incomplete and keeps the marks, so the next
// one tries the same candidates.
static void test_incomplete () {
  Fixture f ("eee");
  f.add (Clause, {1, 2});
  f.add (Clause, {1, 2, 3});
  f.internal.opts.subsumeticks = 0;
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.stats.subsumed[0], 0);
  f.internal.opts.subsumeticks = 1000;
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.stats.subsumed[0], 1);
}

// The schedule: 'subsumeint * (rounds + 1)' conflicts ahead, and a round
// before an elimination round if none ran since the last one.
static void test_schedule () {
  Fixture f ("eeE", false, true);
  f.internal.opts.subsumeint = 5;
  f.internal.opts.elimint = 1000;
  f.add (Clause, {3, 1});
  f.add (Clause, {-3, 2});
  f.internal.init_subsume ();
  f.internal.init_elim ();
  CHECK (f.internal.subsuming ());
  CHECK (f.subsume () == Ref::none);
  CHECK_EQ (f.internal.lim.subsume, 10);
  CHECK (f.eliminate () == Ref::none);
  CHECK (!f.internal.subsuming ());
  f.internal.stats.conflicts = 10;
  CHECK (f.internal.subsuming ());
  f.internal.lim.subsume = 5000;
  CHECK (!f.internal.subsuming ());
  // Elimination is due again and no round ran since the last one.
  f.internal.stats.conflicts = 2000;
  CHECK (f.internal.eliminating () && f.internal.subsuming ());
  f.internal.opts.subsume = 0;
  CHECK (!f.internal.subsuming ());
  f.internal.opts.subsume = 1;
  f.internal.opts.mode = 2;
  CHECK (!f.internal.subsuming ());
}

// Backward subsumption with a resolvent: eliminating 5 gives (1 4) with
// the gate variable 4, whose list holds (1 2 4), which is deleted, and
// (-1 3 4), which loses -1.  Variable 4 stays: it is not rightmost in
// (4 7).
static void test_elim_backward () {
  for (int backward : {1, 0}) {
    Fixture f ("eeeEEae", true, true);
    f.internal.opts.elimbackward = backward;
    f.internal.opts.elimboundmax = 0;
    f.add (Clause, {5, 1});
    f.add (Clause, {-5, 4});
    f.add (Clause, {1, 2, 4});
    f.add (Clause, {-1, 3, 4});
    f.add (Clause, {4, 7});
    f.internal.subsumer.since_elim = true;
    CHECK (f.eliminate () == Ref::none);
    CHECK (f.internal.ftab[var (L (5))].eliminated);
    CHECK (!f.internal.ftab[var (L (4))].eliminated);
    CHECK (f.has (Clause, {1, 4}));
    CHECK_EQ (f.has (Clause, {1, 2, 4}), !backward);
    CHECK_EQ (f.has (Clause, {3, 4}), (bool) backward);
    CHECK_EQ (f.has (Clause, {-1, 3, 4}), !backward);
    CHECK_EQ (f.internal.stats.elimbwsubsumed[0], backward);
    CHECK_EQ (f.internal.stats.elimbwstrengthened[0], backward);
    CHECK (f.garbage_free ());
    f.internal.check_invariants ();
  }
}

// Without '--subsume' the resolvents are not used.
static void test_elim_backward_off () {
  Fixture f ("eeeEEae", false, true);
  f.internal.opts.subsume = 0;
  f.internal.opts.elimboundmax = 0;
  f.add (Clause, {5, 1});
  f.add (Clause, {-5, 4});
  f.add (Clause, {1, 2, 4});
  f.add (Clause, {4, 7});
  CHECK (f.eliminate () == Ref::none);
  CHECK (f.has (Clause, {1, 2, 4}));
  CHECK_EQ (f.internal.stats.elimbwsubsumed[0], 0);
}

int main () {
  test_subsumed ();
  test_status ();
  test_strengthened ();
  test_not_strengthened ();
  test_reduced_to_unit ();
  test_cubes ();
  test_fixed ();
  test_marks ();
  test_incomplete ();
  test_schedule ();
  test_elim_backward ();
  test_elim_backward_off ();
  return test_result ();
}
