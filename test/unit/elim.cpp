// Bounded variable elimination (elim.cpp): clauses and cubes through the
// same path, the side conditions E1-E4, tautological, unit and empty
// resolvents, and the proof steps, which the internal checker replays.

#include "checker.hpp"
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

// An 'Internal' for QCIR input with elimination on, with the recorder and
// the checker connected if traced ('dl' before the variables exist).
struct Fixture {
  Internal internal;
  Proof proof{&internal};
  Recorder *recorder = nullptr;

  Fixture (const char *prefix, bool traced = false, bool dl = false) {
    internal.complete = true;
    internal.opts.elim = 1;
    internal.opts.dl = dl;
    internal.opts.gcfrac = 100;
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
  Ref learn (Kind kind, std::initializer_list<int> dimacs) {
    const std::vector<Lit> ls = lits (dimacs);
    return internal.new_constraint (internal.next_id++, kind, ls, true, 2);
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
  Ref eliminate () {
    if (internal.model_cube == Ref::none)
      internal.init_model_cube ();
    CHECK (internal.propagate () == Ref::none);
    CHECK (internal.eliminating ());
    const Ref conflict = internal.eliminate ();
    CHECK (!internal.eliminating ());
    return conflict;
  }

  // Whether a live irredundant constraint of that kind has exactly these
  // literals.
  bool has (Kind kind, std::initializer_list<int> dimacs) const {
    std::vector<Lit> wanted = lits (dimacs);
    std::sort (wanted.begin (), wanted.end ());
    for (const Ref ref : internal.irredundant[index (kind)]) {
      if (deref (internal.arena, ref).garbage ())
        continue;
      std::vector<Lit> got = stored (internal, ref);
      std::sort (got.begin (), got.end ());
      if (got == wanted)
        return true;
    }
    return false;
  }
  size_t live (Kind kind) const {
    return internal.irredundant[index (kind)].size ();
  }
  bool eliminated (int dimacs) const {
    return internal.ftab[var (L (dimacs))].eliminated;
  }
};

// (x a)(x b)(-x c) with the gate variable x = 4: the resolvents (a c) and
// (b c) replace the three parents.
static void test_clauses () {
  Fixture f ("eeeE");
  f.add (Clause, {4, 1});
  f.add (Clause, {4, 2});
  f.add (Clause, {-4, 3});
  CHECK (f.eliminate () == Ref::none);
  CHECK (f.eliminated (4));
  CHECK_EQ (f.live (Clause), 2u);
  CHECK (f.has (Clause, {1, 3}) && f.has (Clause, {2, 3}));
  CHECK_EQ (f.internal.stats.eliminated[0], 1);
  CHECK_EQ (f.internal.stats.resolvents[0], 2);
  CHECK_EQ (f.internal.stats.elimdeleted[0], 3);
  CHECK_EQ (f.internal.stats.elimtried, 1);
  CHECK_EQ (f.internal.stats.elimrounds, 1);
}

// 3x3 occurrences give 9 resolvents, more than the 6 parents: blocked with
// the bound 0, eliminated with the bound 3.
static void test_bound () {
  for (int bound : {0, 3}) {
    Fixture f ("eeeeeeE");
    f.internal.opts.elimbound = bound;
    for (int other : {1, 2, 3})
      f.add (Clause, {7, other});
    for (int other : {4, 5, 6})
      f.add (Clause, {-7, other});
    CHECK (f.eliminate () == Ref::none);
    CHECK_EQ (f.eliminated (7), bound > 0);
    CHECK_EQ (f.internal.stats.elimblockedbound, bound ? 0 : 1);
    CHECK_EQ (f.live (Clause), bound ? 9u : 6u);
  }
}

// The dual: a universal gate variable eliminated by cube resolution.
static void test_cubes () {
  Fixture f ("aaaA");
  f.add (Cube, {4, 1});
  f.add (Cube, {4, 2});
  f.add (Cube, {-4, 3});
  CHECK (f.eliminate () == Ref::none);
  CHECK (f.eliminated (4));
  CHECK_EQ (f.live (Cube), 2u);
  CHECK (f.has (Cube, {1, 3}) && f.has (Cube, {2, 3}));
  CHECK_EQ (f.internal.stats.eliminated[1], 1);
  CHECK_EQ (f.internal.stats.resolvents[1], 2);
  CHECK_EQ (f.internal.stats.elimdeleted[1], 3);
}

// E2: the existential 2 occurs in the cube (2 3), so it stays.
static void test_other_kind () {
  Fixture f ("eEa");
  f.add (Clause, {2, 1});
  f.add (Clause, {-2, 1});
  f.add (Cube, {2, 3});
  CHECK (f.eliminate () == Ref::none);
  CHECK (!f.eliminated (2));
  CHECK_EQ (f.internal.stats.elimblockedother, 1);
  CHECK_EQ (f.live (Clause), 2u);
}

// E3: (2 3) with 3 in a deeper block blocks 2; a neighbour in the same
// block does not.
static void test_rightmost () {
  {
    Fixture f ("eEae");
    f.add (Clause, {2, 4});
    f.add (Clause, {-2, 1});
    CHECK (f.eliminate () == Ref::none);
    CHECK (!f.eliminated (2));
    CHECK_EQ (f.internal.stats.elimblockedright, 1);
  }
  {
    Fixture f ("aEe");
    f.add (Clause, {2, 3});
    f.add (Clause, {-2, 1});
    CHECK (f.eliminate () == Ref::none);
    CHECK (f.eliminated (2));
    CHECK (f.has (Clause, {1, 3}));
  }
}

// A tautological resolvent is dropped; one that reduces to a unit is
// assigned after the round; an empty one decides the formula.
static void test_results () {
  {
    Fixture f ("eeE");
    f.add (Clause, {3, 1});
    f.add (Clause, {3, 2});
    f.add (Clause, {-3, -1});
    CHECK (f.eliminate () == Ref::none);
    CHECK (f.eliminated (3));
    CHECK_EQ (f.internal.stats.resolvents[0], 1);
    CHECK_EQ (f.live (Clause), 1u);
    CHECK (f.has (Clause, {2, -1}));
  }
  {
    // (1 2) reduces to (1), since 2 is universal and right of 1.
    Fixture f ("eaE");
    f.add (Clause, {3, 1});
    f.add (Clause, {-3, 2});
    CHECK (f.eliminate () == Ref::none);
    CHECK_EQ (f.internal.stats.elimunits, 1);
    CHECK (f.internal.val (L (1)) > 0);
    CHECK (f.has (Clause, {1}));
  }
  {
    Fixture f ("aE", true);
    f.add (Clause, {2, 1});
    f.add (Clause, {-2, 1});
    CHECK (f.eliminate () == Ref::none);
    CHECK (f.internal.status == Status::False);
  }
}

// Each resolvent is derived from its two parents before any parent is
// deleted; the checker replays the steps.
static void test_proof () {
  Fixture f ("eeeE", true);
  f.add (Clause, {4, 1});
  f.add (Clause, {4, 2});
  f.add (Clause, {-4, 3});
  const size_t before = f.recorder->steps.size ();
  CHECK (f.eliminate () == Ref::none);
  const std::vector<std::string> expected = {
      "a 4 c: 1 3 : 1 3", "a 5 c: 2 3 : 2 3", "d 1", "d 2", "d 3"};
  const std::vector<std::string> steps (
      f.recorder->steps.begin () + (long) before, f.recorder->steps.end ());
  CHECK (steps == expected);
  CHECK_EQ (f.internal.stats.checked, 2);
}

// Decision variables and the switches per kind.
static void test_switches () {
  {
    Fixture f ("eee");
    f.add (Clause, {3, 1});
    f.add (Clause, {-3, 2});
    CHECK (f.eliminate () == Ref::none);
    CHECK_EQ (f.internal.stats.elimtried, 0);
  }
  {
    Fixture f ("eeE");
    f.internal.opts.elimclause = 0;
    f.add (Clause, {3, 1});
    f.add (Clause, {-3, 2});
    CHECK (f.eliminate () == Ref::none);
    CHECK (!f.eliminated (3));
    CHECK_EQ (f.internal.stats.elimtried, 0);
  }
  {
    Fixture f ("aaA");
    f.internal.opts.elimcube = 0;
    f.add (Cube, {3, 1});
    f.add (Cube, {-3, 2});
    CHECK (f.eliminate () == Ref::none);
    CHECK (!f.eliminated (3));
    CHECK_EQ (f.internal.stats.elimtried, 0);
  }
  {
    // No round without 'elim', in mode 2, or for QDIMACS input.
    Fixture f ("eE");
    f.internal.opts.elim = 0;
    CHECK (!f.internal.eliminating ());
    f.internal.opts.elim = 1;
    f.internal.opts.mode = 2;
    CHECK (!f.internal.eliminating ());
    f.internal.opts.mode = 0;
    f.internal.complete = false;
    CHECK (!f.internal.eliminating ());
  }
}

// E2 against learnt constraints: a learnt cube containing the existential
// gate variable 3 blocks it.
static void test_learnt_other_kind () {
  Fixture f ("eeEa");
  f.add (Clause, {3, 1});
  f.add (Clause, {-3, 2});
  f.learn (Cube, {3, 4});
  CHECK (f.eliminate () == Ref::none);
  CHECK (!f.eliminated (3));
  CHECK_EQ (f.internal.stats.elimblockedother, 1);
}

// E3 against learnt constraints: the learnt (3 5 1) with 5 in a deeper
// block blocks 3; once it is deleted, the next round eliminates 3.
static void test_learnt_rightmost () {
  Fixture f ("eeEae");
  f.add (Clause, {3, 1});
  f.add (Clause, {-3, 2});
  const Ref learnt = f.learn (Clause, {3, 5, 1});
  CHECK (f.eliminate () == Ref::none);
  CHECK (!f.eliminated (3));
  CHECK_EQ (f.internal.stats.elimblockedright, 1);
  f.internal.mark_garbage (learnt);
  std::erase (f.internal.redundant[index (Clause)], learnt);
  f.internal.lim.elim = 0;
  CHECK (f.eliminate () == Ref::none);
  CHECK (f.eliminated (3));
  CHECK (f.has (Clause, {1, 2}));
  CHECK_EQ (f.internal.stats.elimrounds, 2);
}

// A learnt constraint that passes E3 is deleted with the variable, never
// used as a parent, and leaves no garbage reference behind.
static void test_learnt_deleted () {
  Fixture f ("eeeE");
  f.add (Clause, {4, 1});
  f.add (Clause, {-4, 2});
  f.learn (Clause, {4, 1, 3});
  f.learn (Clause, {1, 2, 3});
  CHECK (f.eliminate () == Ref::none);
  CHECK (f.eliminated (4));
  CHECK_EQ (f.internal.stats.resolvents[0], 1);
  CHECK_EQ (f.internal.stats.elimdeleted[0], 2);
  CHECK_EQ (f.internal.stats.elimlearnt[0], 1);
  CHECK_EQ (f.internal.redundant[index (Clause)].size (), 1u);
  CHECK (f.garbage_free ());
}

// The conflict schedule: no round right after one, the next after
// 'elimint * (rounds + 1)' more conflicts, none at all without 'eliminp'.
static void test_schedule () {
  {
    Fixture f ("eeEE");
    f.internal.opts.elimint = 5;
    f.add (Clause, {3, 1});
    f.add (Clause, {-3, 2});
    f.internal.init_elim ();
    CHECK_EQ (f.internal.lim.elim, 0);
    CHECK (f.eliminate () == Ref::none);
    CHECK_EQ (f.internal.lim.elim, 10);
    CHECK_EQ (f.internal.stats.eliminprounds, 0);
    f.internal.stats.conflicts = 9;
    CHECK (!f.internal.eliminating ());
    f.internal.stats.conflicts = 10;
    CHECK (f.eliminate () == Ref::none);
    CHECK_EQ (f.internal.stats.eliminprounds, 1);
    CHECK_EQ (f.internal.lim.elim, 25);
  }
  {
    Fixture f ("eE");
    f.internal.opts.eliminp = 0;
    f.internal.init_elim ();
    CHECK (f.eliminate () == Ref::none);
    f.internal.stats.conflicts = INT64_MAX - 1;
    CHECK (!f.internal.eliminating ());
    f.internal.opts.elimpre = 0;
    f.internal.init_elim ();
    CHECK (!f.internal.eliminating ());
  }
  {
    Fixture f ("eE");
    f.internal.opts.elimpre = 0;
    f.internal.opts.elimint = 7;
    f.internal.init_elim ();
    CHECK (!f.internal.eliminating ());
    f.internal.stats.conflicts = 7;
    CHECK (f.eliminate () == Ref::none);
    CHECK_EQ (f.internal.stats.eliminprounds, 1);
  }
}

// A round is due above level 0 too; the search loop backtracks first and
// runs it after propagating at level 0 (the steps of its branch).
static void test_above_root () {
  Fixture f ("eeE");
  f.add (Clause, {3, 1});
  f.add (Clause, {-3, 2});
  f.internal.init_model_cube ();
  CHECK (f.internal.propagate () == Ref::none);
  decide (f.internal, 1);
  CHECK (f.internal.propagate () == Ref::none);
  CHECK (f.internal.eliminating ());
  f.internal.backtrack (0);
  CHECK_EQ (f.internal.decision_level (), 0);
  CHECK (f.internal.propagate () == Ref::none);
  CHECK (f.internal.eliminate () == Ref::none);
  CHECK (f.eliminated (3));
  CHECK (!f.internal.eliminating ());
}

// With '--dl', a dependency mentioning an eliminated variable (which the
// search never records, see elim.cpp) makes the round reset them all.
static void test_dependencies () {
  Fixture f ("Eee", false, true);
  f.add (Clause, {1, 2});
  f.add (Clause, {-1, 3});
  f.internal.record_dependency (2, 0);
  CHECK (f.eliminate () == Ref::none);
  CHECK (f.eliminated (1));
  CHECK_EQ (f.internal.stats.depresets, 1);
  CHECK (f.internal.depend.on[2].empty ());
  CHECK (f.internal.depend.watching[0].empty ());
}

int main () {
  test_clauses ();
  test_bound ();
  test_cubes ();
  test_other_kind ();
  test_rightmost ();
  test_results ();
  test_proof ();
  test_switches ();
  test_learnt_other_kind ();
  test_learnt_rightmost ();
  test_learnt_deleted ();
  test_schedule ();
  test_above_root ();
  test_dependencies ();
  return test_result ();
}
