// Vivification of learnt constraints (vivify.cpp): clauses and cubes
// through the same path, cases (a)-(c) of the walk, the side conditions V1,
// V2 and V4, unit and empty results, the schedule, and the proof steps,
// which the internal checker replays.

#include "checker.hpp"
#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <vector>

using namespace miniqu;

static constexpr Kind Clause = Kind::Clause, Cube = Kind::Cube;

// An 'Internal' with vivification on, the recorder and the checker
// connected if traced, and without garbage collection, so that references
// stay valid.
struct Fixture {
  Internal internal;
  Proof proof{&internal};
  Recorder *recorder = nullptr;

  Fixture (const char *prefix, bool traced = false, int mode = 0) {
    internal.opts.mode = mode;
    internal.opts.vivify = 1;
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
  // A learnt constraint; with a proof it is derived from 'chain' first.
  Ref learn (Kind kind, std::initializer_list<int> dimacs,
             std::initializer_list<uint64_t> chain = {}) {
    const std::vector<Lit> ls = lits (dimacs);
    const uint64_t id = internal.next_id++;
    if (internal.proof)
      proof.add_derived (id, kind, ls, std::vector<uint64_t> (chain));
    return internal.new_constraint (id, kind, ls, true, 2);
  }
  // Ids are stored only with a proof.
  uint64_t id (Ref ref) const {
    return internal.proof ? deref (internal.arena, ref).id () : 0;
  }
  bool garbage (Ref ref) const {
    return deref (internal.arena, ref).garbage ();
  }
  std::vector<Lit> sorted (Ref ref) const {
    std::vector<Lit> result = stored (internal, ref);
    std::sort (result.begin (), result.end ());
    return result;
  }
  static std::vector<Lit> sorted (std::initializer_list<int> dimacs) {
    std::vector<Lit> result = lits (dimacs);
    std::sort (result.begin (), result.end ());
    return result;
  }

  // Propagates at the root, runs one round, and checks the state after it
  // (8): level 0, 'seen' clear, phases unchanged, the next round not due,
  // the invariants.  Returns the root conflict.
  Ref vivify () {
    internal.init_model_cube ();
    CHECK (internal.propagate () == Ref::none);
    internal.init_vivify ();
    internal.lim.vivify = 0;
    CHECK (internal.vivifying ());
    const std::vector<int8_t> phases = internal.phases;
    const Ref conflict = internal.vivify ();
    CHECK_EQ (internal.decision_level (), 0);
    CHECK (std::all_of (internal.seen.begin (), internal.seen.end (),
                        [] (uint8_t s) { return !s; }));
    CHECK (internal.phases == phases);
    CHECK (!internal.vivifying ());
    CHECK_EQ (internal.stats.vivifyrounds, 1);
    if (conflict == Ref::none && internal.status == Status::Unknown) {
      CHECK (internal.propagate () == Ref::none);
      internal.check_invariants ();
    }
    return conflict;
  }
};

// (1) Clauses.  The learnt (1 2 3), derived from (1 2 3 4) and (1 2 3 -4),
// with (1 -2) stored: deciding -1 forces -2 by (1 -2), and then the
// candidate itself forces 3 (case (a)), so the analysis resolves the
// candidate with (1 -2) and derives (1 3).  One id is consumed.
static void test_clause (bool traced) {
  Fixture f ("eeee", traced);
  const Ref a = f.add (Clause, {1, 2, 3, 4});
  const Ref b = f.add (Clause, {1, 2, 3, -4});
  f.add (Clause, {1, -2});
  const Ref c = f.learn (Clause, {1, 2, 3}, {f.id (a), f.id (b)});
  const uint64_t next = f.internal.next_id;
  CHECK (f.vivify () == Ref::none);
  CHECK (f.sorted (c) == Fixture::sorted ({1, 3}));
  CHECK_EQ (f.internal.next_id, next + 1);
  CHECK_EQ (f.internal.stats.vivified[0], 1);
  CHECK_EQ (f.internal.stats.vivifiedlits[0], 1);
  CHECK_EQ (f.internal.stats.vivifychecked[0], 1);
  if (traced) {
    CHECK_EQ (f.internal.stats.checked, 2);
    CHECK_EQ (f.id (c), next);
  }
}

// (2) The dual case for cubes through the same function: the learnt cube
// (1 2 3) over universal variables with the stored cube (1 -2): deciding 1
// (true) forces 2 (true), and the candidate then forces -3.
static void test_cube () {
  Fixture f ("aaaa", true);
  const Ref a = f.add (Cube, {1, 2, 3, 4});
  const Ref b = f.add (Cube, {1, 2, 3, -4});
  f.add (Cube, {1, -2});
  const Ref c = f.learn (Cube, {1, 2, 3}, {f.id (a), f.id (b)});
  const uint64_t next = f.internal.next_id;
  CHECK (f.vivify () == Ref::none);
  CHECK (f.sorted (c) == Fixture::sorted ({1, 3}));
  CHECK_EQ (f.internal.next_id, next + 1);
  CHECK_EQ (f.internal.stats.vivified[1], 1);
  CHECK_EQ (f.internal.stats.checked, 2);
}

// (3) Case (a) by another reason: the learnt (1 2 3 4) with (1 3) stored.
// Deciding -1 forces 3, deciding -2 forces nothing, and 3 then disables
// the candidate: the analysis starts from (1 3) and keeps 3, giving (1 3)
// (the decision -2 is not involved).
static void test_implied () {
  Fixture f ("eeee");
  f.add (Clause, {1, 3});
  const Ref c = f.learn (Clause, {1, 2, 3, 4});
  CHECK (f.vivify () == Ref::none);
  CHECK (f.sorted (c) == Fixture::sorted ({1, 3}));
  CHECK_EQ (f.internal.stats.vivifiedlits[0], 2);
}

// (4) V1.  'exists 1 forall 2 exists 3': the cube (-1 -2) would force 2
// after the decision -1, which would shorten the learnt clause (1 2 3) to
// (1 2); only clauses propagate, so nothing changes.  Dually the clause
// (-1 2) would force 2 for the learnt cube (1 2 3) over 'forall 1 exists 2
// forall 3'.
static void test_one_kind () {
  {
    Fixture f ("eae");
    f.add (Cube, {-1, -2});
    const Ref c = f.learn (Clause, {1, 2, 3});
    CHECK (f.vivify () == Ref::none);
    CHECK_EQ (deref (f.internal.arena, c).size (), 3u);
    CHECK_EQ (f.internal.stats.vivified[0], 0);
    CHECK_EQ (f.internal.stats.vivifychecked[0], 1);
  }
  {
    Fixture f ("aea");
    f.add (Clause, {-1, 2});
    const Ref c = f.learn (Cube, {1, 2, 3});
    CHECK (f.vivify () == Ref::none);
    CHECK_EQ (deref (f.internal.arena, c).size (), 3u);
    CHECK_EQ (f.internal.stats.vivified[1], 0);
    CHECK_EQ (f.internal.stats.vivifychecked[1], 1);
  }
}

// (5) V2.  'forall 1 exists 2 3 4 5': after the decision -2 the clause
// (1 2) has the secondary 1 as its only non-vanished literal.  Mode 0
// ignores it, and the learnt (2 3 4) stays; mode 1 propagates 1, (-1 3)
// forces 3, and the QU-resolution of (3 -1) and (1 2) gives (2 3).
static void test_lone_secondary () {
  for (int mode : {0, 1}) {
    Fixture f ("aeeee", true, mode);
    f.add (Clause, {1, 2});
    f.add (Clause, {-1, 3});
    const Ref a = f.add (Clause, {2, 3, 4, 5});
    const Ref b = f.add (Clause, {2, 3, 4, -5});
    const Ref c = f.learn (Clause, {2, 3, 4}, {f.id (a), f.id (b)});
    CHECK (f.vivify () == Ref::none);
    if (mode) {
      CHECK (f.sorted (c) == Fixture::sorted ({2, 3}));
      CHECK_EQ (f.internal.stats.checked, 2);
    } else {
      CHECK_EQ (deref (f.internal.arena, c).size (), 3u);
      CHECK_EQ (f.internal.stats.vivified[0], 0);
    }
  }
}

// (6) Root literals.  With the clause unit (-2) the root-vanished 2 is
// removed from the learnt (1 2 3), and the unit's id is the last in the
// chain.  With the cube unit (2) over 'exists 1 forall 2 exists 3' (it
// forces -2 as well) 2 is a literal of the candidate without a clause
// unit and stays.  With the cube unit and the reason (1 2 3) of 3 for the
// learnt (1 -3 4), the analysis meets 2 outside the candidate and gives
// the candidate up.
static void test_root () {
  {
    Fixture f ("eeee", true);
    const Ref u = f.add (Clause, {-2});
    const Ref a = f.add (Clause, {1, 2, 3, 4});
    const Ref b = f.add (Clause, {1, 2, 3, -4});
    const Ref c = f.learn (Clause, {1, 2, 3}, {f.id (a), f.id (b)});
    const size_t before = f.recorder->steps.size ();
    CHECK (f.vivify () == Ref::none);
    CHECK (f.sorted (c) == Fixture::sorted ({1, 3}));
    CHECK_EQ (f.internal.stats.checked, 2);
    const std::string &step = f.recorder->steps[before];
    CHECK (step.size () > 2 && step[0] == 'a');
    const std::string tail = " " + std::to_string (f.id (u));
    CHECK (step.compare (step.size () - tail.size (), tail.size (), tail) ==
           0);
  }
  {
    Fixture f ("eae");
    f.add (Cube, {2});
    const Ref c = f.learn (Clause, {1, 2, 3});
    CHECK (f.vivify () == Ref::none);
    CHECK_EQ (deref (f.internal.arena, c).size (), 3u);
    CHECK_EQ (f.internal.stats.vivifyskipped, 0);
  }
  {
    Fixture f ("eaee");
    f.add (Cube, {2});
    f.add (Clause, {1, 2, 3});
    const Ref c = f.learn (Clause, {1, -3, 4});
    CHECK (f.vivify () == Ref::none);
    CHECK_EQ (deref (f.internal.arena, c).size (), 3u);
    CHECK_EQ (f.internal.stats.vivifyskipped, 1);
    CHECK_EQ (f.internal.stats.vivified[0], 0);
  }
}

// (7) A unit result: (1 2) and (1 -2) conflict after the decision -1, so
// the learnt (1 2 3) becomes the unit (1), assigned after the round.  Over
// 'forall 1 exists 2 3' the same unit reduces to the empty clause.
static void test_unit_and_empty () {
  {
    Fixture f ("eee", true);
    const Ref a = f.add (Clause, {1, 2});
    f.add (Clause, {1, -2});
    const Ref c = f.learn (Clause, {1, 2, 3}, {f.id (a)});
    CHECK (f.vivify () == Ref::none);
    CHECK (f.garbage (c));
    CHECK_EQ (f.internal.stats.vivifyunits, 1);
    CHECK (f.internal.val (L (1)) > 0);
    const Ref r = f.internal.reason (var (L (1)));
    CHECK (r != Ref::none && deref (f.internal.arena, r).size () == 1);
    CHECK (f.internal.redundant[0].empty ());
    CHECK_EQ (f.internal.stats.checked, 2);
  }
  {
    Fixture f ("aee", true);
    const Ref a = f.add (Clause, {1, 2});
    f.add (Clause, {1, -2});
    f.learn (Clause, {1, 2, 3}, {f.id (a)});
    CHECK (f.vivify () == Ref::none);
    CHECK (f.internal.status == Status::False);
    CHECK_EQ (f.internal.stats.checked, 2);
  }
}

// The schedule: the first round after 'vivifyint' conflicts, the next
// 'vivifyint * (rounds + 1)' conflicts after the last; nothing in mode 2.
static void test_schedule () {
  Fixture f ("ee");
  f.internal.opts.vivifyint = 5;
  f.internal.init_vivify ();
  CHECK (!f.internal.vivifying ());
  f.internal.stats.conflicts = 5;
  CHECK (f.internal.vivifying ());
  f.internal.init_model_cube ();
  CHECK (f.internal.vivify () == Ref::none);
  CHECK_EQ (f.internal.lim.vivify, 15);
  CHECK (!f.internal.vivifying ());
  f.internal.stats.conflicts = 15;
  CHECK (f.internal.vivifying ());
  f.internal.opts.mode = 2;
  CHECK (!f.internal.vivifying ());
  f.internal.opts.mode = 0;
  f.internal.opts.vivifyclause = f.internal.opts.vivifycube = 0;
  CHECK (!f.internal.vivifying ());
}

int main () {
  test_clause (false);
  test_clause (true);
  test_cube ();
  test_implied ();
  test_one_kind ();
  test_lone_secondary ();
  test_root ();
  test_unit_and_empty ();
  test_schedule ();
  return test_result ();
}
