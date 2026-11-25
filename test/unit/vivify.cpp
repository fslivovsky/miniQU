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
    internal.init_tiers ();
    declare (internal, prefix);
    internal.size_watches ();
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
    std::vector<Lit> result = ::stored (internal, ref);
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
    if (internal.model_cube == Ref::none)
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

// A further round after the first, without the checks of 'vivify'.
static void again (Fixture &f) {
  f.internal.lim.vivify = 0;
  CHECK (f.internal.vivify () == Ref::none);
}

static bool tried (Fixture &f, Ref ref) {
  return deref (f.internal.arena, ref).vivified ();
}

// (9) The 'vivified' bit.  The learnts (1 2 3) and (4 5 6) cannot be
// shortened: both get the bit.  With 'vivifyonce' the next round tries
// only the new (1 4 5), the round after finds no candidate without the bit
// and takes all three again; without it every round tries all.
static void test_once () {
  for (int once : {1, 0}) {
    Fixture f ("eeeeee");
    f.internal.opts.vivifyonce = once;
    const Ref a = f.learn (Clause, {1, 2, 3});
    const Ref b = f.learn (Clause, {4, 5, 6});
    CHECK (!tried (f, a) && !tried (f, b));
    CHECK (f.vivify () == Ref::none);
    CHECK (tried (f, a) && tried (f, b));
    CHECK_EQ (f.internal.stats.vivifychecked[0], 2);
    const Ref c = f.learn (Clause, {1, 4, 5});
    again (f);
    CHECK (tried (f, c));
    CHECK_EQ (f.internal.stats.vivifychecked[0], once ? 3 : 5);
    CHECK_EQ (f.internal.stats.vivifyrescheduled, 0);
    again (f);
    CHECK_EQ (f.internal.stats.vivifychecked[0], once ? 6 : 8);
    CHECK_EQ (f.internal.stats.vivifyrescheduled, once);
    CHECK (tried (f, a) && tried (f, b) && tried (f, c));
  }
  // A shortened candidate keeps the bit clear.
  Fixture f ("eeee");
  f.add (Clause, {1, 3});
  const Ref c = f.learn (Clause, {1, 2, 3, 4});
  CHECK (f.vivify () == Ref::none);
  CHECK_EQ (deref (f.internal.arena, c).size (), 2u);
  CHECK (!tried (f, c));
}

// (10) 'vivifytier' with the limits 2 and 6: the learnts of glue 2, 5 and
// 9 are tier 1, 2 and 3.  Tier 1 takes the first, 2 the first two, 3 all,
// lower tier visited first (from the back of the candidates), newest
// first inside a tier.
static void test_tier () {
  for (int tier : {1, 2, 3}) {
    Fixture f ("eeeeeeeeeeee");
    f.internal.opts.vivifytier = tier;
    CHECK_EQ (f.internal.tiers.tier1[0], 2);
    CHECK_EQ (f.internal.tiers.tier2[0], 6);
    const Ref t3 = f.learn (Clause, {7, 8, 9});
    deref (f.internal.arena, t3).set_glue (9);
    const Ref t1 = f.learn (Clause, {1, 2, 3});
    const Ref t2 = f.learn (Clause, {4, 5, 6});
    deref (f.internal.arena, t2).set_glue (5);
    const Ref u1 = f.learn (Clause, {10, 11, 12});
    f.internal.vivify_select (Clause);
    std::vector<Ref> expected = {t1, u1};
    if (tier >= 2)
      expected.insert (expected.begin (), t2);
    if (tier == 3)
      expected.insert (expected.begin (), t3);
    CHECK (f.internal.vivifier.candidates == expected);
    f.internal.vivifier.candidates.clear ();
    CHECK (f.vivify () == Ref::none);
    CHECK_EQ (f.internal.stats.vivifychecked[0], tier + 1);
    CHECK_EQ (tried (f, t2), tier >= 2);
    CHECK_EQ (tried (f, t3), tier == 3);
  }
}

// (11) The literal order.  With (3 -1) stored, deciding -3 first forces -1
// and then 2 by the learnt (1 2 3) itself, giving (2 3); the stored order
// (and the order by literal index) decides -1, -2 and keeps all three.
// The learnts (3 4 5) and (3 6 7) make 3 the most frequent literal.
static void test_order () {
  for (bool frequent : {false, true}) {
    Fixture f ("eeeeeee");
    f.add (Clause, {3, -1});
    const Ref c = f.learn (Clause, {1, 2, 3});
    if (frequent) {
      f.learn (Clause, {3, 4, 5});
      f.learn (Clause, {3, 6, 7});
    }
    CHECK (f.vivify () == Ref::none);
    if (frequent)
      CHECK (f.sorted (c) == Fixture::sorted ({2, 3}));
    else
      CHECK (f.sorted (c) == Fixture::sorted ({1, 2, 3}));
  }
}

// (12) After an elimination round over QCIR input: the gate variable 4 is
// eliminated together with the learnt (1 3 4), and the round that follows
// neither assigns nor sees it; the invariants hold.
static void test_after_elim () {
  Fixture f ("eeeE");
  f.internal.complete = true;
  f.internal.opts.elim = 1;
  f.add (Clause, {4, 1});
  f.add (Clause, {4, 2});
  f.add (Clause, {-4, 3});
  const Ref c = f.learn (Clause, {1, 2, 3});
  const Ref d = f.learn (Clause, {1, 3, 4});
  f.internal.init_model_cube ();
  CHECK (f.internal.propagate () == Ref::none);
  CHECK (f.internal.eliminating ());
  CHECK (f.internal.eliminate () == Ref::none);
  CHECK (f.internal.ftab[var (L (4))].eliminated);
  CHECK (f.garbage (d) || std::find (f.internal.redundant[0].begin (),
                                     f.internal.redundant[0].end (),
                                     d) == f.internal.redundant[0].end ());
  (void) c;
  CHECK (f.vivify () == Ref::none);
  CHECK_EQ (f.internal.val (L (4)), 0);
  for (const auto *lists : {&f.internal.irredundant, &f.internal.redundant})
    for (const auto &list : *lists)
      for (const Ref ref : list) {
        const Constraint &k = deref (f.internal.arena, ref);
        if (k.garbage ())
          continue;
        for (const Lit l : k)
          CHECK (var (l) != var (L (4)));
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
  test_once ();
  test_tier ();
  test_order ();
  test_after_elim ();
  return test_result ();
}
