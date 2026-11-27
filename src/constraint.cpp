// The constraint databases (ARCHITECTURE 4.3, 5, 6): the only place where
// constraints are created, deleted, shrunk and connected to watch lists.
//
// Original constraints take one path, the one the old solver used with a
// proof (porting note 1): sort, remove duplicate literals, skip
// tautological clauses and contradictory cubes, then 'qreduce', and store
// the result *without* simplifying it under the current root assignment.
// Removing a literal because a unit of the other kind assigned it would not
// be a derivation of the same kind (INV-DERIVED).  An empty constraint
// decides the formula: an empty clause is false, an empty cube true.
//
// A unit is stored like any other constraint (irredundant, never watched)
// and is the reason of its root assignment.  It forces its literal to have
// a positive kind value: a unit clause (l) assigns l, a unit cube (l)
// assigns ~l.  Two complementary units resolve to the empty constraint of
// their kind.  Units of different kinds never meet on one variable: after
// reduction a unit clause is existential and a unit cube universal.
//
// Ids are those of the proof (ARCHITECTURE 8.2).  They are counted always
// and stored in the constraint only while a tracer is connected: the given
// original gets one, its reduction (if it lost a literal) the next, and the
// stored constraint carries the last one.
//
// Proof steps: 'o' for the original as given; if reduction shortened it,
// the reduced constraint derived from the original's id alone followed by
// the deletion of the original; the empty constraint derived from two
// complementary units (the new one first).  These steps are logged even
// after the formula was decided, as by the old solver.  'mark_garbage' is
// the single source of deletion steps for stored constraints.

#include "internal.hpp"
#include "proof.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

// 'move' is the derived constraint before reduction when reduction emptied
// it (all its literals are secondary); 'record_certificate' needs it.
void Internal::found_empty (Kind kind, std::span<const Lit> move) {
  LOG ("empty %s", kind == Kind::Clause ? "clause" : "cube");
  root_move.assign (move.begin (), move.end ());
  status = kind == Kind::Clause ? Status::False : Status::True;
  if (proof)
    proof->conclude (kind);
}

// Sorts, removes duplicates, and returns false if 'lits' contains a literal
// and its negation: such a clause is satisfied and such a cube falsified by
// every assignment.
static bool normalize (std::vector<Lit> &lits) {
  std::sort (lits.begin (), lits.end ());
  lits.erase (std::unique (lits.begin (), lits.end ()), lits.end ());
  for (size_t i = 1; i < lits.size (); i++)
    if (lits[i] == ~lits[i - 1])
      return false;
  return true;
}

void Internal::add_original (Kind kind, std::vector<Lit> &lits, int gate) {
  assert (!decision_level ());
  assert (!propagated);
  size_watches ();
  if (!normalize (lits))
    return;
  stats.originals[index (kind)]++;
  uint64_t id = next_id++;
  if (proof)
    proof->add_original (id, kind, gate, lits);
  const size_t size = prefix.reduced_size (lits, kind);
  if (!size && status == Status::Unknown)
    root_move = lits; // for 'found_empty' below
  if (size < lits.size ()) {
    const uint64_t original = id;
    id = next_id++;
    if (proof) {
      proof->add_derived (id, kind, {lits.data (), size}, {&original, 1});
      proof->delete_constraint (original, kind, lits);
    }
    lits.resize (size);
  }
  if (status != Status::Unknown)
    return;
  if (lits.empty ()) {
    const std::vector<Lit> move = std::move (root_move);
    found_empty (kind, move);
    return;
  }
  const Ref ref = new_constraint (id, kind, lits, false, 0);
  if (lits.size () > 1)
    return;
  const Lit unit = kind == Kind::Clause ? lits[0] : ~lits[0];
  if (!val (unit))
    assign (unit, ref);
  else if (val (unit) < 0) {
    // After reduction a unit clause is existential and a unit cube
    // universal, so the earlier unit has the same kind.
    const Constraint &earlier = deref (arena, reason (var (unit)));
    assert (earlier.kind () == kind);
    const uint64_t empty = next_id++;
    if (proof) {
      const uint64_t premises[] = {id, earlier.id ()};
      proof->add_derived (empty, kind, {}, premises);
    }
    found_empty (kind);
  }
}

Ref Internal::new_constraint (uint64_t id, Kind kind,
                              std::span<const Lit> lits, bool learnt,
                              uint32_t glue) {
  assert (!lits.empty ());
  // Units justify root assignments and later deletions (ARCHITECTURE
  // 11.1), so they are irredundant whatever produced them.
  if (lits.size () == 1)
    learnt = false;
  const Ref ref =
      alloc_constraint (arena, lits, kind, learnt, stored_id (id));
  Constraint &c = deref (arena, ref);
  assert (c.has_id () == (proof != nullptr));
  if (learnt)
    c.set_glue (glue);
  (learnt ? redundant : irredundant)[index (kind)].push_back (ref);
  if (lits.size () > 1)
    attach (ref);
  if (opts.subsume)
    mark_subsume (c);
  LOG (ref, "new");
  return ref;
}

void Internal::attach (Ref ref) {
  if (!connected)
    return;
  const Constraint &c = deref (arena, ref);
  assert (c.size () > 1);
  const Kind kind = c.kind ();
  watches (kind, watch_key (kind, c[0])).push (Watch{ref, c[1]});
  watches (kind, watch_key (kind, c[1])).push (Watch{ref, c[0]});
}

// Strict: searches both lists.  For a live constraint whose watched
// literals are about to change outside propagation; deleted constraints
// leave their lists lazily ('mark_garbage').
void Internal::detach (Ref ref) {
  if (!connected)
    return;
  const Constraint &c = deref (arena, ref);
  assert (c.size () > 1);
  const Kind kind = c.kind ();
  for (const Lit l : {c[0], c[1]}) {
    WatchList &list = watches (kind, watch_key (kind, l));
    const auto it =
        std::find_if (list.begin (), list.end (),
                      [ref] (const Watch &w) { return w.ref == ref; });
    assert (it != list.end ());
    list.erase (it);
  }
}

// Units are never deleted (ARCHITECTURE 4.3), so every deleted constraint
// is watched.
void Internal::mark_garbage (Ref ref) {
  Constraint &c = deref (arena, ref);
  assert (!c.garbage ());
  assert (c.size () > 1);
  LOG (ref, "delete");
  if (proof)
    proof->delete_constraint (c);
  if (elim_marking ())
    mark_elim_removed (c);
  c.set_garbage (true);
  arena.free (c.words ());
  if (!connected)
    return;
  const Kind kind = c.kind ();
  watches.smudge (kind, watch_key (kind, c[0]));
  watches.smudge (kind, watch_key (kind, c[1]));
}

// '--dropwatches' (CaDiCaL's 'reset_watches' around elimination and
// subsumption, "saves lots of memory").  A round at level 0 that does not
// propagate frees the watch lists and their tables before it allocates its
// own occurrence lists, so that the two are not in memory together; on a
// formula with 3 million gates the watches are 900 MB of 1834 MB.
void Internal::drop_watches () {
  assert (!decision_level () && connected);
  if (!opts.dropwatches)
    return;
  watches.release ();
  connected = false;
}

// The lists again, after the round: every live constraint of two or more
// literals is watched by its first two literals, as 'attach' would have
// done ('order_root_watches' chose them for the constraints the round
// added or shortened; the others still have the two they had).  Counted
// first, so that every list is allocated once at its size.  The lists come
// back in the order of the databases (irredundant before learnt), not in
// the order propagation had left them in, so the search after the round
// differs from that of '--no-dropwatches'.
void Internal::connect_watches () {
  if (connected)
    return;
  watches.resize (prefix.size ());
  const auto each = [&] (const auto &visit) {
    for (const Kind kind : {Kind::Clause, Kind::Cube})
      for (const auto *lists : {&irredundant, &redundant})
        for (const Ref ref : (*lists)[index (kind)])
          if (const Constraint &c = deref (arena, ref);
              !c.garbage () && c.size () > 1)
            visit (ref, c);
  };
  each ([&] (Ref, const Constraint &c) {
    const Kind kind = c.kind ();
    watches.count (kind, watch_key (kind, c[0]));
    watches.count (kind, watch_key (kind, c[1]));
  });
  watches.allocate_counted ();
  connected = true;
  each ([&] (Ref ref, const Constraint &) { attach (ref); });
}

// The caller keeps the watches consistent: either the first two literals
// stay, or the constraint is detached before and attached after.
void Internal::shrink_constraint (Ref ref, uint32_t new_size) {
  Constraint &c = deref (arena, ref);
  arena.free (c.shrink (new_size));
  LOG (ref, "shrunk");
}

} // namespace miniqu
