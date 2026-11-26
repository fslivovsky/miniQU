// Subsumption and strengthening (ROADMAP "M5+" item 1; CaDiCaL's
// 'subsume.cpp' gives the names and the shape).  Clauses and cubes go
// through the same code, one kind K at a time: a constraint only ever
// subsumes or strengthens a constraint of its own kind.  Off by default
// ('--subsume'); modes 0 and 1, QCIR and QDIMACS input.
//
// Subsumption.  If every literal of C occurs in D, then D is deleted.  A
// clause D is implied by the clause C, a cube D implies the cube C, so the
// formula keeps its value; and whenever D is unit or conflicting under an
// assignment, so is C, with the same literal (the literals of C that are
// not vanished are among those of D), so nothing that D propagated is lost
// (INV-COMPLETE).  An irredundant D is deleted only for an irredundant C: a
// learnt C may be deleted by 'reduce' later.  CaDiCaL turns such a C into
// an irredundant clause instead; here the two have different layouts in
// the arena, and the case is left out.
//
// Strengthening (self-subsuming resolution, '--subsumestr').  If C contains
// a literal p, D contains ~p, and every other literal of C occurs in D,
// then the resolvent of D and C on p is D without ~p.  It is reduced
// ('qreduce') and replaces D, which it subsumes.  The pivot has to be
// primary for K (an existential variable for clauses, a universal one for
// cubes), so that the step is a Q-resolution step in every mode.  The
// result has the status of D (irredundant or learnt): it is a consequence
// of the formula that implies D, so an irredundant D may be replaced by it
// whatever the status of C.
//
// A round ('subsume ()', CaDiCaL's 'subsume_round') is forward subsumption:
// the candidates of a kind are sorted by size and tried in that order, each
// against the smaller or equal ones tried before it, which are connected
// to one of their literals each (the one with the shortest list so far: a
// one-watch scheme).  The literals of the candidate are marked, the lists
// of its literals and of their negations are walked, and for each
// constraint found there 'subsume_check' tests whether all its literals
// are marked, at most one of them negated.  Candidates are the irredundant
// constraints and the learnt ones of tiers 1 and 2 (the ones 'reduce'
// keeps longest), with at most '--subsumeclslim' literals and without a
// literal assigned at the root: such a constraint is no reason, and root
// simplification shortens or deletes it anyway.  Only candidates with more
// than two literals are tried; binary ones only subsume and strengthen.
//
// Marks (CaDiCaL's 'subsume' flag).  'Flags::subsume' says that a variable
// occurs in a constraint added or shortened since the last complete round
// ('mark_subsume', called by 'new_constraint' and after every rewrite in
// place).  A constraint that subsumes or strengthens an older one is new or
// shortened itself, so all its variables are marked: a candidate needs two
// marked variables to be scheduled, only the lists of marked literals are
// walked, and only a constraint all of whose variables are marked is
// connected.  A complete round (every scheduled candidate of both kinds
// tried within '--subsumeticks') clears the marks and then marks the
// variables of the constraints it shortened.
//
// Schedule.  A round is due every 'subsumeint * (rounds + 1)' conflicts,
// the first one before the search, and also right before an elimination
// round if none ran since the last one ('Subsumer::since_elim'), so that
// elimination sees a database without subsumed constraints.  It runs at
// level 0 after a complete propagation, like elimination.  Deleted and
// shortened constraints mark their variables for elimination
// ('mark_elim_removed', 'mark_elim_literal').  With '--elimbackward' the
// resolvents of an elimination are used for backward subsumption and
// strengthening inside the elimination round ('elim_backward' in
// 'elim.cpp').
//
// Proof steps.  A subsumed constraint is deleted ('d', from
// 'mark_garbage').  A strengthened one is one derived step with the chain
// (D, C), followed by the deletion of D ('Proof::strengthen'); the checker
// resolves D with C on the single clashing literal and reduces.
//
// Left out: the list of binary constraints as literal pairs, sorting the
// literals of connected constraints by occurrences (the watches fix the
// first two positions here), a mark per constraint for candidates left
// over from an incomplete round (such a round keeps the variable marks, so
// the next one schedules the same candidates again), turning a learnt
// subsuming constraint irredundant, and an effort limit relative to the
// search.

#include "contract.hpp"
#include "internal.hpp"
#include "proof.hpp"

#include <algorithm>
#include <cassert>
#include <cinttypes>

namespace miniqu {

void Internal::init_subsume () { lim.subsume = 0; }

bool Internal::subsume_applies () const {
  return opts.subsume && opts.mode != 2;
}

bool Internal::subsuming () const {
  if (!subsume_applies ())
    return false;
  if (stats.conflicts >= lim.subsume)
    return true;
  return eliminating () && !subsumer.since_elim;
}

// The constraint was added or shortened.
void Internal::mark_subsume (const Constraint &c) {
  for (const Lit l : c)
    ftab[var (l)].subsume = true;
}

// Replaces 'ref' (D) by its resolvent with 'by' (C) on the variable of
// 'remove', a literal of D whose negation is in C while every other
// literal of C is in D; that is D without 'remove', reduced.  At level 0.
// 'subsumer.removed' holds the literals D lost.  A result of one literal
// is logged, queued in 'simplifier.units' and D is deleted; an empty one
// decides the formula.
Internal::Strengthening Internal::strengthen_by (Ref ref, Ref by,
                                                 Lit remove) {
  assert (!decision_level ());
  Constraint &d = deref (arena, ref);
  const Kind kind = d.kind ();
  assert (deref (arena, by).kind () == kind);
  assert (prefix.is_primary (kind, var (remove)));
  std::vector<Lit> &lits = subsumer.lits;
  std::vector<Lit> &removed = subsumer.removed;
  std::vector<uint64_t> &ids = subsumer.chain;
  lits.clear ();
  ids.clear ();
  for (const Lit l : d)
    if (l != remove)
      lits.push_back (l);
  assert (lits.size () + 1 == d.size ());
  if (proof) {
    ids.push_back (d.id ());
    ids.push_back (deref (arena, by).id ());
  }
  if (prefix.reduces_to_empty (lits, kind))
    subsumer.move = lits; // for 'found_empty' below
  prefix.qreduce (lits, kind);
  removed.clear ();
  for (const Lit l : d)
    if (std::find (lits.begin (), lits.end (), l) == lits.end ())
      removed.push_back (l);
  stats.strengthened[index (kind)]++;
  stats.strengthenedlits[index (kind)] += (int64_t) removed.size ();
  LOG (ref, "strengthening to %zu literals", lits.size ());
  const bool learnt = d.redundant ();
  if (lits.size () < 2) {
    const uint64_t id = next_id++;
    if (proof)
      proof->add_derived (id, kind, lits, ids);
    if (lits.empty ()) {
      found_empty (kind, subsumer.move);
      return Strengthening::Empty;
    }
    stats.subsumeunits++;
    mark_garbage (ref); // marks the variables for elimination
    simplifier.units.push_back ({id, kind, lits[0]});
    return Strengthening::Unit;
  }
  if (proof)
    proof->strengthen (d, lits, ids);
  else
    next_id++;
  detach (ref);
  std::copy (lits.begin (), lits.end (), d.begin ());
  const uint32_t size = static_cast<uint32_t> (lits.size ());
  shrink_constraint (ref, size);
  if (learnt) {
    d.set_glue (std::min (d.glue (), size));
    d.set_used (std::max (d.used (), deref (arena, by).used ()));
    d.set_vivified (false);
  }
  watch_root_simplified (ref);
  mark_subsume (d);
  if (elim_marking ())
    for (const Lit l : removed)
      mark_elim_literal (l, learnt);
  return Strengthening::Shortened;
}

// Whether all literals of 'subsuming' are marked, at most one of them
// negated: 1 if it subsumes the marked candidate, -1 if it strengthens it
// ('flipped' is then the literal of 'subsuming' whose negation the
// candidate loses), 0 otherwise.
int Internal::subsume_check (const Constraint &subsuming, Lit &flipped) {
  stats.subsumechecks++;
  flipped = lit_undef;
  for (const Lit l : subsuming) {
    subsumer.ticks++;
    if (subsumer.marks[index (l)])
      continue;
    if (!subsumer.marks[index (~l)] || flipped != lit_undef)
      return 0;
    flipped = l;
  }
  if (flipped == lit_undef)
    return 1;
  if (!opts.subsumestr ||
      !prefix.is_primary (subsuming.kind (), var (flipped)))
    return 0;
  return -1;
}

// Forward check of one candidate against the connected constraints.  True
// if it was deleted (subsumed, or strengthened to a unit) or the formula
// was decided.
bool Internal::try_to_subsume (Ref ref) {
  const Constraint &c = deref (arena, ref);
  const Kind kind = c.kind ();
  stats.subsumetried[index (kind)]++;
  for (const Lit l : c)
    subsumer.marks[index (l)] = 1;
  subsumer.ticks += c.size ();
  Ref by = Ref::none;
  Lit flipped = lit_undef;
  int found = 0;
  for (const Lit l : c) {
    if (found)
      break;
    if (!ftab[var (l)].subsume)
      continue;
    for (const Lit key : {l, ~l}) {
      if (found)
        break;
      for (uint32_t i = subsumer.head[index (key)]; i && !found;
           i = subsumer.links[i - 1].next) {
        subsumer.ticks++;
        const Ref other = subsumer.links[i - 1].ref;
        const Constraint &e = deref (arena, other);
        assert (!e.garbage () && other != ref && e.size () <= c.size ());
        const int result = subsume_check (e, flipped);
        // An irredundant constraint is not deleted for a learnt one.
        if (result > 0 && !c.redundant () && e.redundant ())
          continue;
        if (result) {
          found = result;
          by = other;
        }
      }
    }
  }
  for (const Lit l : c)
    subsumer.marks[index (l)] = 0;
  if (!found)
    return false;
  if (found > 0) {
    LOG (ref, "subsumed");
    stats.subsumed[index (kind)]++;
    assert (!is_root_reason (ref));
    mark_garbage (ref);
    return true;
  }
  if (strengthen_by (ref, by, ~flipped) != Strengthening::Shortened)
    return true;
  subsumer.shrunken.push_back (ref);
  return false;
}

// Connects a constraint that was tried to its literal with the shortest
// list (ties: fewest occurrences in the schedule), if all its variables
// are marked and that list is not longer than '--subsumeocclim'.
void Internal::subsume_connect (Ref ref) {
  const Constraint &c = deref (arena, ref);
  Lit best = lit_undef;
  for (const Lit l : c) {
    if (!ftab[var (l)].subsume)
      return;
    if (best == lit_undef) {
      best = l;
      continue;
    }
    const uint32_t a = subsumer.length[index (l)];
    const uint32_t b = subsumer.length[index (best)];
    if (a < b || (a == b &&
                  subsumer.noccs[index (l)] < subsumer.noccs[index (best)]))
      best = l;
  }
  subsumer.ticks += c.size ();
  if (subsumer.length[index (best)] > (uint32_t) opts.subsumeocclim)
    return;
  subsumer.links.push_back ({ref, subsumer.head[index (best)]});
  subsumer.head[index (best)] = (uint32_t) subsumer.links.size ();
  subsumer.length[index (best)]++;
}

// The round for one kind.  True if every scheduled candidate was tried.
bool Internal::subsume_kind (Kind kind) {
  std::vector<Subsumer::Scheduled> &schedule = subsumer.schedule;
  schedule.clear ();
  const size_t k = index (kind);
  for (const auto *lists : {&irredundant, &redundant})
    for (const Ref ref : (*lists)[k]) {
      const Constraint &c = deref (arena, ref);
      if (c.garbage () || c.size () < 2 ||
          c.size () > (uint32_t) opts.subsumeclslim)
        continue;
      if (c.redundant () && c.glue () > (uint32_t) tiers.tier2[k])
        continue;
      subsumer.ticks += c.size ();
      bool fixed = false;
      int marked = 0;
      for (const Lit l : c) {
        fixed |= val (l) != 0;
        marked += ftab[var (l)].subsume;
      }
      if (fixed || marked < 2)
        continue;
      schedule.push_back ({c.size (), ref});
      for (const Lit l : c)
        subsumer.noccs[index (l)]++;
    }
  std::stable_sort (
      schedule.begin (), schedule.end (),
      [] (const Subsumer::Scheduled &a, const Subsumer::Scheduled &b) {
        return a.size < b.size;
      });
  size_t tried = 0;
  for (const Subsumer::Scheduled &s : schedule) {
    if (status != Status::Unknown || subsumer.ticks >= opts.subsumeticks)
      break;
    tried++;
    if (s.size > 2 && try_to_subsume (s.ref))
      continue;
    subsume_connect (s.ref);
  }
  const bool finished =
      tried == schedule.size () && status == Status::Unknown;
  // Not through the literals of the schedule: strengthening removed some.
  std::fill (subsumer.noccs.begin (), subsumer.noccs.end (), 0u);
  std::fill (subsumer.head.begin (), subsumer.head.end (), 0u);
  std::fill (subsumer.length.begin (), subsumer.length.end (), 0u);
  subsumer.links.clear ();
  schedule.clear ();
  return finished;
}

// One round; returns a root conflict or 'Ref::none'.  Every exit leaves
// 'subsuming ()' false.
Ref Internal::subsume () {
  PROFILE_SCOPE (subsume);
  assert (!decision_level () && propagated == trail.size ());
  assert (subsume_applies () && simplifier.units.empty ());
  stats.subsumerounds++;
  const size_t literals = 2 * (size_t) prefix.size ();
  subsumer.ticks = 0;
  subsumer.head.assign (literals, 0);
  subsumer.length.assign (literals, 0);
  subsumer.noccs.assign (literals, 0);
  subsumer.marks.assign (literals, 0);
  subsumer.shrunken.clear ();
  const int64_t before[2] = {stats.subsumed[0] + stats.subsumed[1],
                             stats.strengthened[0] + stats.strengthened[1]};
  bool finished = true;
  for (const Kind kind : {Kind::Clause, Kind::Cube})
    if (status == Status::Unknown)
      finished &= subsume_kind (kind);
  if (finished && status == Status::Unknown) {
    for (Flags &f : ftab)
      f.subsume = false;
    for (const Ref ref : subsumer.shrunken)
      if (const Constraint &c = deref (arena, ref); !c.garbage ())
        mark_subsume (c);
  }
  std::vector<uint32_t> ().swap (subsumer.head);
  std::vector<uint32_t> ().swap (subsumer.length);
  std::vector<uint32_t> ().swap (subsumer.noccs);
  std::vector<int8_t> ().swap (subsumer.marks);
  std::vector<Subsumer::Link> ().swap (subsumer.links);
  std::vector<Subsumer::Scheduled> ().swap (subsumer.schedule);
  std::vector<Ref> ().swap (subsumer.shrunken);
  const int64_t subsumed =
      stats.subsumed[0] + stats.subsumed[1] - before[0];
  const int64_t strengthened =
      stats.strengthened[0] + stats.strengthened[1] - before[1];
  if (subsumed || strengthened)
    for (Kind kind : {Kind::Clause, Kind::Cube})
      for (auto *lists : {&irredundant, &redundant})
        std::erase_if ((*lists)[index (kind)], [&] (Ref ref) {
          return deref (arena, ref).garbage ();
        });
  subsumer.since_elim = true;
  lim.subsume = stats.conflicts +
                (int64_t) opts.subsumeint * (stats.subsumerounds + 1);
  if (status != Status::Unknown) {
    simplifier.units.clear ();
    return Ref::none;
  }
  const Ref conflict = add_root_units ();
  PHASE ("subsume", stats.subsumerounds,
         "subsumed %" PRId64 " strengthened %" PRId64 "%s", subsumed,
         strengthened, finished ? "" : " (incomplete)");
  if (conflict != Ref::none)
    return conflict;
  if (collecting ())
    garbage_collect ();
  else if (assertions_enabled || opts.check)
    check_invariants ();
  return Ref::none;
}

} // namespace miniqu
