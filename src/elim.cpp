// Bounded variable elimination (ROADMAP "M3 execution plan", M3.2-M3.4;
// ARCHITECTURE 10, 11.1).  CaDiCaL's 'elim.cpp' gives the names and the
// shape (occurrence lists, a bound on the resolvents, resolvents added
// before the parents are deleted); clauses and cubes take the same code
// path over 'Kind'.  Initial version: QCIR input ('complete') in modes 0
// and 1 only, off by default ('--elim').
//
// Schedule.  'lim.elim' is the conflict count at which the next round is
// due: 0 with '--elimpre' (the preprocessing round before the first
// decision), else '--elimint'.  Every round, whatever its outcome, sets it
// to 'elimint * (rounds + 1)' conflicts ahead with '--eliminp' (an
// arithmetically growing interval, as in CaDiCaL) and to never without, so
// 'eliminating ()' is false right after a round and the loop cannot spin.
// A due round may do nothing: it is skipped when no variable is marked
// and, with '--elimeffort', delayed when its budget does not cover the
// occurrence lists (both below and at 'eliminate ()'); it counts as a round
// of the schedule all the same.
//
// Marks ('--elimmark', as the 'elim' flag of CaDiCaL).  A pass tries only
// marked variables.  All are marked before the first round and whenever
// the bound grows; an attempt clears the mark, and the deletion of a
// constraint marks its variables again ('mark_elim_removed', called by
// 'mark_garbage').  With '--no-elimmark' every pass tries every candidate.
//
// Level 0.  A round runs at level 0 with propagation complete.  When one is
// due above level 0 the search loop backtracks to level 0 and the next
// iterations propagate and simplify at the root before the round.  That
// backtrack is as safe as the one of 'restart ()': both are taken in the
// same state (the propagation of this iteration found no conflict, so no
// lone literal is pending, and nothing else is in flight), 'restart ()'
// backtracks to level 0 itself whenever trail reuse keeps nothing, and
// 'backtrack' undoes assignments only, putting decision variables back
// into their heaps and, with '--dl', moving the trail head of 'depend.cpp'
// back so that waiting variables become eligible again as after a restart.
// A backtrack derives nothing, so it has no proof step.
//
// Learnt constraints.  E2 and E3 below are checked against every live
// constraint at the time of the round, learnt ones included.  Learnt
// 'K'-constraints containing 'x' are never parents; they are deleted with
// 'x' ('elimlearnt').  None of them is a reason: 'x' is unassigned and a
// root reason has no unassigned literal.  Constraints learnt later never
// mention 'x', since no live constraint does and 'x' stays unassigned
// ('learn.cpp' asserts it).  Dependencies ('--dl') are between a decision
// variable and a secondary variable of a learnt constraint, and a gate
// variable is primary wherever it occurs, so none should mention 'x'; a
// round that finds one all the same resets the dependencies, since a
// variable waiting for 'x' would never become eligible again.
//
// Classes (D) and (R).  A variable 'x' is eliminated in the kind 'K' in
// which it is primary (an existential variable by clause resolution, a
// universal one by cube resolution; 'K'' is the other kind): every
// non-tautological resolvent on 'x' of two irredundant 'K'-constraints is
// derived (D: two parents with the single clash on 'x', then 'qreduce'),
// and then every live 'K'-constraint containing 'x', irredundant or
// learnt, is deleted (R).  Afterwards no live constraint contains 'x'.
//
// Side conditions.
//
//  E1 (candidate).  'x' is not a decision variable (in QCIR input: a gate
//     variable), not eliminated, not assigned, has no unit resolvent
//     pending in this round, and elimination in 'K' is switched on
//     ('--elimclause', '--elimcube').  Since 'x' is never decided and no
//     constraint is left to propagate it, no heap, block counter or
//     certificate changes.
//  E2 (other kind).  No live 'K''-constraint, original or learnt, contains
//     'x': an existential variable is eliminated only if it occurs in no
//     cube, a universal one only if it occurs in no clause.
//  E3 (rightmost).  In every live 'K'-constraint containing 'x', learnt
//     ones included, no literal has a block depth greater than that of 'x'
//     (the same block is allowed).
//  E4 (bound).  At most '--elimocclim' irredundant occurrences per
//     polarity; every resolvent (non-tautological, after 'qreduce') has at
//     most '--elimclslim' literals; there are at most as many resolvents as
//     irredundant parents plus 'eliminator.bound' (below).  A resolvent
//     containing a literal and its negation (any variable) is dropped: such
//     a clause is satisfied and such a cube falsified by every assignment.
//
// Subsumed resolvents ('--elimsubsume', M3-T4).  A resolvent 'R' (after
// 'qreduce') all of whose literals occur in a live irredundant
// 'K'-constraint 'D' that is not a parent, or in an earlier resolvent of
// the same candidate, is dropped: not stored, not logged, no id, and not
// counted against the bound ('elimsubsumed').  'D' never contains 'x' (the
// literal of 'x' is not in 'R'), so it survives the elimination of 'x';
// learnt constraints are never used as 'D', since 'reduce' may delete them.
// Sound: nothing is added, so INV-DERIVED and the proof are untouched (a
// dropped resolvent has no proof step at all); INV-COMPLETE holds because
// 'D' (or the earlier resolvent, which is stored) propagates whenever 'R'
// would, and is irredundant.  Dropping 'R' is the same as adding it and
// removing it at once by subsumption with an irredundant constraint, so the
// rounds after it start from an ordinary formula state.  'D' is looked up
// in the occurrence lists of the round, which hold the literals of
// candidates only, and only in the shortest non-empty list of a literal of
// 'R' (walking all of them used up the tick budget on the corpus, see
// STATUS.md M3-T4): a 'D' without that literal, or without any candidate
// literal, is not found, a missed opportunity and not an error.  The visits
// count as ticks.
//
// Growing bound ('--elimboundmax', as 'elimboundmin/max' in CaDiCaL).  The
// first round sets 'eliminator.bound' to '--elimbound'.  A round whose
// passes reached a fixpoint (the last one eliminated nothing) within
// '--elimticks' raises it to '2 * bound' (to 1 from 0), at most to
// '--elimboundmax', for the next round; a round never loops over bounds.
//
// Root-assigned literals are ordinary literals here: a root-disabled
// parent takes part and resolvents keep root-vanished literals, because no
// unit justifies their removal (INV-DERIVED, M3.3).  Root simplification
// removes them later where a unit exists.
//
// Results.  A resolvent of two or more literals is stored irredundant and
// watched by its best literals under the root assignment
// ('order_root_watches'), with the propagation head rewound if it is unit
// or conflicting there ('rewind_root_propagation'), as in 'simplify.cpp'.
// A unit resolvent is logged at once and stored and assigned after the
// round through 'simplifier.units' and 'add_root_units', which may find a
// root conflict; its variable is no candidate for the rest of the round.
// The empty resolvent decides the formula and ends the round.
//
// Proof steps.  Each resolvent is one derived step whose chain is the ids
// of its two parents (the checker's rule: one clashing literal, then
// reduction); every derived step of a variable comes before its deletions,
// which are the 'd' steps of 'mark_garbage'.  Ids are consumed with and
// without a proof alike.
//
// The occurrence lists are built per round, for the literals of candidates
// only, in one array ('Occs' in 'elim.hpp'), and dropped at its end; the
// watches stay (no occurrence mode).  No 'Constraint &' is held across
// 'new_constraint' and no arena collection happens inside a round.
// Candidates are visited from the innermost variable outwards, in passes
// repeated while a pass eliminated something and the round's budget of
// literal visits lasts ('--elimticks'; for inprocessing rounds a share of
// the search ticks, '--elimeffort').
//
// Left out (ROADMAP "Left for later"): decision variables, QDIMACS input,
// mode 2, gate-aware elimination, backward subsumption and strengthening
// with the resolvents, counting the resolvents before building them,
// candidates ordered by cost and occurrence mode.

#include "contract.hpp"
#include "internal.hpp"
#include "proof.hpp"

#include <algorithm>
#include <cassert>
#include <cinttypes>
#include <cstdint>

namespace miniqu {

// The kind in which a variable is primary.
static Kind primary_kind (Quant quant) {
  return quant == Quant::Exists ? Kind::Clause : Kind::Cube;
}

void Internal::init_elim () {
  if (opts.elimpre)
    lim.elim = 0;
  else
    lim.elim = opts.eliminp ? opts.elimint : INT64_MAX;
}

bool Internal::eliminating () const {
  if (!opts.elim || (!opts.elimclause && !opts.elimcube))
    return false;
  if (opts.mode == 2 || !complete)
    return false;
  return stats.conflicts >= lim.elim;
}

// E1.  Only valid inside a round ('pending' is sized there).
bool Internal::elim_candidate (Var v) const {
  if (prefix.vars[v].decision || ftab[v].eliminated)
    return false;
  if (val (mk_lit (v)) || eliminator.pending[v])
    return false;
  return primary_kind (prefix.quant (v)) == Kind::Clause ? opts.elimclause
                                                         : opts.elimcube;
}

// Whether deletions set the marks: elimination applies and '--elimmark'.
bool Internal::elim_marking () const {
  return opts.elim && opts.elimmark && complete && opts.mode != 2;
}

// A constraint is deleted ('mark_garbage'): its variables may have become
// eliminable.  Every side condition of a variable 'x' fails on constraints
// containing 'x' only, and adding constraints never makes one hold, so a
// failed attempt can only succeed after such a deletion (or with a larger
// bound, 'mark_elim_all').  One exception is accepted, as in CaDiCaL: a
// constraint stored later may subsume a resolvent on 'x' ('--elimsubsume')
// and bring 'x' within the bound; 'x' is then tried again only when it is
// marked for another reason.  Learnt constraints matter for E2 and E3
// only, so their deletion marks only variables whose last attempt failed
// on a learnt constraint.
void Internal::mark_elim_removed (const Constraint &c) {
  const bool learnt = c.redundant ();
  for (const Lit l : c)
    mark_elim_literal (l, learnt);
}

// The literal left a constraint (deleted, or shortened in place by
// 'strengthen_by').
void Internal::mark_elim_literal (Lit l, bool learnt) {
  const Var v = var (l);
  Flags &f = ftab[v];
  if (f.elim || f.eliminated || prefix.vars[v].decision)
    return;
  if (learnt && !f.elimblocked)
    return;
  if (val (l) && !level (v))
    return;
  f.elim = true;
  eliminator.scheduled++;
}

// Marks every variable that may be a candidate (before the first round and
// when the bound grew), and counts the marks.
void Internal::mark_elim_all () {
  eliminator.scheduled = 0;
  for (Var v = 0; v < prefix.size (); v++) {
    Flags &f = ftab[v];
    f.elim = !prefix.vars[v].decision && !f.eliminated;
    eliminator.scheduled += f.elim;
  }
}

// Occurrence lists of both kinds, irredundant and learnt constraints, in
// two passes: the lengths, then the references.  Only the second pass
// counts ticks, so that a round spends its budget as it did with one pass
// ('--no-elimmark' is the search of the version before the marks).  False
// if the lists do not fit 32-bit offsets.
bool Internal::connect_occs () {
  Occs &occs = eliminator.occs;
  const size_t slots = 4 * (size_t) prefix.size ();
  occs.start.assign (slots, 0);
  occs.len.assign (slots, 0);
  const auto each = [&] (bool count, const auto &visit) {
    for (Kind kind : {Kind::Clause, Kind::Cube})
      for (const auto *lists : {&irredundant, &redundant})
        for (const Ref ref : (*lists)[index (kind)]) {
          const Constraint &c = deref (arena, ref);
          if (c.garbage ())
            continue;
          if (count)
            eliminator.ticks += c.size ();
          for (const Lit l : c)
            if (elim_candidate (var (l)))
              visit (Occs::slot (kind, l), ref);
        }
  };
  each (false, [&] (size_t s, Ref) { occs.len[s]++; });
  uint64_t total = 0;
  for (size_t s = 0; s < slots; s++) {
    occs.start[s] = (uint32_t) total;
    total += occs.len[s];
    occs.len[s] = 0;
  }
  if (total >= Occs::moved)
    return false;
  occs.refs.resize (total);
  each (true, [&] (size_t s, Ref ref) {
    occs.refs[occs.start[s] + occs.len[s]++] = ref;
  });
  return true;
}

// Drops the garbage references of a list.
void Internal::flush_occs (Kind kind, Lit l) {
  const std::span<Ref> occs = eliminator (kind, l);
  eliminator.ticks += (int64_t) occs.size ();
  const auto end =
      std::remove_if (occs.begin (), occs.end (), [&] (Ref ref) {
        return deref (arena, ref).garbage ();
      });
  eliminator.occs.truncate (kind, l, (size_t) (end - occs.begin ()));
}

// Whether an earlier resolvent of this candidate has all its literals
// marked ('marked' holds the 'size' literals of the new one).
bool Internal::subsumed_by_resolvent (size_t size) {
  for (const Resolvent &r : eliminator.resolvents) {
    if (r.size > size)
      continue;
    eliminator.ticks += r.size;
    const Lit *begin = eliminator.lits.data () + r.offset;
    if (std::all_of (begin, begin + r.size,
                     [&] (Lit l) { return eliminator.marked[index (l)]; }))
      return true;
  }
  return false;
}

// Whether a live irredundant 'kind'-constraint in the shortest non-empty
// occurrence list of a literal of 'lits' has all its literals marked.
// Lists of non-candidate literals are empty or stale (without the later
// resolvents), which only misses opportunities; a parent never qualifies,
// since its pivot is unmarked.
bool Internal::subsumed_by_stored (Kind kind, std::span<const Lit> lits) {
  std::span<Ref> shortest;
  for (const Lit l : lits) {
    const std::span<Ref> occs = eliminator (kind, l);
    eliminator.ticks++;
    if (!occs.empty () &&
        (shortest.empty () || occs.size () < shortest.size ()))
      shortest = occs;
  }
  for (const Ref ref : shortest) {
    eliminator.ticks++;
    const Constraint &d = deref (arena, ref);
    if (d.garbage () || d.redundant () || d.size () > lits.size ())
      continue;
    eliminator.ticks += d.size ();
    if (std::all_of (d.begin (), d.end (),
                     [&] (Lit k) { return eliminator.marked[index (k)]; }))
      return true;
  }
  return false;
}

// '--elimsubsume': whether the resolvent 'lits' is subsumed by an earlier
// resolvent of the candidate or by a stored irredundant constraint.
bool Internal::resolvent_subsumed (Kind kind, std::span<const Lit> lits) {
  for (const Lit l : lits)
    eliminator.marked[index (l)] = 1;
  const bool subsumed = subsumed_by_resolvent (lits.size ()) ||
                        subsumed_by_stored (kind, lits);
  for (const Lit l : lits)
    eliminator.marked[index (l)] = 0;
  return subsumed;
}

// The resolvent of 'c' (containing 'pivot', whose other literals are
// marked) and 'd' (containing '~pivot'), stored unless tautological or
// subsumed.  False if it is too large (E4).
bool Internal::resolve (Kind kind, Ref c_ref, Ref d_ref, Lit pivot) {
  std::vector<Lit> &lits = eliminator.resolvent;
  const Constraint &c = deref (arena, c_ref);
  const Constraint &d = deref (arena, d_ref);
  eliminator.ticks += c.size () + d.size ();
  lits.clear ();
  for (const Lit l : c)
    if (l != pivot)
      lits.push_back (l);
  for (const Lit l : d) {
    if (l == ~pivot)
      continue;
    if (eliminator.marks[index (~l)])
      return true;
    if (!eliminator.marks[index (l)])
      lits.push_back (l);
  }
  if (prefix.reduces_to_empty (lits, kind))
    eliminator.move = lits; // for 'found_empty' (certificate)
  prefix.qreduce (lits, kind);
  if (opts.elimsubsume && resolvent_subsumed (kind, lits)) {
    stats.elimsubsumed[index (kind)]++;
    return true;
  }
  if (lits.size () > (size_t) opts.elimclslim)
    return false;
  eliminator.resolvents.push_back (
      {eliminator.lits.size (), (uint32_t) lits.size (), {c_ref, d_ref}});
  eliminator.lits.insert (eliminator.lits.end (), lits.begin (),
                          lits.end ());
  return true;
}

// E4: all resolvents of the irredundant occurrences of 'x' into the
// buffers of 'eliminator', or false if the bound is exceeded.
bool Internal::find_resolvents (Kind kind, Var x) {
  const Lit pivot = mk_lit (x);
  const std::span<Ref> pos = eliminator (kind, pivot);
  const std::span<Ref> neg = eliminator (kind, ~pivot);
  const auto irredundant_count = [&] (std::span<Ref> occs) {
    return (size_t) std::count_if (occs.begin (), occs.end (), [&] (Ref r) {
      return !deref (arena, r).redundant ();
    });
  };
  const size_t p = irredundant_count (pos), n = irredundant_count (neg);
  if (p > (size_t) opts.elimocclim || n > (size_t) opts.elimocclim)
    return false;
  const size_t limit = p + n + (size_t) eliminator.bound;
  eliminator.lits.clear ();
  eliminator.resolvents.clear ();
  std::vector<int8_t> &marks = eliminator.marks;
  for (const Ref c_ref : pos) {
    const Constraint &c = deref (arena, c_ref);
    if (c.redundant ())
      continue;
    for (const Lit l : c)
      if (l != pivot)
        marks[index (l)] = 1;
    bool within = true;
    for (const Ref d_ref : neg) {
      if (deref (arena, d_ref).redundant ())
        continue;
      if (!resolve (kind, c_ref, d_ref, pivot) ||
          eliminator.resolvents.size () > limit) {
        within = false;
        break;
      }
    }
    for (const Lit l : c)
      marks[index (l)] = 0;
    if (!within)
      return false;
  }
  return true;
}

// Stores the resolvents found for 'x' (derived before anything is deleted).
void Internal::add_resolvents (Kind kind, Var x) {
  (void) x;
  for (const Resolvent &r : eliminator.resolvents) {
    const uint64_t id = next_id++;
    uint64_t parents[2] = {0, 0};
    if (proof)
      for (int i = 0; i < 2; i++)
        parents[i] = deref (arena, r.parents[i]).id ();
    const std::span<Lit> lits{eliminator.lits.data () + r.offset, r.size};
    LOG ("resolvent %" PRIu64 " of %zu literals on %u", id, lits.size (),
         x + 1);
    if (lits.size () < 2) {
      if (proof)
        proof->add_derived (id, kind, lits, parents);
      if (lits.empty ()) {
        found_empty (kind, eliminator.move);
        return;
      }
      stats.elimunits++;
      simplifier.units.push_back ({id, kind, lits[0]});
      eliminator.pending[var (lits[0])] = 1;
      continue;
    }
    order_root_watches (kind, lits);
    const Ref ref = new_constraint (id, kind, lits, false, 0);
    if (proof)
      proof->add_derived (deref (arena, ref), parents);
    rewind_root_propagation (ref);
    for (const Lit l : lits)
      if (elim_candidate (var (l)))
        eliminator.occs.push (kind, l, ref);
    if (subsume_applies () && opts.elimbackward)
      eliminator.backward.push_back (ref);
    stats.resolvents[index (kind)]++;
  }
}

// E1-E4 for 'x', then the elimination.  True if it was eliminated (or the
// formula was decided by an empty resolvent).
bool Internal::try_eliminate (Var x) {
  if (!elim_candidate (x))
    return false;
  stats.elimtried++;
  const Kind kind = primary_kind (prefix.quant (x));
  const Lit pivot = mk_lit (x);
  Flags &flags = ftab[x];
  flags.elimblocked = false;
  for (const Lit l : {pivot, ~pivot})
    for (const Kind k : {Kind::Clause, Kind::Cube})
      flush_occs (k, l);
  for (const Lit l : {pivot, ~pivot})
    if (const std::span<Ref> occs = eliminator (other (kind), l);
        !occs.empty ()) {
      flags.elimblocked = deref (arena, occs[0]).redundant ();
      stats.elimblockedother++;
      return false;
    }
  const uint32_t depth = prefix.depth (x);
  for (const Lit p : {pivot, ~pivot})
    for (const Ref ref : eliminator (kind, p)) {
      const Constraint &c = deref (arena, ref);
      eliminator.ticks += c.size ();
      for (const Lit l : c)
        if (prefix.depth (var (l)) > depth) {
          flags.elimblocked = c.redundant ();
          stats.elimblockedright++;
          return false;
        }
    }
  if (!find_resolvents (kind, x)) {
    stats.elimblockedbound++;
    return false;
  }
  LOG ("eliminating %u with %zu resolvents", x + 1,
       eliminator.resolvents.size ());
  add_resolvents (kind, x);
  if (status != Status::Unknown)
    return true;
  if (assertions_enabled)
    check_elimination_owner (x);
  // Set before the deletions, which must not mark 'x' again.
  flags.eliminated = true;
  // Each contains the unassigned 'x', so it is neither a unit nor a
  // reason.  The lists of 'x' got no resolvent, but 'add_resolvents' may
  // have moved them, so they are looked up here.
  for (const Lit p : {pivot, ~pivot})
    for (const Ref ref : eliminator (kind, p)) {
      const Constraint &c = deref (arena, ref);
      assert (!c.garbage ());
      assert (!is_root_reason (ref));
      if (c.redundant ())
        stats.elimlearnt[index (kind)]++;
      else
        stats.elimdeleted[index (kind)]++;
      mark_garbage (ref);
    }
  eliminator.occs.truncate (kind, pivot, 0);
  eliminator.occs.truncate (kind, ~pivot, 0);
  if (opts.dl && (!depend.on[x].empty () || !depend.watching[x].empty ()))
    eliminator.dependent = true;
  elim_backward_queue ();
  stats.eliminated[index (kind)]++;
  return true;
}

// Backward subsumption and strengthening with one constraint C, a
// resolvent or a constraint this function shortened ('--elimbackward';
// CaDiCaL's 'elim_backward_clause').  Every constraint D of the kind of C
// that contains all literals of C is deleted, and one that contains all of
// them but one, and that one negated, loses the negated literal
// ('strengthen_by' in 'subsume.cpp', which has the side conditions and the
// proof steps).  The constraints D are those in the occurrence list of the
// candidate literal of C with the shortest list: the lists of candidate
// literals hold every live constraint with that literal, learnt ones
// included.  As in CaDiCaL a D that contains that literal negated is not
// found.  A root reason is left alone.  A shortened D leaves the lists of
// the literals it lost and is queued itself.
void Internal::elim_backward (Ref ref) {
  const Constraint &c = deref (arena, ref);
  if (c.garbage ())
    return;
  const Kind kind = c.kind ();
  const size_t k = index (kind);
  const uint32_t size = c.size ();
  const bool learnt = c.redundant ();
  Lit best = lit_undef;
  size_t shortest = 0;
  for (const Lit l : c) {
    eliminator.ticks++;
    if (!elim_candidate (var (l)))
      continue;
    const size_t length = eliminator (kind, l).size ();
    if (best == lit_undef || length < shortest)
      best = l, shortest = length;
  }
  if (best == lit_undef || shortest > (size_t) opts.elimocclim)
    return;
  flush_occs (kind, best);
  std::vector<int8_t> &marked = eliminator.marked;
  for (const Lit l : c)
    marked[index (l)] = 1;
  for (size_t i = 0;
       i < eliminator (kind, best).size () && status == Status::Unknown;
       i++) {
    const Ref other = eliminator (kind, best)[i];
    if (other == ref)
      continue;
    const Constraint &d = deref (arena, other);
    eliminator.ticks++;
    if (d.garbage () || d.size () < size)
      continue;
    eliminator.ticks += d.size ();
    uint32_t found = 0;
    Lit negated = lit_undef;
    bool failed = false;
    for (const Lit l : d) {
      if (marked[index (l)])
        found++;
      else if (marked[index (~l)]) {
        if (negated != lit_undef) {
          failed = true;
          break;
        }
        negated = l;
        found++;
      }
    }
    if (failed || found != size || is_root_reason (other))
      continue;
    if (negated == lit_undef) {
      // An irredundant constraint is not deleted for a learnt one.
      if (!d.redundant () && learnt)
        continue;
      LOG (other, "backward subsumed");
      stats.elimbwsubsumed[k]++;
      mark_garbage (other);
      continue;
    }
    if (!opts.subsumestr || !prefix.is_primary (kind, var (negated)))
      continue;
    stats.elimbwstrengthened[k]++;
    switch (strengthen_by (other, ref, negated)) {
    case Strengthening::Empty:
      break;
    case Strengthening::Unit:
      stats.elimunits++;
      eliminator.pending[var (subsumer.lits[0])] = 1;
      break;
    case Strengthening::Shortened:
      for (const Lit l : subsumer.removed) {
        eliminator.occs.remove (kind, l, other);
        if (l == best)
          i--;
      }
      eliminator.backward.push_back (other);
      break;
    }
  }
  for (const Lit l : deref (arena, ref))
    marked[index (l)] = 0;
}

void Internal::elim_backward_queue () {
  std::vector<Ref> &queue = eliminator.backward;
  for (size_t i = 0; i < queue.size (); i++) {
    if (status != Status::Unknown || eliminator.ticks >= eliminator.budget)
      break;
    elim_backward (queue[i]);
  }
  queue.clear ();
}

// After a round at a fixpoint within its budget: the next round may add
// more (0, 1, 2, 4, ... up to '--elimboundmax'; never lowers the bound).
void Internal::grow_elim_bound () {
  int64_t &bound = eliminator.bound;
  if (bound >= opts.elimboundmax)
    return;
  bound = std::min<int64_t> (bound ? 2 * bound : 1, opts.elimboundmax);
  mark_elim_all ();
  LOG ("elimination bound raised to %" PRId64, bound);
}

// The next round: 'elimint * (rounds + 1)' conflicts ahead, or never.
void Internal::schedule_elim () {
  lim.elim = opts.eliminp ? stats.conflicts + (int64_t) opts.elimint *
                                                  (stats.elimrounds + 1)
                          : INT64_MAX;
}

// Drops the occurrence lists and the garbage references of the databases
// ('reduce.cpp' and 'check.cpp' expect lists without garbage), resets the
// dependencies if one mentions an eliminated variable, and schedules the
// next round.
void Internal::finish_elim_round () {
  eliminator.occs.release ();
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (auto *lists : {&irredundant, &redundant})
      std::erase_if ((*lists)[index (kind)], [&] (Ref ref) {
        return deref (arena, ref).garbage ();
      });
  std::fill (eliminator.pending.begin (), eliminator.pending.end (), 0);
  eliminator.lits.clear ();
  eliminator.resolvents.clear ();
  eliminator.resolvent.clear ();
  eliminator.backward.clear ();
  if (eliminator.dependent) {
    eliminator.dependent = false;
    reset_dependencies ();
  }
  eliminator.last_ticks = stats.ticks;
  schedule_elim ();
}

// One round; returns a root conflict or 'Ref::none'.  Every exit leaves
// 'eliminating ()' false (the next round is scheduled).
//
// Skipped rounds ('--elimmark').  A due round does nothing when no variable
// is marked: no constraint of a candidate was deleted since the last round
// and the bound did not grow.
//
// Budget ('--elimeffort').  The round before the search may spend
// '--elimticks' literal visits.  A later round may spend 'elimeffort' per
// mille of the search ticks since the last round that ran, at least
// '--elimmineff' and at most '--elimticks'.  Building the occurrence lists
// visits every stored literal twice; when the budget does not cover that
// (estimated by the words of the arena in use), the round is delayed to the
// next point of the schedule and the search ticks keep adding up.
// Off by default: '--elimeffort=0' gives every round '--elimticks'.
Ref Internal::eliminate () {
  PROFILE_SCOPE (elim);
  assert (!decision_level () && propagated == trail.size ());
  assert (opts.mode != 2 && complete && simplifier.units.empty ());
  subsumer.since_elim = false; // the next round gets a subsumption round
  if (!stats.elimrounds++) {
    eliminator.bound = opts.elimbound;
    mark_elim_all ();
  }
  const bool inprocessing = stats.conflicts != 0;
  if (inprocessing)
    stats.eliminprounds++;
  if (opts.elimmark && !eliminator.scheduled) {
    stats.elimskipped++;
    schedule_elim ();
    return Ref::none;
  }
  eliminator.budget = opts.elimticks;
  if (inprocessing && opts.elimeffort) {
    const double relative = (double) (stats.ticks - eliminator.last_ticks) *
                            1e-3 * (double) opts.elimeffort;
    eliminator.budget = (int64_t) std::clamp (
        relative, (double) std::min (opts.elimmineff, opts.elimticks),
        (double) opts.elimticks);
    const int64_t connect = 2 * (int64_t) (arena.size () - arena.wasted ());
    if (eliminator.budget < connect) {
      stats.elimdelayed++;
      schedule_elim ();
      return Ref::none;
    }
  }
  const size_t vars = prefix.size ();
  eliminator.ticks = 0;
  eliminator.pending.assign (vars, 0);
  if (!connect_occs ()) {
    VERBOSE (1, "elimination switched off: too many occurrences");
    finish_elim_round ();
    lim.elim = INT64_MAX;
    return Ref::none;
  }
  eliminator.marks.assign (2 * vars, 0);
  eliminator.marked.assign (2 * vars, 0);
  bool progress = true;
  while (progress && status == Status::Unknown &&
         eliminator.ticks < eliminator.budget) {
    progress = false;
    for (Var v = prefix.size (); v-- > 0;) {
      if (status != Status::Unknown ||
          eliminator.ticks >= eliminator.budget)
        break;
      if (opts.elimmark) {
        Flags &f = ftab[v];
        if (!f.elim)
          continue;
        f.elim = false;
        eliminator.scheduled--;
      }
      if (try_eliminate (v))
        progress = true;
    }
  }
  const int64_t bound = eliminator.bound;
  if (!progress && eliminator.ticks < eliminator.budget)
    grow_elim_bound ();
  finish_elim_round ();
  if (status != Status::Unknown) {
    simplifier.units.clear ();
    return Ref::none;
  }
  const Ref conflict = add_root_units ();
  PHASE ("elim", stats.elimrounds,
         "eliminated %" PRId64 " existential %" PRId64
         " universal, resolvents %" PRId64 " clauses %" PRId64
         " cubes, deleted %" PRId64 ", bound %" PRId64,
         stats.eliminated[0], stats.eliminated[1], stats.resolvents[0],
         stats.resolvents[1], stats.elimdeleted[0] + stats.elimdeleted[1],
         bound);
  if (conflict != Ref::none)
    return conflict;
  if (collecting ())
    garbage_collect ();
  else if (assertions_enabled || opts.check)
    check_invariants ();
  return Ref::none;
}

} // namespace miniqu
