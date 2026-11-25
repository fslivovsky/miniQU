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
//     irredundant parents plus '--elimbound'.  A resolvent containing a
//     literal and its negation (any variable) is dropped: such a clause is
//     satisfied and such a cube falsified by every assignment.
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
// only, and dropped at its end; the watches stay (no occurrence mode).  No
// 'Constraint &' is held across 'new_constraint' and no arena collection
// happens inside a round.  Candidates are visited from the innermost
// variable outwards, in passes repeated while a pass eliminated something
// and the round's budget of literal visits ('--elimticks') lasts.
//
// Left out (ROADMAP "Left for later"): effort relative to search ticks,
// delays after fruitless rounds, decision variables, QDIMACS input, mode 2,
// gate-aware elimination, subsumption, schedule marks, candidates ordered
// by cost, a growing bound and occurrence mode.

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

// Occurrence lists of both kinds, irredundant and learnt constraints.
void Internal::connect_occs () {
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (const auto *lists : {&irredundant, &redundant})
      for (const Ref ref : (*lists)[index (kind)]) {
        const Constraint &c = deref (arena, ref);
        if (c.garbage ())
          continue;
        eliminator.ticks += c.size ();
        for (const Lit l : c)
          if (elim_candidate (var (l)))
            eliminator (kind, l).push_back (ref);
      }
}

void Internal::flush_occs (std::vector<Ref> &occs) {
  eliminator.ticks += (int64_t) occs.size ();
  std::erase_if (occs,
                 [&] (Ref ref) { return deref (arena, ref).garbage (); });
}

// The resolvent of 'c' (containing 'pivot', whose other literals are
// marked) and 'd' (containing '~pivot'), stored unless tautological.
// False if it is too large (E4).
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
  prefix.qreduce (lits, kind);
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
  const std::vector<Ref> &pos = eliminator (kind, pivot);
  const std::vector<Ref> &neg = eliminator (kind, ~pivot);
  const auto irredundant_count = [&] (const std::vector<Ref> &occs) {
    return (size_t) std::count_if (occs.begin (), occs.end (), [&] (Ref r) {
      return !deref (arena, r).redundant ();
    });
  };
  const size_t p = irredundant_count (pos), n = irredundant_count (neg);
  if (p > (size_t) opts.elimocclim || n > (size_t) opts.elimocclim)
    return false;
  const size_t limit = p + n + (size_t) opts.elimbound;
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
        found_empty (kind);
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
        eliminator (kind, l).push_back (ref);
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
  for (const Lit l : {pivot, ~pivot})
    for (const Kind k : {Kind::Clause, Kind::Cube})
      flush_occs (eliminator (k, l));
  if (!eliminator (other (kind), pivot).empty () ||
      !eliminator (other (kind), ~pivot).empty ()) {
    stats.elimblockedother++;
    return false;
  }
  std::vector<Ref> &pos = eliminator (kind, pivot);
  std::vector<Ref> &neg = eliminator (kind, ~pivot);
  const uint32_t depth = prefix.depth (x);
  for (const std::vector<Ref> *occs : {&pos, &neg})
    for (const Ref ref : *occs) {
      const Constraint &c = deref (arena, ref);
      eliminator.ticks += c.size ();
      for (const Lit l : c)
        if (prefix.depth (var (l)) > depth) {
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
  // Each contains the unassigned 'x', so it is neither a unit nor a
  // reason.
  for (const std::vector<Ref> *occs : {&pos, &neg})
    for (const Ref ref : *occs) {
      const Constraint &c = deref (arena, ref);
      assert (!c.garbage ());
      assert (!is_root_reason (ref));
      if (c.redundant ())
        stats.elimlearnt[index (kind)]++;
      else
        stats.elimdeleted[index (kind)]++;
      mark_garbage (ref);
    }
  pos.clear ();
  neg.clear ();
  if (opts.dl && (!depend.on[x].empty () || !depend.watching[x].empty ()))
    eliminator.dependent = true;
  ftab[x].eliminated = true;
  stats.eliminated[index (kind)]++;
  return true;
}

// Drops the occurrence lists and the garbage references of the databases
// ('reduce.cpp' and 'check.cpp' expect lists without garbage), resets the
// dependencies if one mentions an eliminated variable, and schedules the
// next round.
void Internal::finish_elim_round () {
  std::vector<std::vector<Ref>> ().swap (eliminator.occs);
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (auto *lists : {&irredundant, &redundant})
      std::erase_if ((*lists)[index (kind)], [&] (Ref ref) {
        return deref (arena, ref).garbage ();
      });
  std::fill (eliminator.pending.begin (), eliminator.pending.end (), 0);
  eliminator.lits.clear ();
  eliminator.resolvents.clear ();
  eliminator.resolvent.clear ();
  if (eliminator.dependent) {
    eliminator.dependent = false;
    reset_dependencies ();
  }
  lim.elim = opts.eliminp ? stats.conflicts + (int64_t) opts.elimint *
                                                  (stats.elimrounds + 1)
                          : INT64_MAX;
}

// One round; returns a root conflict or 'Ref::none'.  Every exit leaves
// 'eliminating ()' false ('finish_elim_round' schedules the next one).
Ref Internal::eliminate () {
  PROFILE_SCOPE (elim);
  assert (!decision_level () && propagated == trail.size ());
  assert (opts.mode != 2 && complete && simplifier.units.empty ());
  stats.elimrounds++;
  if (stats.conflicts)
    stats.eliminprounds++;
  const size_t vars = prefix.size ();
  eliminator.ticks = 0;
  eliminator.occs.resize (4 * vars);
  eliminator.pending.assign (vars, 0);
  eliminator.marks.assign (2 * vars, 0);
  connect_occs ();
  bool progress = true;
  while (progress && status == Status::Unknown &&
         eliminator.ticks < opts.elimticks) {
    progress = false;
    for (Var v = prefix.size (); v-- > 0;) {
      if (status != Status::Unknown || eliminator.ticks >= opts.elimticks)
        break;
      if (try_eliminate (v))
        progress = true;
    }
  }
  finish_elim_round ();
  if (status != Status::Unknown) {
    simplifier.units.clear ();
    return Ref::none;
  }
  const Ref conflict = add_root_units ();
  PHASE ("elim", stats.elimrounds,
         "eliminated %" PRId64 " existential %" PRId64
         " universal, resolvents %" PRId64 " clauses %" PRId64
         " cubes, deleted %" PRId64,
         stats.eliminated[0], stats.eliminated[1], stats.resolvents[0],
         stats.resolvents[1], stats.elimdeleted[0] + stats.elimdeleted[1]);
  if (conflict != Ref::none)
    return conflict;
  if (collecting ())
    garbage_collect ();
  else if (assertions_enabled || opts.check)
    check_invariants ();
  return Ref::none;
}

} // namespace miniqu
