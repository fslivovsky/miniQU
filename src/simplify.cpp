// Root-level simplification of the constraint databases (ROADMAP M2.1;
// ARCHITECTURE 4.3, 8.2, 11.1).  MiniSat's 'simplify' / 'removeSatisfied'
// and CaDiCaL's 'mark_satisfied_clauses_as_garbage' /
// 'remove_falsified_literals' give the structure; the QBF rules are those
// of the roadmap, which differ from SAT in one point: a root literal may
// only be used to remove or delete something if a stored *unit* justifies
// it.
//
// Definitions.  A variable has a unit of kind K if it is assigned on level
// 0 and its reason is a stored constraint of size 1 and kind K.  Disabled
// and vanished are per kind ('kval', ARCHITECTURE 4.1).
//
// Runs at decision level 0 after a complete conflict-free propagation, when
// root literals were assigned since the last run ('simplifying'), in modes
// 0 and 1 only.  Mode 2 learns constraints with complementary secondary
// literals and ignores a lone secondary literal in propagation; removing
// literals there needs its own argument and has no proof to check it, so
// the technique is off in mode 2 and nothing below is mode-2 specific
// (ROADMAP "M2 execution plan").
//
//  1. Materialise units (class D).  Over the new root literals in trail
//     order: a literal forced by a reason R of kind K with more than one
//     literal gets a unit of kind K if every other literal of R (all of
//     them vanished, since propagation in modes 0 and 1 ignores the prefix)
//     has a unit of kind K.  The unit is the propagated literal of R,
//     reduced; it replaces R as the reason.  A secondary propagated literal
//     (mode 1) reduces to the empty constraint, which decides the formula.
//     If some other literal has no unit of kind K (it was assigned by the
//     other kind, or by such an R in turn), the variable stays
//     root-assigned without a unit, and nothing below uses it: that keeps
//     INV-DERIVED. Proof: derived step, chain = R, then the units of its
//     other literals (each clashes with R on exactly one literal).
//
//  2. Remove root-vanished literals (class D).  From every stored
//  constraint
//     C of kind K and size >= 2, irredundant or redundant, that step 3 does
//     not delete and that is not a reason: every vanished literal whose
//     variable has a unit of kind K, then 'qreduce'.  A vanished literal
//     without a unit, or with a unit of the other kind, stays
//     (INV-DERIVED). Proof: 'strengthen', chain = C, then the units of the
//     removed literals; without a proof the id is counted all the same, so
//     that runs with and without proof number alike.  A reason (its
//     propagated literal has no unit, otherwise step 1 replaced it) is
//     skipped: its propagated literal must stay at position 0 and its
//     memory must stay valid, and it is disabled at the root forever
//     anyway.
//
//  3. Delete root-disabled constraints (class R).  A constraint of size >=
//  2
//     with a literal that disables it and has a unit of *either* kind is
//     deleted ('mark_garbage', proof 'd').  One disabled only by literals
//     without a unit stays; it is never visited again (its watch on the
//     disabling literal blocks).  A reason is never deleted by this rule,
//     as it is disabled by its propagated literal only, which has no unit.
//
// Side conditions (ARCHITECTURE 11.1).  QCIR: steps 1 and 2 are
// derivations of the same kind; step 3 cannot affect INV-COMPLETE, since
// root assignments are never undone and a root-disabled constraint can
// neither propagate nor conflict again.  QDIMACS, modes 0 and 1
// (INV-SANDWICH): a clause unit is a derived clause stored irredundant (the
// "promote" row); step 2 on an irredundant clause is the "replace C by C'
// in C" row (the unit may be a learnt consequence, hence (LO)/(HI) and not
// equivalence); step 3 is one of the two deletion rows, under an
// irredundant unit clause or a stored unit cube.  Units are irredundant and
// never deleted, and initial cubes ('model.cpp') hit the remaining
// irredundant clauses including the units.
//
// Units and conflicts from step 2.  After complete propagation every
// constraint that is not disabled has at least two literals that have not
// vanished (its two watched ones).  Step 2 removes vanished literals only,
// but 'qreduce' then also drops unassigned secondary literals, and
// propagation in modes 0 and 1 does not reduce: (e1 u2 e3) with e3 removed
// becomes the unit (e1); (u2 u4 e5) becomes empty; and with a literal x
// that vanished without a unit, (x e1 u3 e5) becomes (x e1), which is unit,
// and (x u2 u4 e5) becomes (x), a root conflict.  So strengthening can
// produce all of these, and each is handled:
//
//  - empty: the empty constraint of kind K is logged and decides the
//    formula;
//  - one literal: the unit is derived under a fresh id and the old
//    constraint deleted (exactly one derivation and one deletion), and it
//    is stored and given to the assignment only after the pass, so that the
//    assignment, and with it what has a unit, does not change while the
//    databases are walked.  An unassigned literal is assigned with the unit
//    as reason; an assigned one with a positive kind value gets the unit as
//    reason unless it has a unit already (a unit has no antecedents on the
//    trail, so any root reason can be replaced by it); a vanished one is a
//    root conflict, which is returned to the search loop and analysed like
//    any other conflict (it derives the empty constraint);
//  - two or more literals, at most one of them not vanished: shrunk in
//  place
//    like any other, and watched by the literals that are best for
//    propagation (disabling, then unassigned, then the latest vanished);
//    when the second watch is a vanished literal whose propagation is over,
//    the propagation head goes back to it, so that propagation finds the
//    unit or the conflict.
//
// A strengthened constraint is detached before and attached after the
// rewrite, also when its watched literals stay: the blocker of a watch can
// be any literal that once was watched, including a removed one.  A
// redundant constraint keeps its 'used' mark and its glue (at most the new
// size).  Garbage collection follows if due, with no 'Ref' held.

#include "contract.hpp"
#include "internal.hpp"
#include "proof.hpp"

#include <algorithm>
#include <cassert>
#include <cinttypes>
#include <limits>

namespace miniqu {

bool Internal::simplifying () const {
  if (!opts.rootsimp || opts.mode == 2 || decision_level ())
    return false;
  if (trail.size () <= simplifier.trail)
    return false;
  return !opts.rootsimpdelay || stats.propagations >= lim.simplify;
}

const Constraint *Internal::root_unit (Lit l) const {
  if (!val (l))
    return nullptr;
  const Var v = var (l);
  assert (!level (v));
  const Ref r = reason (v);
  if (r == Ref::none)
    return nullptr;
  const Constraint &c = deref (arena, r);
  return c.size () == 1 ? &c : nullptr;
}

// A unit of that kind on the variable of 'l', or 'nullptr'.
const Constraint *Internal::root_unit (Kind kind, Lit l) const {
  const Constraint *unit = root_unit (l);
  return unit && unit->kind () == kind ? unit : nullptr;
}

// Reasons of modes 0 and 1 hold the propagated literal at position 0.
bool Internal::is_root_reason (Ref ref) const {
  const Lit first = deref (arena, ref)[0];
  return val (first) && reason (var (first)) == ref;
}

void Internal::materialize_root_units (size_t end) {
  std::vector<uint64_t> &ids = simplifier.chain;
  std::vector<Lit> &lits = simplifier.lits;
  for (size_t i = simplifier.trail; i < end; i++) {
    const Lit lit = trail[i];
    const Ref r = reason (var (lit));
    // At the root nothing is decided, and a completed conflict of mode 0
    // on level 0 ends the search.
    assert (r != Ref::none);
    const Constraint &c = deref (arena, r);
    if (c.size () == 1)
      continue;
    const Kind kind = c.kind ();
    assert (forced (kind, c[0]) == lit);
    const auto has_unit = [&] (Lit other) {
      assert (kval (kind, other) < 0);
      return root_unit (kind, other) != nullptr;
    };
    if (!std::all_of (c.begin () + 1, c.end (), has_unit))
      continue;
    ids.clear ();
    if (proof) {
      ids.push_back (c.id ());
      for (uint32_t k = 1; k < c.size (); k++)
        ids.push_back (root_unit (kind, c[k])->id ());
    }
    lits.assign (1, c[0]);
    prefix.qreduce (lits, kind);
    const uint64_t id = next_id++;
    if (proof)
      proof->add_derived (id, kind, lits, ids);
    if (lits.empty ()) {
      found_empty (kind, {&c[0], 1});
      return;
    }
    stats.rootunits++;
    const Ref unit = new_constraint (id, kind, lits, false, 0);
    replace_reason (var (lit), unit);
  }
}

// Positions 0 and 1 get the literals that are best for propagation under
// the root assignment: disabling, then unassigned, then the latest
// vanished.  At least two literals.
void Internal::order_root_watches (Kind kind, std::span<Lit> lits) const {
  assert (lits.size () > 1);
  const auto rank = [&] (Lit l) -> int64_t {
    const int value = kval (kind, l);
    if (value > 0)
      return std::numeric_limits<int64_t>::max ();
    if (!value)
      return std::numeric_limits<int64_t>::max () - 1;
    return vtab[var (l)].trail;
  };
  const auto by_rank = [&] (Lit a, Lit b) { return rank (a) < rank (b); };
  std::iter_swap (lits.begin (),
                  std::max_element (lits.begin (), lits.end (), by_rank));
  std::iter_swap (
      lits.begin () + 1,
      std::max_element (lits.begin () + 1, lits.end (), by_rank));
}

// For a constraint ordered by 'order_root_watches': if the second literal
// vanished in a propagation that is over and the first does not disable
// the constraint, the constraint is unit or conflicting, and propagation
// has to visit it again from there.
void Internal::rewind_root_propagation (Ref ref) {
  const Constraint &c = deref (arena, ref);
  const Kind kind = c.kind ();
  if (kval (kind, c[0]) <= 0 && kval (kind, c[1]) < 0)
    propagated = std::min (propagated, (size_t) vtab[var (c[1])].trail);
}

void Internal::watch_root_simplified (Ref ref) {
  Constraint &c = deref (arena, ref);
  order_root_watches (c.kind (), c.lits ());
  rewind_root_propagation (ref);
  attach (ref);
}

// Step 2 on one constraint.
void Internal::strengthen_root (Ref ref) {
  Constraint &c = deref (arena, ref);
  const Kind kind = c.kind ();
  std::vector<uint64_t> &ids = simplifier.chain;
  std::vector<Lit> &lits = simplifier.lits;
  ids.clear ();
  lits.clear ();
  if (proof)
    ids.push_back (c.id ());
  for (Lit l : c) {
    const Constraint *unit =
        kval (kind, l) < 0 ? root_unit (kind, l) : nullptr;
    if (!unit)
      lits.push_back (l);
    else if (proof)
      ids.push_back (unit->id ());
  }
  if (prefix.reduces_to_empty (lits, kind))
    simplifier.move = lits; // for 'found_empty' below
  prefix.qreduce (lits, kind);
  assert (lits.size () < c.size ());
  stats.rootstrengthened++;
  stats.rootlits += (int64_t) (c.size () - lits.size ());
  LOG (ref, "strengthening to %zu literals", lits.size ());
  if (lits.size () < 2) {
    const uint64_t id = next_id++;
    if (proof)
      proof->add_derived (id, kind, lits, ids);
    if (lits.empty ()) {
      found_empty (kind, simplifier.move);
      return;
    }
    stats.rootstrunits++;
    mark_garbage (ref);
    simplifier.units.push_back ({id, kind, lits[0]});
    return;
  }
  if (proof)
    proof->strengthen (c, lits, ids);
  else
    next_id++;
  detach (ref);
  std::copy (lits.begin (), lits.end (), c.begin ());
  const uint32_t size = static_cast<uint32_t> (lits.size ());
  shrink_constraint (ref, size);
  if (c.redundant ())
    c.set_glue (std::min (c.glue (), size));
  watch_root_simplified (ref);
}

// Steps 2 and 3 on one constraint; step 2 may decide the formula.
void Internal::simplify_constraint (Ref ref) {
  const Constraint &c = deref (arena, ref);
  const Kind kind = c.kind ();
  bool removable = false;
  for (Lit l : c) {
    const int value = kval (kind, l);
    if (!value)
      continue;
    const Constraint *unit = root_unit (l);
    if (!unit)
      continue;
    if (value > 0) {
      assert (!is_root_reason (ref));
      stats.rootdeleted++;
      mark_garbage (ref);
      return;
    }
    removable |= unit->kind () == kind;
  }
  if (removable && !is_root_reason (ref))
    strengthen_root (ref);
}

// The units of step 2, stored and assigned after the pass.  Returns a root
// conflict or 'Ref::none'.
Ref Internal::add_root_units () {
  Ref conflict = Ref::none;
  for (const RootUnit &u : simplifier.units) {
    const Ref ref = new_constraint (u.id, u.kind, {&u.lit, 1}, false, 0);
    if (conflict != Ref::none)
      continue;
    const Lit l = forced (u.kind, u.lit);
    if (!val (l))
      assign (l, ref);
    else if (val (l) < 0) {
      stats.rootconflicts++;
      conflict = ref;
    } else if (!root_unit (l))
      replace_reason (var (l), ref);
  }
  simplifier.units.clear ();
  return conflict;
}

Ref Internal::simplify_root () {
  PROFILE_SCOPE (simplify);
  assert (!decision_level () && propagated == trail.size ());
  assert (opts.mode != 2 && simplifier.units.empty ());
  stats.rootsimps++;
  const size_t end = trail.size ();
  materialize_root_units (end);
  // The units of step 2 are assigned after this point; they are new root
  // literals for the next run.
  simplifier.trail = end;
  if (status != Status::Unknown)
    return Ref::none;

  int64_t literals = 0; // in the stored constraints, for the throttle
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (auto *lists : {&irredundant, &redundant}) {
      std::vector<Ref> &list = (*lists)[index (kind)];
      size_t kept = 0;
      for (const Ref ref : list) {
        if (status == Status::Unknown && deref (arena, ref).size () > 1 &&
            !deref (arena, ref).garbage ())
          simplify_constraint (ref);
        const Constraint &c = deref (arena, ref);
        if (c.garbage ())
          continue;
        list[kept++] = ref;
        literals += c.size ();
      }
      list.resize (kept);
    }
  if (status != Status::Unknown) {
    simplifier.units.clear ();
    return Ref::none;
  }
  if (assertions_enabled || opts.check)
    check_root_simplified ();

  const Ref conflict = add_root_units ();
  lim.simplify = stats.propagations + literals;
  PHASE ("simplify", stats.rootsimps,
         "units %" PRId64 " strengthened %" PRId64 " deleted %" PRId64
         ", trail at root %zu",
         stats.rootunits, stats.rootstrengthened, stats.rootdeleted,
         trail.size ());
  if (conflict != Ref::none)
    return conflict;
  if (collecting ())
    garbage_collect ();
  else if (assertions_enabled || opts.check)
    check_invariants ();
  return Ref::none;
}

} // namespace miniqu
