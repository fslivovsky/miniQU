// Vivification of learnt constraints (ROADMAP M4, V1-V6; CaDiCaL's
// 'vivify.cpp' gives the names and the shape, this is a much smaller
// version).  Clauses and cubes go through the same code, parameterised by
// the kind K of the candidate.
//
// A round runs at decision level 0 after a complete conflict-free
// propagation, on a conflict schedule ('--vivifyint', growing
// arithmetically), in modes 0 and 1, for QCIR and QDIMACS input alike.  For
// each kind switched on ('--vivifyclause', '--vivifycube') it takes the
// candidates of that kind ('vivify_select'), lower tier first and newest
// first inside a tier, until its share of '--vivifyticks' (propagation
// ticks) is spent.  Candidates are the learnt constraints of tier 1, up to
// tier 2, or all ('--vivifytier'; the limits of 'tier.cpp').  A candidate
// tried and left unchanged gets the 'vivified' bit; with '--vivifyonce'
// such candidates are skipped until a pass finds none without the bit,
// which then clears the bits of its candidates and takes them all
// ('vivifyrescheduled'); a shortened candidate keeps the bit clear and is
// tried again (CaDiCaL).  For a candidate C of kind K that is live, has at
// least two literals and no literal disabling it at the root, the literals
// of C are visited in descending number of occurrences among the
// candidates of the pass, ties by literal index ('vivify_order', CaDiCaL's
// heuristic; the stored order of C does not change):
//
//  (a) a literal that disables C (implied above the root) ends the walk;
//      the analysis starts from its reason and keeps the literal;
//  (b) a vanished literal (implied or at the root) is skipped;
//  (c) an unassigned literal is assigned its vanishing value (a clause
//      literal false, a cube literal true) as a decision on a new level,
//      and the trail is propagated through the K-constraints only
//      ('propagate_kind'); a conflict ends the walk and starts the
//      analysis.
//
// C stays watched and may itself be the conflict or a reason.
//
// Side conditions.  V1: only K-constraints propagate during the walk, so
// every reason above level 0 has kind K.  V2: in mode 0 a constraint whose
// single non-vanished literal is secondary does nothing ('Lone::Ignore'),
// in mode 1 it propagates (QU-resolution, as in the search).  V4: the
// analysis ('vivify_analyze') walks the trail back from its end and
// resolves with K-reasons only; a marked decision is a literal of C and
// goes into the result D; a marked root literal is resolved away with its
// unit of kind K ('root_unit (K, .)') if it has one, else it stays in D if
// its variable occurs in C (it is then the literal of C), and else the
// candidate is given up ('vivifyskipped'): a root literal assigned by the
// other kind, or by a K-constraint without a stored unit, is no
// consequence in K's calculus that the chain could name.
//
// Soundness.  Every resolution step uses a K-reason all of whose other
// literals have vanished under the current assignment.  The running
// resolvent consists of vanished literals plus possibly the kept literal of
// case (a), which was assigned after everything earlier on the trail, so no
// earlier reason contains its variable.  Hence each step clashes on exactly
// one pivot (the propagated literal of the reason) and no resolvent is
// tautological.  In mode 0 all pivots are primary (Q-resolution), in mode
// 1 pivots may be secondary (QU-resolution).  The decisions may be in any
// prefix order (V3): the analysis never looks at it.  D, reduced
// ('qreduce'), is a subset of C (V5), so it replaces C: a shorter D is
// logged as one derived step with chain = the conflict (or the reason of
// the kept literal), the reasons in reverse trail order, then the root
// units; the Lean checker resolves along the chain and reduces at the end,
// so the format needs nothing new.  Ids are consumed alike with and
// without a proof.
//
// Results.  Empty: decides the formula.  One literal: a unit under a fresh
// id, C deleted, the unit assigned after the round ('simplifier.units',
// 'add_root_units', as in 'simplify.cpp').  Otherwise C is rewritten in
// place exactly as 'strengthen_root' does it.  Every candidate starts and
// ends at level 0 (no decision reuse), the saved phases are restored after
// the round, and no 'Ref' is held across the round.  A rewritten
// constraint that is unit or conflicting at the root moves 'propagated'
// back ('watch_root_simplified'); later candidates of the round then run
// with incomplete root propagation, which is weaker but sound.
//
// Deliberately left out (M4-T1, M4-T2): irredundant constraints, mode 2 (a
// notice, nothing done), decision reuse between candidates and sorting of
// candidates by literals, per-tier effort shares, effort relative to the
// search ticks (the occurrence count is not counted either), deletion of
// subsumed or implied candidates, glue recomputation, tuning.

#include "contract.hpp"
#include "internal.hpp"
#include "proof.hpp"

#include <algorithm>
#include <cassert>
#include <cinttypes>

namespace miniqu {

void Internal::init_vivify () { lim.vivify = opts.vivifyint; }

bool Internal::vivifying () const {
  if (!opts.vivify || (!opts.vivifyclause && !opts.vivifycube))
    return false;
  return opts.mode != 2 && stats.conflicts >= lim.vivify;
}

// The tier of a learnt constraint by its glue, with the current limits of
// its kind.
int Internal::vivify_tier (const Constraint &c) const {
  assert (c.redundant ());
  const size_t k = index (c.kind ());
  const uint32_t glue = c.glue ();
  if (glue <= (uint32_t) tiers.tier1[k])
    return 1;
  return glue <= (uint32_t) tiers.tier2[k] ? 2 : 3;
}

// The candidates of one pass into 'vivifier.candidates', visited from the
// back: higher tiers first in the vector, newest last inside a tier.
void Internal::vivify_select (Kind kind) {
  std::vector<Ref> &candidates = vivifier.candidates;
  candidates.clear ();
  for (const Ref ref : redundant[index (kind)]) {
    const Constraint &c = deref (arena, ref);
    if (!c.garbage () && vivify_tier (c) <= opts.vivifytier)
      candidates.push_back (ref);
  }
  if (opts.vivifyonce) {
    const auto tried = [&] (Ref ref) {
      return deref (arena, ref).vivified ();
    };
    if (!candidates.empty () &&
        std::all_of (candidates.begin (), candidates.end (), tried)) {
      stats.vivifyrescheduled++;
      for (const Ref ref : candidates)
        deref (arena, ref).set_vivified (false);
    } else
      std::erase_if (candidates, tried);
  }
  std::stable_sort (candidates.begin (), candidates.end (),
                    [&] (Ref a, Ref b) {
                      return vivify_tier (deref (arena, a)) >
                             vivify_tier (deref (arena, b));
                    });
}

// Occurrences of each literal among the candidates of the pass.
void Internal::vivify_count () {
  for (const Ref ref : vivifier.candidates)
    for (const Lit l : deref (arena, ref))
      vivifier.counts[index (l)]++;
}

// The order in which the literals of the candidate are visited: more
// occurrences first, ties by literal index.  Marks the variables of the
// candidate.
void Internal::vivify_order (const Constraint &c) {
  std::vector<Lit> &order = vivifier.order;
  const std::vector<uint32_t> &counts = vivifier.counts;
  order.assign (c.begin (), c.end ());
  std::sort (order.begin (), order.end (), [&] (Lit a, Lit b) {
    const uint32_t x = counts[index (a)], y = counts[index (b)];
    return x != y ? x > y : index (a) < index (b);
  });
  for (Lit l : order)
    vivifier.in_candidate[var (l)] = 1;
}

// V4.  Derives D into 'vivifier.lits' (and its chain) from 'start', a
// conflict or the reason of 'kept'.  False if the candidate is given up.
bool Internal::vivify_analyze (Kind kind, Ref start, Lit kept) {
  assert (decision_level () > 0);
  std::vector<Lit> &lits = vivifier.lits;
  std::vector<uint64_t> &ids = vivifier.chain;
  std::vector<uint64_t> &units = vivifier.units;
  std::vector<Var> &touched = vivifier.touched;
  lits.clear ();
  ids.clear ();
  units.clear ();
  const auto mark = [&] (Lit l) {
    assert (kval (kind, l) < 0);
    const Var v = var (l);
    if (seen[v])
      return;
    seen[v] = 1;
    touched.push_back (v);
  };
  const Constraint &s = deref (arena, start);
  assert (s.kind () == kind);
  if (proof)
    ids.push_back (s.id ());
  for (Lit l : s)
    if (l != kept)
      mark (l);
  if (kept != lit_undef)
    lits.push_back (kept);

  // Above the root: decisions go into D, implied literals are resolved.
  for (size_t i = trail.size (); i-- > control[0];) {
    const Lit p = trail[i];
    const Var v = var (p);
    if (!seen[v])
      continue;
    const Ref r = reason (v);
    if (r == Ref::none) {
      lits.push_back (kind == Kind::Clause ? ~p : p);
      continue;
    }
    const Constraint &c = deref (arena, r);
    assert (c.kind () == kind && forced (kind, c[0]) == p);
    if (proof)
      ids.push_back (c.id ());
    for (uint32_t k = 1; k < c.size (); k++)
      mark (c[k]);
  }

  // At the root: K-units, literals of C, or give up.
  bool ok = true;
  for (const Var v : touched) {
    if (!ok)
      break;
    if (level (v))
      continue;
    const Lit p = val (mk_lit (v)) > 0 ? mk_lit (v) : ~mk_lit (v);
    const Lit x = kind == Kind::Clause ? ~p : p;
    if (const Constraint *unit = root_unit (kind, x)) {
      if (proof)
        units.push_back (unit->id ());
    } else if (vivifier.in_candidate[v])
      lits.push_back (x);
    else
      ok = false;
  }
  for (const Var v : touched)
    seen[v] = 0;
  touched.clear ();
  if (ok && proof)
    ids.insert (ids.end (), units.begin (), units.end ());
  return ok;
}

// Debug check before a rewrite: no two literals of D are equal or
// complementary.
[[maybe_unused]] static bool distinct_variables (std::vector<Lit> lits) {
  std::sort (lits.begin (), lits.end (),
             [] (Lit a, Lit b) { return var (a) < var (b); });
  return std::adjacent_find (lits.begin (), lits.end (), [] (Lit a, Lit b) {
           return var (a) == var (b);
         }) == lits.end ();
}

// V5.  Replaces the candidate by the reduced D if it is shorter, as
// 'strengthen_root' does, else marks it as tried.  At level 0.
void Internal::vivify_apply (Ref ref) {
  Constraint &c = deref (arena, ref);
  const Kind kind = c.kind ();
  std::vector<Lit> &lits = vivifier.lits;
  assert (std::all_of (lits.begin (), lits.end (), [&] (Lit l) {
    return std::find (c.begin (), c.end (), l) != c.end ();
  }));
  if (lits.size () >= c.size ()) {
    c.set_vivified (true);
    return;
  }
  assert (distinct_variables (lits)); // with the above: a proper subset
  stats.vivified[index (kind)]++;
  stats.vivifiedlits[index (kind)] += (int64_t) (c.size () - lits.size ());
  LOG (ref, "vivified to %zu literals", lits.size ());
  const std::vector<uint64_t> &ids = vivifier.chain;
  if (lits.size () < 2) {
    const uint64_t id = next_id++;
    if (proof)
      proof->add_derived (id, kind, lits, ids);
    if (lits.empty ()) {
      found_empty (kind, vivifier.unreduced);
      return;
    }
    stats.vivifyunits++;
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
  c.set_glue (std::min (c.glue (), size));
  c.set_vivified (false);
  watch_root_simplified (ref);
  if (opts.subsume)
    mark_subsume (c);
}

// One candidate, from level 0 back to level 0.
void Internal::vivify_constraint (Ref ref) {
  assert (!decision_level ());
  const Constraint &c = deref (arena, ref);
  if (c.garbage () || c.size () < 2)
    return;
  const Kind kind = c.kind ();
  for (Lit l : c)
    if (kval (kind, l) > 0)
      return; // disabled at the root
  stats.vivifychecked[index (kind)]++;
  vivify_order (c);

  Ref start = Ref::none;
  Lit kept = lit_undef;
  for (const Lit l : vivifier.order) {
    const int value = kval (kind, l);
    if (value > 0) { // (a)
      assert (level (var (l)) && reason (var (l)) != Ref::none);
      start = reason (var (l));
      kept = l;
      break;
    }
    if (value < 0) // (b)
      continue;
    size_t head = trail.size (); // (c)
    new_level ();
    assign (kind == Kind::Clause ? ~l : l, Ref::none);
    stats.vivifydecisions++;
    start = propagate_kind (kind, head);
    if (start != Ref::none)
      break;
  }

  bool success = false;
  if (start != Ref::none) {
    success = vivify_analyze (kind, start, kept);
    if (!success)
      stats.vivifyskipped++;
  }
  backtrack (0);
  if (success) {
    vivifier.unreduced = vivifier.lits; // for 'found_empty'
    prefix.qreduce (vivifier.lits, kind);
    vivify_apply (ref);
  } else
    deref (arena, ref).set_vivified (true);
  for (Lit l : vivifier.order)
    vivifier.in_candidate[var (l)] = 0;
  vivifier.order.clear ();
  vivifier.lits.clear ();
  vivifier.chain.clear ();
}

// The candidates of one kind within 'ticks'.
void Internal::vivify_kind (Kind kind, int64_t ticks) {
  std::vector<Ref> &candidates = vivifier.candidates;
  vivify_select (kind);
  vivify_count ();
  const int64_t limit = stats.ticks + ticks;
  while (!candidates.empty () && stats.ticks < limit &&
         status == Status::Unknown) {
    const Ref ref = candidates.back ();
    candidates.pop_back ();
    vivify_constraint (ref);
  }
  candidates.clear ();
  std::fill (vivifier.counts.begin (), vivifier.counts.end (), 0u);
}

// One round; returns a root conflict or 'Ref::none'.  Every exit leaves
// 'vivifying ()' false.
Ref Internal::vivify () {
  PROFILE_SCOPE (vivify);
  assert (!decision_level () && propagated == trail.size ());
  assert (opts.mode != 2 && simplifier.units.empty ());
  stats.vivifyrounds++;
  vivifier.phases = phases;
  vivifier.in_candidate.assign (prefix.size (), 0);
  vivifier.counts.assign (2 * prefix.size (), 0);
  const int kinds = opts.vivifyclause + opts.vivifycube;
  for (const Kind kind : {Kind::Clause, Kind::Cube}) {
    const int on =
        kind == Kind::Clause ? opts.vivifyclause : opts.vivifycube;
    if (on && status == Status::Unknown)
      vivify_kind (kind, opts.vivifyticks / kinds);
  }
  for (std::vector<Ref> &list : redundant)
    std::erase_if (list,
                   [&] (Ref ref) { return deref (arena, ref).garbage (); });
  phases.swap (vivifier.phases);
  std::vector<int8_t> ().swap (vivifier.phases);
  std::vector<uint8_t> ().swap (vivifier.in_candidate);
  std::vector<uint32_t> ().swap (vivifier.counts);
  lim.vivify =
      stats.conflicts + (int64_t) opts.vivifyint * (stats.vivifyrounds + 1);
  if (status != Status::Unknown) {
    simplifier.units.clear ();
    return Ref::none;
  }
  const Ref conflict = add_root_units ();
  PHASE ("vivify", stats.vivifyrounds,
         "checked %" PRId64 " clauses %" PRId64 " cubes, vivified %" PRId64
         " clauses %" PRId64 " cubes, removed %" PRId64 " literals",
         stats.vivifychecked[0], stats.vivifychecked[1], stats.vivified[0],
         stats.vivified[1], stats.vivifiedlits[0] + stats.vivifiedlits[1]);
  if (conflict != Ref::none)
    return conflict;
  if (collecting ())
    garbage_collect ();
  else if (assertions_enabled || opts.check)
    check_invariants ();
  return Ref::none;
}

} // namespace miniqu
