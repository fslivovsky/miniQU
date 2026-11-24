// Reduction of the learnt constraint databases (ARCHITECTURE 4.3, 5.3, 9.1;
// the old 'reduceDB').
//
// Learnt clauses and cubes are redundant: deleting any of them keeps the
// formula's truth value, so there is no QBF side condition, and the
// deletion is a QLRUP 'd' step that 'mark_garbage' emits (soundness class
// 11.2 "deletion").  Units are irredundant and never deleted.
//
// Two triggers, either of which starts a reduction:
//
//  - the conflict schedule ('--reduceint=n', 0 = never): the first
//    reduction after n conflicts, then 'reductions' times n conflicts after
//    the previous one.  The growth is arithmetic on purpose: a fixed tiny
//    interval would keep the databases at a constant size and, together
//    with restarts, can cost termination.  The base is the current conflict
//    count so that a burst of conflicts does not cause a burst of
//    reductions.
//  - the size limit of MiniSat ('--reducesize', off by default): the number
//    of learnt constraints of both kinds minus the number of assigned
//    variables reaches 'lim.max_learnts'.  That limit starts at a third of
//    the original constraints (at least '--minlearnts') and grows by 10%
//    after each of the conflict counts 100, 150, 225, ... (the interval
//    itself grows by 50%).  The constants below are MiniSat's.
//
// Per kind, a learnt constraint that is not the reason of an assignment is
// kept if
//
//  1. '--tiers' and its 'used' mark is nonzero (the mark is decremented,
//     see 'tier.cpp'), or
//  2. its glue is at most the tier 1 limit of its kind ('--tier1glue', or
//     what '--recomputetier' made of it).
//
// Everything else is a candidate.  The candidates are sorted by glue, then
// by size, both descending (the old tie-break by activity is replaced by
// size), and the first '--reducetarget' percent of them are deleted, so the
// worst go.  The sort is stable and the candidates are taken in the order
// of the list, which is creation order (garbage collection keeps it), so
// ties keep creation order: the order of the ids, without reading them,
// which are not stored without a proof.  Reasons are protected by a header
// bit that is set only inside 'reduce'.
//
// The M1 solver is reproduced bit for bit by '--no-tiers --no-glueupdate
// --reducetarget=50 --reducesize --reduceint=0' (tests/m1_equiv.sh).
//
// A trigger can stay true after a reduction (protected constraints, the
// share that is kept), so the search loop decides right after 'reduce',
// like the old 'search' does, instead of reducing again at once.

#include "internal.hpp"

#include <algorithm>
#include <cstdint>

namespace miniqu {

// MiniSat's 'learntsize_factor', 'learntsize_inc', 'learntsize_adjust_*'.
static constexpr double learnt_fraction = 1.0 / 3;
static constexpr double learnt_limit_growth = 1.1;
static constexpr double adjust_start = 100;
static constexpr double adjust_growth = 1.5;

void Internal::init_reduce () {
  size_t originals = 0;
  for (const auto &list : irredundant)
    originals += list.size ();
  lim.max_learnts = std::max ((double) originals * learnt_fraction,
                              (double) opts.minlearnts);
  inc.adjust = adjust_start;
  lim.adjust = (int64_t) inc.adjust;
  lim.reduce = opts.reduceint;
}

// Called once per learnt constraint.
void Internal::adjust_learnt_limit () {
  if (--lim.adjust > 0)
    return;
  inc.adjust *= adjust_growth;
  lim.adjust = (int64_t) inc.adjust;
  lim.max_learnts *= learnt_limit_growth;
}

bool Internal::reducing () const {
  if (opts.reduceint && stats.conflicts >= lim.reduce)
    return true;
  if (!opts.reducesize)
    return false;
  const int64_t learnts =
      (int64_t) (redundant[0].size () + redundant[1].size ());
  return (double) (learnts - (int64_t) trail.size ()) >= lim.max_learnts;
}

void Internal::protect_reasons () {
  for (Lit l : trail)
    if (const Ref r = reason (var (l)); r != Ref::none)
      deref (arena, r).set_reason (true);
}

void Internal::unprotect_reasons () {
  for (Lit l : trail)
    if (const Ref r = reason (var (l)); r != Ref::none)
      deref (arena, r).set_reason (false);
}

void Internal::reduce () {
  PROFILE_SCOPE (reduce);
  stats.reductions++;
  protect_reasons ();
  std::vector<Ref> candidates;
  for (Kind kind : {Kind::Clause, Kind::Cube}) {
    std::vector<Ref> &list = redundant[index (kind)];
    candidates.clear ();
    for (Ref ref : list) {
      Constraint &c = deref (arena, ref);
      if (c.reason ())
        continue;
      if (opts.tiers && c.used ()) {
        c.set_used (c.used () - 1);
        continue;
      }
      if (c.glue () > (uint32_t) tiers.tier1[index (kind)])
        candidates.push_back (ref);
    }
    std::stable_sort (candidates.begin (), candidates.end (),
                      [this] (Ref a, Ref b) {
                        const Constraint &x = deref (arena, a);
                        const Constraint &y = deref (arena, b);
                        if (x.glue () != y.glue ())
                          return x.glue () > y.glue ();
                        return x.size () > y.size ();
                      });
    const size_t deleted =
        candidates.size () * (size_t) opts.reducetarget / 100;
    for (size_t i = 0; i < deleted; i++)
      mark_garbage (candidates[i]);
    stats.reduced[index (kind)] += (int64_t) deleted;
    list.erase (std::remove_if (list.begin (), list.end (),
                                [this] (Ref ref) {
                                  return deref (arena, ref).garbage ();
                                }),
                list.end ());
  }
  unprotect_reasons ();
  if (opts.reduceint)
    lim.reduce =
        stats.conflicts + (int64_t) opts.reduceint * stats.reductions;
  report ("reduce");
  if (collecting ())
    garbage_collect ();
}

} // namespace miniqu
