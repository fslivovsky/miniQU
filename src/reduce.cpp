// Reduction of the learnt constraint databases (ARCHITECTURE 4.3, 5.3, 9.1;
// the old 'reduceDB').
//
// Learnt clauses and cubes are redundant: deleting any of them keeps the
// formula's truth value, so there is no QBF side condition, and the
// deletion is a QLRUP 'd' step that 'mark_garbage' emits (soundness class
// 11.2 "deletion").  Units are irredundant and never deleted.
//
// Old policy (porting note 7), still the default in M1: reduce when the
// number of learnt constraints of both kinds minus the number of assigned
// variables reaches 'lim.max_learnts'.  That limit starts at a third of the
// original constraints (at least '--minlearnts') and grows by 10% after
// each of the conflict counts 100, 150, 225, ... (the interval itself grows
// by 50%), as in MiniSat.  '--reduceint=n' adds a second trigger for stress
// tests: every 'n * (reductions + 1)' conflicts.  Its growth is arithmetic
// on purpose: a fixed tiny interval would keep the databases at a constant
// size and, together with restarts, can cost termination.
//
// Per kind, the candidates are the learnt constraints that are not the
// reason of an assignment and have glue above '--tier1glue'; the worse half
// is deleted, ordered by glue, then by size, both descending (the old
// tie-break by activity is replaced by size).  The sort is stable and the
// candidates are taken in the order of the list, which is creation order
// (garbage collection keeps it), so ties keep creation order: the order of
// the ids, without reading them, which are not stored without a proof.
// Reasons are protected by a header bit that is set only inside 'reduce'.
//
// The size trigger can stay true after a reduction (protected constraints,
// the half that is kept), so the search loop decides right after 'reduce',
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
      const Constraint &c = deref (arena, ref);
      if (!c.reason () && c.glue () > (uint32_t) opts.tier1glue)
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
    const size_t deleted = candidates.size () / 2;
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
