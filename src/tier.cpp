// Usage marks, glue updates and tier limits of learnt constraints
// (ARCHITECTURE 5.2, 9.1; CaDiCaL's 'bump_clause', 'recompute_glue',
// 'promote_clause' and 'recompute_tier').
//
// Class: heuristic only.  There is no QBF side condition and no proof step
// beyond the 'd' of 'reduce.cpp': the marks, the glue and the limits decide
// which learnt constraints 'reduce' deletes, and deleting a learnt
// constraint is always sound.  Every counter and every limit is per kind,
// because the glue distributions of clauses and cubes differ (cubes from
// satisfying assignments are long).
//
// Tiers by glue: tier 1 is 'glue <= tier1' and never deleted, tier 2 is
// 'glue <= tier2', tier 3 the rest.  The limits start as '--tier1glue' and
// '--tier2glue'.  With '--recomputetier' every use adds the glue of the
// constraint to a histogram of its kind, and 'retier' (scheduled in
// 'lim.retier': after 2 conflicts, then after 4, 8, ... at most 2^16 apart)
// moves the limits of each kind to the smallest glues that cover
// '--tier1limit' and '--tier2limit' percent of the uses, but not below
// '--tier1minglue' and '--tier2minglue', and tier 2 stays above tier 1.
// A kind without a recorded use keeps the options.  A moved limit does not
// touch the marks already stored.  Without '--recomputetier' the limits are
// the options forever.
//  A learnt constraint carries
// two bits 'used': 2 when it was learnt or used while in tier 1 or 2, 1
// when in tier 3, and every reduction decrements it, so tier 2 survives
// two reductions without use and tier 3 one.  With '--no-tiers' nothing is
// marked and 'reduce' sees 0 everywhere.
//
// A constraint is used when its literals enter the resolvent of an
// analysis, as the conflict or as the reason of a resolution step, in all
// three analyses and at the same place in each: a constraint that an
// analysis was about to resolve with when it ended by learning a dependency
// is not used, one it did resolve with before is.  Units, the model-cube
// buffer and every other irredundant constraint return at once.
//
// With '--glueupdate' the glue of a used constraint above tier 1 is
// recomputed over its currently assigned literals and replaces the stored
// one if smaller.  It never grows: the stored glue was counted when more
// of the constraint was assigned, and a constraint is not demoted by one
// analysis in which few of its literals happen to be assigned.

#include "internal.hpp"

#include <algorithm>
#include <cinttypes>

namespace miniqu {

void Internal::init_tiers () {
  tiers.tier1.fill (opts.tier1glue);
  tiers.tier2.fill (opts.tier2glue);
  for (auto &histogram : tiers.usage)
    histogram.fill (0);
  lim.retier = 2;
}

void Internal::mark_used (Constraint &c) {
  if (opts.tiers)
    c.set_used (c.glue () <= (uint32_t) tiers.tier2[index (c.kind ())] ? 2
                                                                       : 1);
}

void Internal::bump_constraint (Constraint &c) {
  if (!c.redundant ())
    return;
  const size_t k = index (c.kind ());
  stats.used[k]++;
  const uint32_t tier1 = (uint32_t) tiers.tier1[k];
  const uint32_t tier2 = (uint32_t) tiers.tier2[k];
  const uint32_t glue = c.glue ();
  // A moving limit makes glues below it matter too (CaDiCaL's cutoff).
  const uint32_t cutoff = opts.recomputetier ? (tier1 + 1) / 2 : tier1;
  if (opts.glueupdate && glue > cutoff) {
    const uint32_t updated = compute_glue (c.lits (), glue);
    if (updated < glue) {
      c.set_glue (updated);
      stats.glueupdates[k]++;
      stats.promoted[k] +=
          updated <= tier1 || (updated <= tier2 && glue > tier2);
      LOG ("glue %u -> %u", glue, updated);
    }
  }
  if (opts.recomputetier)
    tiers.usage[k][std::min<uint32_t> (c.glue (), Tiers::buckets - 1)]++;
  mark_used (c);
}

bool Internal::retiering () const {
  return opts.recomputetier && stats.conflicts >= lim.retier;
}

// The smallest glue, at least 1, up to which the uses of the histogram sum
// to 'percent' of the total.  CaDiCaL accumulates from bucket 0 too, so
// uses of glue 0 count for every limit.
static int cover (const std::array<int64_t, Tiers::buckets> &usage,
                  int64_t total, int percent) {
  const int64_t wanted = total * percent / 100;
  int64_t accumulated = usage[0];
  for (size_t glue = 1; glue < usage.size (); glue++) {
    accumulated += usage[glue];
    if (accumulated >= wanted)
      return (int) glue;
  }
  return Tiers::buckets - 1;
}

void Internal::retier () {
  stats.retiered++;
  lim.retier = stats.conflicts +
               (int64_t (1) << std::min<int64_t> (stats.retiered, 16));
  for (Kind kind : {Kind::Clause, Kind::Cube}) {
    const size_t k = index (kind);
    int64_t total = 0;
    for (int64_t uses : tiers.usage[k])
      total += uses;
    if (!total)
      continue;
    int tier1 = std::max (cover (tiers.usage[k], total, opts.tier1limit),
                          opts.tier1minglue);
    int tier2 = std::max (cover (tiers.usage[k], total, opts.tier2limit),
                          opts.tier2minglue);
    if (tier2 <= tier1)
      tier2 = tier1 + 1;
    if (tier1 == tiers.tier1[k] && tier2 == tiers.tier2[k])
      continue;
    tiers.tier1[k] = tier1;
    tiers.tier2[k] = tier2;
    VERBOSE (2, "retiered %" PRId64 " %s: tier 1 limit %d, tier 2 limit %d",
             stats.retiered, kind == Kind::Clause ? "clause" : "cube",
             tier1, tier2);
  }
}

void Internal::print_tier_limits () const {
  for (Kind kind : {Kind::Clause, Kind::Cube})
    MSG ("tier limits %s %d %d", kind == Kind::Clause ? "clause" : "cube",
         tiers.tier1[index (kind)], tiers.tier2[index (kind)]);
}

} // namespace miniqu
