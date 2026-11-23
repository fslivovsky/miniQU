// Usage marks and glue updates of learnt constraints (ARCHITECTURE 5.2,
// 9.1; CaDiCaL's 'bump_clause', 'recompute_glue' and 'promote_clause').
//
// Class: heuristic only.  There is no QBF side condition and no proof step:
// the marks and the glue decide which learnt constraints 'reduce.cpp'
// deletes, and deleting a learnt constraint is always sound.  Clauses and
// cubes are treated alike; every counter is per kind, because their glue
// distributions differ.
//
// Tiers by glue: tier 1 is 'glue <= --tier1glue' and never deleted, tier 2
// is 'glue <= --tier2glue', tier 3 the rest.  A learnt constraint carries
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

namespace miniqu {

void Internal::mark_used (Constraint &c) {
  if (opts.tiers)
    c.set_used (c.glue () <= (uint32_t) opts.tier2glue ? 2 : 1);
}

void Internal::bump_constraint (Constraint &c) {
  if (!c.redundant ())
    return;
  const size_t k = index (c.kind ());
  stats.used[k]++;
  const uint32_t tier1 = (uint32_t) opts.tier1glue;
  const uint32_t tier2 = (uint32_t) opts.tier2glue;
  const uint32_t glue = c.glue ();
  if (opts.glueupdate && glue > tier1) {
    const uint32_t updated = compute_glue (c.lits (), glue);
    if (updated < glue) {
      c.set_glue (updated);
      stats.glueupdates[k]++;
      stats.promoted[k] +=
          updated <= tier1 || (updated <= tier2 && glue > tier2);
      LOG ("glue %u -> %u", glue, updated);
    }
  }
  mark_used (c);
}

} // namespace miniqu
