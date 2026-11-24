// Restarts (ARCHITECTURE 7.1, 9.4).  A restart keeps everything learnt and
// only undoes assignments, so it has no proof steps; it is a heuristic and
// every backtrack level is sound.  Being at level 0 afterwards, it is where
// '--check' verifies the invariants (ARCHITECTURE 9.6).
//
// '--restartmode=0' is the old schedule: the search restarts when the
// conflicts since the last restart reach the current interval.  The k-th
// interval (k = 0, 1, ...) is 'rfirst * luby (rinc, k)' with '--luby' (the
// default), otherwise 'rfirst * rinc^k', with 'rinc' in percent; both
// truncated to an integer as the old 'search (rest_base * restart_first)'
// does.
//
// '--restartmode=1' restarts on glue averages as CaDiCaL does: at least
// 'restartint' conflicts after the last restart, when the fast average of
// the glues of learnt constraints exceeds the slow one by 'restartmargin'
// percent, a sign that the search left the part of the space it learnt
// good constraints in.  Glues of clauses and of cubes are not comparable,
// so each kind has its own pair of averages and the pair of the kind
// learnt last decides.  A learnt dependency learns no constraint and
// leaves the averages alone.  The averages are updated in both modes (one
// multiplication per conflict), which changes nothing observable in
// mode 0.
//
// Trail reuse ('--reusetrail', CaDiCaL's 'reuse_trail'): after a restart
// the search would take the same decisions again as long as they still
// beat every unassigned candidate, so it backtracks only to the first level
// whose decision a candidate outscores.  Without '--dl' the candidate is
// the best unassigned variable of the heap of the decision's block, which
// approximates what the prefix-ordered search decides there: the first
// block with an unassigned variable is the decision's own block as long as
// the kept levels are complete up to it, and the later levels are the ones
// the criterion checks.  With '--dl' it is the best unassigned variable of
// the one heap.  The candidates are the ones unassigned now, not those
// after the backtrack, as in CaDiCaL.  A pending dependency reset needs
// level 0 (it puts root-assigned variables back into the heap), so then
// nothing is reused.  Root simplification also waits for level 0, which
// reuse mostly reaches after a learnt unit.

#include "internal.hpp"

#include <cmath>
#include <cstdint>

namespace miniqu {

// 'y' to the power of the k-th element (from 0) of the Luby sequence
// 0 0 1 0 0 1 2 0 0 1 0 0 1 2 3 ... (MiniSat's 'luby').  The sequence is
// made of finite prefixes of sizes 2^n - 1; find the one containing 'k',
// then descend into the left or right copy of the previous prefix.
static double luby (double y, int64_t k) {
  int64_t size = 1;
  int seq = 0;
  while (size < k + 1) {
    seq++;
    size = 2 * size + 1;
  }
  while (size - 1 != k) {
    size = (size - 1) >> 1;
    seq--;
    k = k % size;
  }
  return std::pow (y, seq);
}

int64_t Internal::restart_interval (int64_t restarts) const {
  const double base = opts.rinc / 100.0;
  const double factor = opts.luby ? luby (base, restarts)
                                  : std::pow (base, (double) restarts);
  const double interval = factor * opts.rfirst;
  // The geometric sequence leaves the integers after a few hundred
  // restarts; the old code would overflow there.
  return interval < (double) INT64_MAX / 2 ? (int64_t) interval
                                           : INT64_MAX / 2;
}

void Internal::init_restart () {
  lim.restart = opts.restartmode ? opts.restartint : restart_interval (0);
  lim.depreset = opts.depresetint;
  for (Averages &a : averages) {
    a.fast = Ema (1.0 / opts.emagluefast);
    a.slow = Ema (1.0 / opts.emaglueslow);
  }
}

void Internal::update_averages (Kind kind, uint32_t glue) {
  Averages &a = averages[index (kind)];
  a.fast.update (glue);
  a.slow.update (glue);
  last_learnt_kind = kind;
}

bool Internal::restarting () const {
  if (stats.conflicts < lim.restart)
    return false;
  if (!opts.restartmode)
    return true;
  const Averages &a = averages[index (last_learnt_kind)];
  return a.fast > (1 + opts.restartmargin / 100.0) * a.slow;
}

// The level a restart backtracks to.  Levels are checked from the first;
// 'best' caches the candidate of the heap the previous level used, which
// is the same heap for consecutive levels of one block.
int Internal::reuse_level () const {
  if (!opts.reusetrail || resetting_dependencies ())
    return 0;
  const Heap *cached = nullptr;
  Var best = no_var;
  for (int level = 1; level <= decision_level (); level++) {
    const Var decision =
        var (trail[control[static_cast<size_t> (level - 1)]]);
    const Heap *heap = &heap_of (decision);
    if (heap != cached) {
      cached = heap;
      best = heap->best_unskipped (
          [this] (Var v) { return val (mk_lit (v)) != 0; });
    }
    if (best != no_var && scores[decision] < scores[best])
      return level - 1;
  }
  return decision_level ();
}

void Internal::restart () {
  stats.restarts++;
  const int level = reuse_level ();
  if (level)
    stats.reused++;
  backtrack (level);
  if (opts.check && !decision_level ())
    check_invariants ();
  lim.restart = stats.conflicts + (opts.restartmode
                                       ? opts.restartint
                                       : restart_interval (stats.restarts));
  report ("restart");
}

} // namespace miniqu
