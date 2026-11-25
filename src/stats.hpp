#ifndef MINIQU_STATS_HPP_INCLUDED
#define MINIQU_STATS_HPP_INCLUDED

#include <cstdint>
#include <cstdio>

namespace miniqu {

// Counters, incremented directly ('stats.conflicts++') and printed in one
// place.  Every counter appears in the machine-readable block
// 'c stat <name> <integer>' (per-kind counters as '<name>.clause' and
// '<name>.cube'), zero or not.  Renaming one is an interface change: the
// test matrix in tests/matrix.txt refers to these names (ARCHITECTURE 9.2).
//
// 'COUNTER' is a plain counter, 'KIND_COUNTER' one per 'Kind' (index with
// 'index (kind)').
#define STATS \
  COUNTER (conflicts) \
  COUNTER (decisions) \
  COUNTER (propagations) \
  COUNTER (ticks) \
  COUNTER (restarts) \
  COUNTER (reused) \
  KIND_COUNTER (learned) \
  KIND_COUNTER (learnedlits) \
  COUNTER (minimized) \
  COUNTER (minimizedchain) \
  COUNTER (dependencies) \
  COUNTER (depresets) \
  COUNTER (reductions) \
  KIND_COUNTER (reduced) \
  KIND_COUNTER (used) \
  KIND_COUNTER (glueupdates) \
  KIND_COUNTER (promoted) \
  COUNTER (retiered) \
  COUNTER (rootsimps) \
  COUNTER (rootunits) \
  COUNTER (rootstrengthened) \
  COUNTER (rootstrunits) \
  COUNTER (rootconflicts) \
  COUNTER (rootlits) \
  COUNTER (rootdeleted) \
  COUNTER (elimrounds) \
  COUNTER (eliminprounds) \
  COUNTER (elimskipped) \
  COUNTER (elimdelayed) \
  COUNTER (elimtried) \
  COUNTER (elimblockedother) \
  COUNTER (elimblockedright) \
  COUNTER (elimblockedbound) \
  COUNTER (elimunits) \
  KIND_COUNTER (eliminated) \
  KIND_COUNTER (resolvents) \
  KIND_COUNTER (elimdeleted) \
  KIND_COUNTER (elimlearnt) \
  KIND_COUNTER (elimsubsumed) \
  COUNTER (vivifyrounds) \
  COUNTER (vivifydecisions) \
  COUNTER (vivifyprops) \
  COUNTER (vivifyskipped) \
  COUNTER (vivifyunits) \
  COUNTER (vivifyrescheduled) \
  KIND_COUNTER (vivifychecked) \
  KIND_COUNTER (vivified) \
  KIND_COUNTER (vivifiedlits) \
  COUNTER (collections) \
  COUNTER (relocated) \
  COUNTER (modelcubes) \
  KIND_COUNTER (originals) \
  COUNTER (checked)

struct Stats {
#define COUNTER(NAME) int64_t NAME = 0;
#define KIND_COUNTER(NAME) int64_t NAME[2] = {0, 0};
  STATS
#undef COUNTER
#undef KIND_COUNTER

  // 'seconds' is the time the rates refer to.
  void print (FILE *, double seconds) const;
};

} // namespace miniqu

#endif
