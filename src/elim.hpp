#ifndef MINIQU_ELIM_HPP_INCLUDED
#define MINIQU_ELIM_HPP_INCLUDED

#include "lit.hpp"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace miniqu {

// A resolvent of the candidate being tried: 'size' literals from 'offset'
// in 'Eliminator::lits', derived from the two irredundant 'parents'.
struct Resolvent {
  size_t offset;
  uint32_t size;
  Ref parents[2];
};

// Scratch state of bounded variable elimination ('elim.cpp').  Everything
// is empty outside a round, except 'pending', which stays sized; no
// reference survives a round, so rounds cope with whatever happened to the
// databases in between.
struct Eliminator {
  // Occurrence lists of the round, for the literals of candidates only, at
  // '2 * index (lit) + index (kind)'.  They may hold garbage references,
  // which are dropped when a list is used.
  std::vector<std::vector<Ref>> occs;
  std::vector<Ref> &operator() (Kind kind, Lit l) {
    return occs[2 * (size_t) index (l) + index (kind)];
  }

  // Per variable: a unit resolvent on it waits to be assigned at the end of
  // the round, so it is no candidate in this round.
  std::vector<uint8_t> pending;

  // The resolvents of the candidate being tried.
  std::vector<Lit> lits;
  std::vector<Resolvent> resolvents;
  std::vector<Lit> resolvent; // the one being built
  std::vector<int8_t> marks;  // per literal: in the first parent

  int64_t ticks = 0; // literal visits of the round

  // With '--dl': a variable eliminated in this round is mentioned by a
  // dependency, which the end of the round resets.
  bool dependent = false;
};

} // namespace miniqu

#endif
