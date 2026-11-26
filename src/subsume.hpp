#ifndef MINIQU_SUBSUME_HPP_INCLUDED
#define MINIQU_SUBSUME_HPP_INCLUDED

#include "lit.hpp"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace miniqu {

// Scratch state of subsumption ('subsume.cpp').  Everything is empty
// outside a round except 'since_elim'.
struct Subsumer {
  // The candidates of one kind, smaller ones first.
  struct Scheduled {
    uint32_t size;
    Ref ref;
  };
  std::vector<Scheduled> schedule;

  // One-watch lists: a constraint that was tried is connected to one of
  // its literals.  'head' (per literal) is the index + 1 of the newest
  // link of that literal in 'links', 0 for none; 'length' the number of
  // links of the literal.
  struct Link {
    Ref ref;
    uint32_t next; // index + 1 of the next link, 0 at the end
  };
  std::vector<uint32_t> head;
  std::vector<uint32_t> length;
  std::vector<Link> links;

  std::vector<uint32_t> noccs; // per literal: occurrences in the schedule
  std::vector<int8_t> marks;   // per literal: in the candidate being tried

  std::vector<Ref> shrunken; // strengthened in this round
  int64_t ticks = 0;         // literal visits of the round

  // The literals and the chain of a strengthening step, the literals it
  // removed (the pivot and what reduction took), and the constraint
  // before reduction when reduction emptied it ('found_empty').
  std::vector<Lit> lits;
  std::vector<Lit> removed;
  std::vector<Lit> move;
  std::vector<uint64_t> chain;

  // A round ran since the last elimination round (CaDiCaL: "make sure
  // there was a complete subsumption phase since last elimination").
  bool since_elim = false;
};

} // namespace miniqu

#endif
