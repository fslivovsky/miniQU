#ifndef MINIQU_VIVIFY_HPP_INCLUDED
#define MINIQU_VIVIFY_HPP_INCLUDED

#include "lit.hpp"

#include <cstdint>
#include <vector>

namespace miniqu {

// Scratch state of vivification ('vivify.cpp').  Everything is empty (and
// 'in_candidate' all zero) outside the treatment of one candidate, except
// 'candidates', 'counts' (all zero between passes) and 'phases', which
// live for one round.  No reference
// survives a round.
struct Vivifier {
  std::vector<Ref> candidates;  // of the kind being vivified, newest last
  std::vector<int8_t> phases;   // saved phases, restored after the round
  std::vector<uint32_t> counts; // per 'index (lit)': occurrences in the
                                // candidates of the current pass
  std::vector<Lit> order;       // literals of the candidate, in visit order
  std::vector<uint8_t>
      in_candidate;            // per variable: occurs in the candidate
  std::vector<Var> touched;    // variables whose 'seen' was set
  std::vector<Lit> lits;       // the derived constraint 'D'
  std::vector<Lit> unreduced;  // 'D' before reduction (certificate)
  std::vector<uint64_t> chain; // its antecedents, only with a proof
  std::vector<uint64_t> units; // root units of the chain
};

} // namespace miniqu

#endif
