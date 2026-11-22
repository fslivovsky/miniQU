// Quantifier prefix and universal/existential reduction (ARCHITECTURE 4.2,
// 4.6).
//
// 'qreduce' is the reduction rule of Q-resolution: in a clause (cube) an
// universal (existential) literal may be dropped when no existential
// (universal) literal of the clause (cube) is quantified further inside.
// Because variables are numbered in prefix order, "further inside" is a
// comparison of indices, so the rule removes a suffix of the sorted
// literals.  It is a sound derivation of a constraint of the same kind and
// is one QLRUP step (derived from the unreduced constraint alone).

#include "prefix.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

Var Prefix::add_var (Quant quant, bool decision, int proof) {
  const Var v = size ();
  if (blocks.empty () || blocks.back ().quant != quant)
    blocks.push_back (Block{quant, v, v, 0});
  Block &b = blocks.back ();
  b.end = v + 1;
  b.unassigned += decision;
  const uint32_t depth = static_cast<uint32_t> (blocks.size () - 1);
  vars.push_back (VarInfo{quant, decision, depth, proof});
  return v;
}

void Prefix::qreduce (std::vector<Lit> &lits, Kind kind) const {
  std::sort (lits.begin (), lits.end ());
  auto end = lits.end ();
  while (end != lits.begin () && !is_primary (kind, var (end[-1])))
    --end;
  lits.erase (end, lits.end ());
}

} // namespace miniqu
