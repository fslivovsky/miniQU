// Construction of the solver state and the top-level 'solve'.
//
// Variables are created only while the formula is added, in prefix order
// (INV-ORDER, ARCHITECTURE 4.2); every per-variable array grows here.  The
// search loop of ARCHITECTURE 7.1 is not there yet: 'solve' answers only
// formulas that the input decided.

#include "internal.hpp"

namespace miniqu {

Var Internal::add_var (Quant quant, bool decision, int proof_number) {
  const Var v = prefix.add_var (quant, decision, proof_number);
  const Var vars = v + 1;
  vals.resize (2 * (size_t) vars, 0);
  vtab.push_back (VarData{0, Ref::none, -1});
  scores.push_back (0);
  // The initial phase is false (porting note 6).
  phases.push_back (-1);
  watches.resize (vars);
  if (heaps.size () < prefix.blocks.size ())
    heaps.emplace_back (scores, prefix.blocks.back ().begin);
  if (decision)
    heaps.back ().push (v);
  LOG ("new %s variable %u, %sdecision, block %u",
       quant == Quant::Exists ? "existential" : "universal", v + 1,
       decision ? "" : "no ", prefix.depth (v));
  return v;
}

Status Internal::solve () { return status; }

} // namespace miniqu
