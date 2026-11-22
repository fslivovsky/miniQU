// Construction of the solver state, the top-level 'solve' and the search
// loop (ARCHITECTURE 7.1).
//
// Variables are created only while the formula is added, in prefix order
// (INV-ORDER, ARCHITECTURE 4.2); every per-variable array grows here.
//
// The loop is the one of the old 'search' / 'solve_' pair, flattened: each
// iteration propagates, and either analyses the conflict found, or stops
// when asked to, or restarts, or decides (after a reduction, if one is
// due).  When no decision variable is left, the clauses are satisfied
// (QDIMACS) and the initial cube taken from the assignment is analysed like
// any satisfied cube (4.5).  Analysis ends the search by deriving an empty
// constraint, which sets 'status'.

#include "internal.hpp"

namespace miniqu {

Var Internal::add_var (Quant quant, bool decision, int proof_number) {
  const Var v = prefix.add_var (quant, decision, proof_number);
  const Var vars = v + 1;
  vals.resize (2 * (size_t) vars, 0);
  vtab.push_back (VarData{0, Ref::none, -1});
  scores.push_back (initial_score ());
  // The initial phase is false (porting note 6).
  phases.push_back (-1);
  seen.push_back (0);
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

void Internal::search () {
  profiles.enable (opts.profile);
  lim.restart = restart_interval (0);
  init_reduce ();
  init_model_cube ();
  while (status == Status::Unknown) {
    if (const Ref conflict = propagate (); conflict != Ref::none)
      analyze (conflict);
    else if (terminated)
      break;
    else if (restarting ())
      restart ();
    else {
      // The size trigger of 'reduce' may stay true, so the loop goes on
      // to decide: see reduce.cpp.
      if (reducing ())
        reduce ();
      if (!decide ())
        analyze (initial_cube ());
    }
  }
}

Status Internal::solve () {
  if (status == Status::Unknown)
    search ();
  // The old solver records the certificate on the trail as the search
  // left it, before going back to the root.
  record_certificate ();
  backtrack (0);
  return status;
}

} // namespace miniqu
