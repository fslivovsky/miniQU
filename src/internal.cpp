// Construction of the solver state, the top-level 'solve' and the search
// loop (ARCHITECTURE 7.1).
//
// Variables are created only while the formula is added, in prefix order
// (INV-ORDER, ARCHITECTURE 4.2); every per-variable array grows here
// except the watch lists ('size_watches').
//
// The loop is the one of the old 'search' / 'solve_' pair, flattened: each
// iteration propagates, and either analyses the conflict found, or stops
// when asked to, or restarts (and forgets the dependencies on their
// schedule, after the restart as in the old 'solve_'), or decides (after a
// reduction, if one is due).  When no decision variable is left, the
// clauses are satisfied (QDIMACS) and the initial cube taken from the
// assignment is analysed like any satisfied cube (4.5).  Analysis ends the
// search by deriving an empty constraint, which sets 'status'.

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
  if (opts.dl) {
    add_dependency_var ();
    if (heaps.empty ())
      heaps.emplace_back (scores);
  } else if (heaps.size () < prefix.blocks.size ())
    heaps.emplace_back (scores, prefix.blocks.back ().begin);
  if (decision)
    heaps.back ().push (v);
  LOG ("new %s variable %u, %sdecision, block %u",
       quant == Quant::Exists ? "existential" : "universal", v + 1,
       decision ? "" : "no ", prefix.depth (v));
  return v;
}

// The watch lists of all variables are allocated in one step when the
// first constraint is added (no variable is added after it) or, without
// constraints, when the search starts.  Growing the array of per-literal
// records one variable at a time would keep the old and the new array
// alive during each reallocation, which raised the peak memory by 8% on
// an instance with two million variables (STATUS.md M1-R2-T2).
void Internal::size_watches () {
  if (watches.size () < prefix.size ())
    watches.resize (prefix.size ());
}

void Internal::search () {
  profiles.enable (opts.profile);
  PROFILE_SCOPE (search);
  lim.restart = restart_interval (0);
  size_watches ();
  init_reduce ();
  init_tiers ();
  init_model_cube ();
  while (status == Status::Unknown) {
    if (const Ref conflict = propagate (); conflict != Ref::none)
      analyze (conflict);
    else if (terminated)
      break;
    else if (restarting ()) {
      restart ();
      if (resetting_dependencies ())
        reset_dependencies ();
    } else {
      // The size trigger of 'reduce' may stay true, so the loop goes on
      // to decide: see reduce.cpp.
      if (retiering ())
        retier ();
      if (reducing ())
        reduce ();
      if (!decide ())
        analyze (initial_cube ());
    }
  }
}

Status Internal::solve () {
  if (opts.ccminmode && opts.mode != 2 && !minimizing ())
    MSG ("warning: no learnt minimisation while a proof, trace or check "
         "is written (M1)");
  if (status == Status::Unknown)
    search ();
  // The old solver records the certificate on the trail as the search
  // left it, before going back to the root.
  record_certificate ();
  backtrack (0);
  return status;
}

} // namespace miniqu
