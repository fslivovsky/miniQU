// The common tail of the analyses (ARCHITECTURE 7.1, 7.5): from the
// literals left in the resolvent to a stored constraint, the backjump and
// the propagated asserting literal; or to the end of the search.
//
// Reduction comes first.  If no primary literal is left, the result is the
// empty constraint of the analysed kind: the empty clause (formula false)
// or the empty cube (formula true).  Otherwise the asserting literal goes
// to position 0 and a literal of the highest remaining level to position
// 1, the two literals the constraint is watched by; that level is the
// backjump level (0 for a unit).  After the backjump the asserting literal
// is the only non-vanished one, so the new constraint is its reason: a
// clause assigns it, a cube its negation.
//
// Glue is the number of distinct decision levels of the assigned literals,
// computed before the backjump unassigns them (porting note 8).  Learnt
// constraints are redundant, except units, which 'new_constraint' stores
// irredundant (ARCHITECTURE 4.3).
//
// Proof: the learnt constraint, or the empty one, is a derived step with
// the chain collected by the analysis (conflict id, then the reason ids in
// resolution order).  Reduction is part of the step, so INV-DERIVED holds.

#include "internal.hpp"
#include "proof.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

uint32_t Internal::compute_glue (std::span<const Lit> lits) {
  glue_levels.clear ();
  for (Lit l : lits)
    if (val (l))
      glue_levels.push_back (level (var (l)));
  std::sort (glue_levels.begin (), glue_levels.end ());
  return static_cast<uint32_t> (
      std::unique (glue_levels.begin (), glue_levels.end ()) -
      glue_levels.begin ());
}

// 'derived' holds the resolvent; 'asserting' is its asserting variable, or
// 'no_var' if every primary literal was resolved away.
void Internal::learn (Kind kind, Var asserting) {
  prefix.qreduce (derived, kind);
  assert (derived.empty () == (asserting == no_var));
  if (derived.empty ()) {
    const uint64_t id = next_id++;
    if (proof)
      proof->add_derived (id, kind, {}, chain);
    found_empty (kind);
    return;
  }

  const auto first =
      std::find_if (derived.begin (), derived.end (),
                    [=] (Lit l) { return var (l) == asserting; });
  std::iter_swap (derived.begin (), first);
  int jump = 0;
  if (derived.size () > 1) {
    const auto second = std::max_element (
        derived.begin () + 1, derived.end (), [this] (Lit a, Lit b) {
          return level (var (a)) < level (var (b));
        });
    std::iter_swap (derived.begin () + 1, second);
    jump = level (var (derived[1]));
  }
  assert (jump < level (asserting));

  const uint32_t glue = compute_glue (derived);
  stats.learned[index (kind)]++;
  stats.learnedlits[index (kind)] += (int64_t) derived.size ();
  backtrack (jump);
  const Ref ref = new_constraint (next_id++, kind, derived, true, glue);
  if (proof)
    proof->add_derived (deref (arena, ref), chain);
  assign (forced (kind, derived[0]), ref);
  decay_scores ();
  adjust_learnt_limit ();
}

} // namespace miniqu
