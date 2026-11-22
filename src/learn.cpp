// The common tail of the analyses (ARCHITECTURE 7.1, 7.5): from the
// literals left in the resolvent to a stored constraint, the backjump and
// the propagated asserting literal; or to the end of the search.
//
// Modes 0 and 1 ('learn'): minimisation first (if enabled, below), then
// reduction.  If no primary literal is left, the result is the empty
// constraint of the analysed kind: the empty clause (formula false) or the
// empty cube (formula true).  Otherwise the asserting literal goes to
// position 0 and a literal of the highest remaining level to position 1,
// the two literals the constraint is watched by.  Mode 2 ('analyze_ldq')
// chooses the two positions itself and enters at 'learn_watched'.  The
// level of position 1 is the backjump level (0 for a unit).  After the
// backjump the asserting literal is the only non-vanished one (mode 2:
// the only one that is not vanished or a secondary literal to its right),
// so the new constraint is its reason: a clause assigns it, a cube its
// negation.
//
// Minimisation ('minimize.cpp', '--ccminmode') runs where the old
// 'finishLearnt' ran it, for the resolvents of 'analyze_q' and
// 'analyze_qu', with the asserting literal at position 0.  In M1 it is off
// while a tracer is connected (ARCHITECTURE 7.5, 8.1): the chain of the
// analysis does not cover the reasons it resolves with.
//
// Glue is the number of distinct decision levels of the assigned literals,
// computed before the backjump unassigns them (porting note 8).  Learnt
// constraints are redundant, except units, which 'new_constraint' stores
// irredundant (ARCHITECTURE 4.3).
//
// In mode 1 the asserting literal may be secondary (QU-resolution
// propagates such literals too).  It is never removed by reduction there:
// 'analyze_qu' keeps only secondary literals left of a primary one.
//
// A learnt dependency (an analysis met a decision x that has to be
// resolved away to reduce y) backtracks below x, as the old 'search' does,
// and records it ('depend.cpp').  The scores are not decayed and the
// learnt limit is not adjusted: no constraint is learnt.
//
// Proof: the learnt constraint, or the empty one, is a derived step with
// the chain collected by the analysis (conflict id, then the reason ids in
// resolution order).  Reduction is part of the step, so INV-DERIVED holds.
// A dependency derives nothing.  Mode 2 has no tracer.

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

bool Internal::minimizing () const { return opts.ccminmode && !proof; }

// 'derived' holds the resolvent; 'asserting' is its asserting variable, or
// 'no_var' if every primary literal was resolved away.
void Internal::learn (Kind kind, Var asserting) {
  assert (opts.mode != 2);
  const auto move_to_front = [this] (Var v) {
    const auto it = std::find_if (derived.begin (), derived.end (),
                                  [=] (Lit l) { return var (l) == v; });
    assert (it != derived.end ());
    std::iter_swap (derived.begin (), it);
  };
  if (minimizing () && asserting != no_var) {
    move_to_front (asserting);
    minimize (derived, kind);
  }
  prefix.qreduce (derived, kind);
  assert (derived.empty () == (asserting == no_var));
  if (derived.empty ()) {
    learn_empty (kind);
    return;
  }
  move_to_front (asserting);
  if (derived.size () > 1) {
    const auto second = std::max_element (
        derived.begin () + 1, derived.end (), [this] (Lit a, Lit b) {
          return level (var (a)) < level (var (b));
        });
    std::iter_swap (derived.begin () + 1, second);
  }
  learn_watched (kind);
}

// 'derived[0]' is the asserting literal, 'derived[1]' (if any) a literal
// of the backjump level.
void Internal::learn_watched (Kind kind) {
  const int jump = derived.size () > 1 ? level (var (derived[1])) : 0;
  assert (jump < level (var (derived[0])));
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

void Internal::learn_empty (Kind kind) {
  const uint64_t id = next_id++;
  if (proof)
    proof->add_derived (id, kind, {}, chain);
  found_empty (kind);
}

void Internal::learn_dependency (Var x, Var y) {
  backtrack (level (x) - 1);
  record_dependency (x, y);
}

} // namespace miniqu
