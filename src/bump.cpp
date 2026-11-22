// Variable scores: EVSIDS exactly as MiniSat (ARCHITECTURE 7.3).
//
// A bump adds 'score_inc' to the score of a variable, and after every
// learnt constraint 'score_inc' grows by the factor 1/decay, so that recent
// bumps weigh exponentially more than old ones.  When a score exceeds
// 1e100 all scores and the increment are scaled down by the same factor,
// which keeps the order.
//
// Which variables are bumped is the old solver's choice: every variable
// that enters the resolvent of an analysis (conflict, reasons; primary and
// secondary), and every variable that reduction removes from an initial
// cube ('model.cpp').
//
// Initial scores are 0, so that the first decisions follow variable order,
// unless '--seed=s' is given: then each variable, in creation order, starts
// with a score drawn by MiniSat's generator seeded with s, which is the
// baseline's '-rnd-init -rnd-seed=s'.  This is the only effect of the seed.
//
// Heuristic only: nothing here affects soundness or proofs.

#include "internal.hpp"

namespace miniqu {

namespace {

// The bounds of the old solver.
constexpr double max_initial_score = 1e-5;
constexpr double rescale_limit = 1e100;

} // namespace

// Called by 'add_var' for each new variable, in creation order.
double Internal::initial_score () {
  if (!opts.seed)
    return 0;
  if (scores.empty ())
    random = Random (opts.seed);
  return random.drand () * max_initial_score;
}

void Internal::bump_variable (Var v) {
  if ((scores[v] += score_inc) > rescale_limit) {
    for (double &score : scores)
      score /= rescale_limit;
    score_inc /= rescale_limit;
  }
  // Gate variables share the heap of their block but are never in it.
  Heap &heap = heap_of (v);
  if (heap.contains (v))
    heap.update (v);
}

void Internal::decay_scores () { score_inc *= 1000.0 / opts.vardecay; }

} // namespace miniqu
