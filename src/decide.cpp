// Decisions (ARCHITECTURE 7.3; the old 'pickBranchLit').
//
// Without dependency learning decisions follow the prefix: the current
// block is the first one that still has an unassigned decision variable,
// and the variable is the one with the highest score in the heap of that
// block (ties: as the heap operations leave them).  Every unassigned
// decision variable is in the heap of its block ('backtrack' re-inserts
// it), while assigned ones are dropped lazily when they come to the top.
// Gate variables are never in a heap and never counted in
// 'Block::unassigned' (porting note 10), so a block is complete once its
// input variables are assigned, whatever its gates do.
//
// With '--dl' there is one heap over all decision variables, and the
// variable is the best one whose watched dependency is assigned
// ('depend.cpp').  Popped variables that are assigned or not eligible are
// dropped; 'depend.cpp' and 'backtrack' put the latter back in time.
// Since dependencies are acyclic the heap cannot run empty while a
// decision variable is unassigned.  As in the old 'pickBranchLit' the
// heap is popped until it is empty when every decision variable is
// assigned: what it holds then is assigned anyway, and later decisions
// depend on which variables the backtrack finds in it.
//
// The value is the saved phase, initially false (porting note 6; the old
// 'polarity' starts true, which is MiniSat's sign of the negative literal).
//
// Nothing is derived here, so there are no proof steps.

#include "internal.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

// The old 'isEligibleDecision'.  In prefix order: every block further out
// of the other quantifier is assigned, which taking the first incomplete
// block guarantees, so this is only asserted.  With dependency learning:
// the watched dependency is assigned.
bool Internal::eligible (Var v) const {
  if (opts.dl) {
    const std::vector<Var> &on = depend.on[v];
    return on.empty () || val (mk_lit (on.front ()));
  }
  const Quant quant = prefix.quant (v);
  for (uint32_t d = 0; d < prefix.depth (v); d++) {
    const Block &b = prefix.blocks[d];
    if (b.quant != quant && b.unassigned > 0)
      return false;
  }
  return true;
}

// Returns false if every decision variable is assigned.
bool Internal::decide () {
  const auto block =
      std::find_if (prefix.blocks.begin (), prefix.blocks.end (),
                    [] (const Block &b) { return b.unassigned > 0; });
  Var v;
  if (opts.dl) {
    update_dependency_watches ();
    Heap &heap = heaps[0];
    do {
      if (heap.empty ()) {
        if (block != prefix.blocks.end ())
          fatal ("internal error: no eligible decision variable");
        return false;
      }
      v = heap.pop ();
    } while (val (mk_lit (v)) || !eligible (v));
  } else {
    if (block == prefix.blocks.end ())
      return false;
    Heap &heap = heaps[(size_t) (block - prefix.blocks.begin ())];
    do {
      assert (!heap.empty ());
      v = heap.pop ();
    } while (val (mk_lit (v)));
    assert (eligible (v));
  }
  stats.decisions++;
  new_level ();
  const Lit decision = mk_lit (v, phases[v] < 0);
  LOG ("decide %s%u", sign (decision) ? "-" : "", v + 1);
  assign (decision, Ref::none);
  return true;
}

} // namespace miniqu
