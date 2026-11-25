// The certificate block (ARCHITECTURE 10.4; the old
// 'saveOutermostAssignment'): the values of the decision variables of the
// outermost block that has decision variables, as the search left them.
// For a true formula whose outermost block is existential this assignment
// can be extended to a winning strategy, dually for a false formula whose
// outermost block is universal.
//
// A variable left unassigned gets the value true, which is how the old
// binary prints it.  This happens when the search ended before the block
// was complete, for instance when the formula was decided at the root.
//
// Decided by reduction ('root_move').  When the deciding empty constraint
// of kind K was obtained by reducing a derived constraint D (root
// simplification, vivification, elimination, an original), every literal
// of D is secondary, and D is implied by the formula.  The secondary player
// wins by making every literal of D vanish: its outer literals by its move,
// the inner ones by later moves.  Those values override the trail (which
// may leave them unassigned or, for the propagated literal of root
// simplification step 1, assign the opposite), in the certificate block
// only and only when that block belongs to the secondary player of K.
// Other variables of the block keep the trail value (or true): any value
// is a winning move for them.
//
// Nothing is derived, so there are no proof steps.  'Solver' translates the
// literals to user variables.

#include "internal.hpp"

#include <algorithm>

namespace miniqu {

void Internal::record_certificate () {
  certificate.clear ();
  const Block *block = nullptr;
  for (const Block &b : prefix.blocks) {
    for (Var v = b.begin; v < b.end; v++)
      if (prefix.vars[v].decision)
        certificate.push_back (mk_lit (v, val (mk_lit (v)) < 0));
    if (!certificate.empty ()) {
      block = &b;
      break;
    }
  }
  if (!block || root_move.empty () || status == Status::Unknown)
    return;
  const Kind kind = status == Status::False ? Kind::Clause : Kind::Cube;
  if (block->quant == primary (kind))
    return;
  for (const Lit l : root_move) {
    assert (!prefix.is_primary (kind, var (l)));
    const Var v = var (l);
    if (v < block->begin || v >= block->end || !prefix.vars[v].decision)
      continue;
    // 'kval (kind, vanished) < 0': false in a clause, true in a cube.
    const Lit vanished = kind == Kind::Clause ? ~l : l;
    const auto it = std::lower_bound (certificate.begin (),
                                      certificate.end (), mk_lit (v));
    assert (it != certificate.end () && var (*it) == v);
    *it = vanished;
  }
}

// 1 or -1 for a variable of the certificate, 0 for any other.
int Internal::certificate_value (Var v) const {
  const auto it = std::lower_bound (certificate.begin (),
                                    certificate.end (), mk_lit (v));
  if (it == certificate.end () || var (*it) != v)
    return 0;
  return sign (*it) ? -1 : 1;
}

} // namespace miniqu
