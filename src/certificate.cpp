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
// Nothing is derived, so there are no proof steps.  'Solver' translates the
// literals to user variables.

#include "internal.hpp"

#include <algorithm>

namespace miniqu {

void Internal::record_certificate () {
  certificate.clear ();
  for (const Block &b : prefix.blocks) {
    for (Var v = b.begin; v < b.end; v++)
      if (prefix.vars[v].decision)
        certificate.push_back (mk_lit (v, val (mk_lit (v)) < 0));
    if (!certificate.empty ())
      break;
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
