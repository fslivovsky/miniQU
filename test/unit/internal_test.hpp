#ifndef MINIQU_INTERNAL_TEST_HPP_INCLUDED
#define MINIQU_INTERNAL_TEST_HPP_INCLUDED

// Support for tests that drive 'Internal' directly.  Literals are written
// as in DIMACS over internal variables counted from 1: 3 is variable 2,
// -3 its negation.

#include "internal.hpp"

#include <cstdlib>
#include <initializer_list>
#include <vector>

inline miniqu::Lit L (int dimacs) {
  return miniqu::mk_lit ((miniqu::Var) std::abs (dimacs) - 1, dimacs < 0);
}

inline std::vector<miniqu::Lit> lits (std::initializer_list<int> dimacs) {
  std::vector<miniqu::Lit> result;
  for (int d : dimacs)
    result.push_back (L (d));
  return result;
}

// One character per variable, in prefix order: 'e' / 'a' an existential /
// universal decision variable, 'E' / 'A' one that is never decided.
inline void declare (miniqu::Internal &internal, const char *prefix) {
  for (const char *p = prefix; *p; p++) {
    const bool universal = *p == 'a' || *p == 'A';
    const bool decision = *p == 'e' || *p == 'a';
    internal.add_var (universal ? miniqu::Quant::Forall
                                : miniqu::Quant::Exists,
                      decision, (int) (p - prefix) + 1);
  }
}

// Adds an original and returns the reference of the constraint stored
// last, which is the new one if it was stored.
inline miniqu::Ref add (miniqu::Internal &internal, miniqu::Kind kind,
                        std::initializer_list<int> dimacs) {
  std::vector<miniqu::Lit> ls = lits (dimacs);
  internal.add_original (kind, ls, 0);
  const std::vector<miniqu::Ref> &list =
      internal.irredundant[miniqu::index (kind)];
  return list.empty () ? miniqu::Ref::none : list.back ();
}

inline std::vector<miniqu::Lit> stored (const miniqu::Internal &internal,
                                        miniqu::Ref ref) {
  const miniqu::Constraint &c = deref (internal.arena, ref);
  return {c.begin (), c.end ()};
}

// Assigns 'dimacs' as a decision on a new level.
inline void decide (miniqu::Internal &internal, int dimacs) {
  internal.new_level ();
  internal.assign (L (dimacs), miniqu::Ref::none);
}

#endif
