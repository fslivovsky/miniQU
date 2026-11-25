#ifndef MINIQU_FLAGS_HPP_INCLUDED
#define MINIQU_FLAGS_HPP_INCLUDED

namespace miniqu {

// Status of a variable that pre- and inprocessing change ('ftab' of
// 'Internal', one entry per variable, grown in 'add_var').
struct Flags {
  // Removed by bounded variable elimination ('elim.cpp'): no live
  // constraint contains the variable, and it is never assigned again.
  bool eliminated = false;
  // Scheduling marks of elimination ('--elimmark').  'elim': a constraint
  // containing the variable was deleted since its last attempt (or it was
  // never tried, or the bound grew), so it is tried in the next pass.
  // 'elimblocked': its last attempt failed on a *learnt* constraint (E2 or
  // E3), so the deletion of a learnt constraint marks it too; otherwise
  // only the deletion of an irredundant one does.
  bool elim = true;
  bool elimblocked = false;
};

} // namespace miniqu

#endif
