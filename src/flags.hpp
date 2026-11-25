#ifndef MINIQU_FLAGS_HPP_INCLUDED
#define MINIQU_FLAGS_HPP_INCLUDED

namespace miniqu {

// Status of a variable that pre- and inprocessing change ('ftab' of
// 'Internal', one entry per variable, grown in 'add_var').
struct Flags {
  // Removed by bounded variable elimination ('elim.cpp'): no live
  // constraint contains the variable, and it is never assigned again.
  bool eliminated = false;
};

} // namespace miniqu

#endif
