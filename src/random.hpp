#ifndef MINIQU_RANDOM_HPP_INCLUDED
#define MINIQU_RANDOM_HPP_INCLUDED

namespace miniqu {

// MiniSat's multiplicative congruential generator, bit for bit, so that
// initial scores seeded with the same number can equal those of the old
// solver ('-rnd-init -rnd-seed=s').  The seed must not be zero.
class Random {
  double seed;

public:
  explicit Random (double s = 91648253) : seed (s) {}

  // Uniform in [0, 1).
  double drand () {
    seed *= 1389796;
    const int q = (int) (seed / 2147483647);
    seed -= (double) q * 2147483647;
    return seed / 2147483647;
  }

  // Uniform in [0, size).
  int irand (int size) { return (int) (drand () * size); }
};

} // namespace miniqu

#endif
