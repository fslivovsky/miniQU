#ifndef MINIQU_EMA_HPP_INCLUDED
#define MINIQU_EMA_HPP_INCLUDED

#include <cassert>

namespace miniqu {

// Exponential moving average with initialisation bias correction as in the
// ADAM method and CaDiCaL: 'biased' is the plain average started at zero,
// and 'value' divides it by 1 - beta^updates, so that the first updates are
// not dragged towards zero.
class Ema {
  double value_ = 0;   // corrected average
  double biased = 0;   // plain average
  double alpha = 0;    // weight of a new sample
  double beta = 1;     // 1 - alpha
  double exponent = 0; // beta^updates, 0 until the first update

public:
  Ema () = default;

  // 'a' is the weight of a new sample, about one over the window length.
  explicit Ema (double a) : alpha (a), beta (1 - a), exponent (beta != 0) {
    assert (a > 0 && a <= 1);
  }

  double value () const { return value_; }
  operator double () const { return value_; }

  void update (double y) {
    biased += alpha * (y - biased);
    if (exponent != 0) {
      exponent *= beta;
      assert (exponent < 1);
      value_ = biased / (1 - exponent);
    } else
      value_ = biased;
  }
};

} // namespace miniqu

#endif
