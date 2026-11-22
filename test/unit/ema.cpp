#include "ema.hpp"
#include "test.hpp"

#include <cmath>

using namespace miniqu;

static bool near (double a, double b) { return std::fabs (a - b) < 1e-12; }

int main () {
  // The first sample is returned exactly, however small alpha is.
  Ema e (0.01);
  CHECK (near (e.value (), 0));
  e.update (5);
  CHECK (near (e, 5));

  // A constant input stays constant despite the zero start.
  for (int i = 0; i < 100; i++)
    e.update (5);
  CHECK (near (e, 5));

  // Compared with the textbook formula for the corrected average.
  const double alpha = 0.25;
  Ema f (alpha);
  double biased = 0, power = 1;
  for (int i = 1; i <= 50; i++) {
    const double y = (double) (i % 7) - 2;
    f.update (y);
    biased = (1 - alpha) * biased + alpha * y;
    power *= 1 - alpha;
    CHECK (near (f.value (), biased / (1 - power)));
  }

  // Alpha one follows the input.
  Ema g (1.0);
  g.update (3);
  g.update (-1);
  CHECK (near (g, -1));

  return test_result ();
}
