#include "random.hpp"
#include "test.hpp"

using namespace miniqu;

int main () {
  // MiniSat's generator with its default seed, evaluated by hand for the
  // first step: seed = 91648253 * 1389796 mod 2147483647.
  Random r;
  const double first = r.drand ();
  const double expected =
      (double) ((91648253ull * 1389796ull) % 2147483647ull) / 2147483647;
  CHECK (first == expected);

  Random a (42), b (42);
  for (int i = 0; i < 1000; i++) {
    const double x = a.drand ();
    CHECK (x == b.drand ());
    CHECK (x >= 0 && x < 1);
  }
  for (int i = 0; i < 1000; i++) {
    const int k = a.irand (10);
    CHECK (k >= 0 && k < 10);
  }
  return test_result ();
}
