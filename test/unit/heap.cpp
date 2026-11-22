#include "heap.hpp"
#include "test.hpp"

#include <algorithm>
#include <random>
#include <vector>

using namespace miniqu;

// The reference: the member with the best (score, then smaller index).
static Var naive_top (const std::vector<double> &scores,
                      const std::vector<bool> &in) {
  Var best = UINT32_MAX;
  for (Var v = 0; v < in.size (); v++)
    if (in[v] && (best == UINT32_MAX || scores[v] > scores[best]))
      best = v;
  return best;
}

int main () {
  const Var n = 50;
  std::mt19937 rng (12345);
  const auto below = [&rng] (uint32_t bound) {
    return static_cast<uint32_t> (rng () % bound);
  };
  // Few distinct scores, so that ties are frequent.
  std::vector<double> scores (n, 0);
  Heap heap (scores);
  std::vector<bool> in (n, false);

  for (int step = 0; step < 20000; step++) {
    const Var v = below (n);
    switch (below (5)) {
    case 0:
      if (!in[v]) {
        heap.push (v);
        in[v] = true;
      }
      break;
    case 1:
      if (!heap.empty ()) {
        const Var expected = naive_top (scores, in);
        CHECK_EQ (heap.top (), expected);
        CHECK_EQ (heap.pop (), expected);
        in[expected] = false;
      }
      break;
    case 2:
      scores[v] = (double) (below (6));
      heap.update (v);
      in[v] = true; // update inserts
      break;
    case 3:
      CHECK_EQ (heap.contains (v), (bool) in[v]);
      break;
    case 4:
      if (below (200) == 0) {
        heap.clear ();
        in.assign (n, false);
      }
      break;
    }
    CHECK_EQ (heap.size (),
              (size_t) std::count (in.begin (), in.end (), true));
  }

  // Draining yields descending scores, ties by ascending variable.
  heap.clear ();
  for (Var v = 0; v < n; v++)
    scores[v] = (double) (v % 4);
  std::vector<Var> all (n);
  for (Var v = 0; v < n; v++)
    all[v] = v;
  std::shuffle (all.begin (), all.end (), rng);
  heap.build (all);
  Var previous = UINT32_MAX;
  while (!heap.empty ()) {
    const Var v = heap.pop ();
    if (previous != UINT32_MAX) {
      CHECK (scores[previous] > scores[v] ||
             (scores[previous] == scores[v] && previous < v));
    }
    previous = v;
  }

  // 'build' replaces earlier contents.
  heap.push (3);
  const Var two[2] = {7, 9};
  heap.build (two);
  CHECK (!heap.contains (3) && heap.contains (7) && heap.contains (9));
  CHECK_EQ (heap.size (), 2u);

  return test_result ();
}
