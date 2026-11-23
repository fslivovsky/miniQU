#include "heap.hpp"
#include "test.hpp"

#include <cstdint>
#include <random>
#include <vector>

using namespace miniqu;

// The reference: the baseline's heap (old solver, commit c39005a,
// 'minisat/mtl/Heap.h' with the strict order of 'VarOrderLt'), transcribed
// operation by operation (positions unsigned, 'absent' for MiniSat's -1).
class MinisatHeap {
  static constexpr uint32_t absent = UINT32_MAX;
  const std::vector<double> &activity;
  std::vector<Var> heap;
  std::vector<uint32_t> indices;

  bool lt (Var x, Var y) const { return activity[x] > activity[y]; }
  static uint32_t parent (uint32_t i) { return (i - 1) >> 1; }
  size_t size () const { return heap.size (); }

  void percolate_up (uint32_t i) {
    const Var x = heap[i];
    while (i != 0 && lt (x, heap[parent (i)])) {
      heap[i] = heap[parent (i)];
      indices[heap[i]] = i;
      i = parent (i);
    }
    heap[i] = x;
    indices[x] = i;
  }

  void percolate_down (uint32_t i) {
    const Var x = heap[i];
    while (2 * i + 1 < size ()) {
      const uint32_t left = 2 * i + 1, right = 2 * i + 2;
      const uint32_t child =
          right < size () && lt (heap[right], heap[left]) ? right : left;
      if (!lt (heap[child], x))
        break;
      heap[i] = heap[child];
      indices[heap[i]] = i;
      i = child;
    }
    heap[i] = x;
    indices[x] = i;
  }

public:
  explicit MinisatHeap (const std::vector<double> &a)
      : activity (a), indices (a.size (), absent) {}

  bool empty () const { return heap.empty (); }
  bool in_heap (Var k) const { return indices[k] != absent; }

  void insert (Var k) {
    indices[k] = static_cast<uint32_t> (size ());
    heap.push_back (k);
    percolate_up (indices[k]);
  }

  void decrease (Var k) { percolate_up (indices[k]); }

  void remove (Var k) {
    const uint32_t k_pos = indices[k];
    indices[k] = absent;
    if (k_pos + 1 < size ()) {
      heap[k_pos] = heap.back ();
      indices[heap[k_pos]] = k_pos;
      heap.pop_back ();
      percolate_down (k_pos);
    } else
      heap.pop_back ();
  }

  Var remove_min () {
    const Var x = heap[0];
    heap[0] = heap.back ();
    indices[heap[0]] = 0;
    indices[x] = absent;
    heap.pop_back ();
    if (size () > 1)
      percolate_down (0);
    return x;
  }
};

// Random operations with few distinct scores, so that ties are frequent:
// every pop must give the reference's variable.  Scores only grow, as with
// bumping.
static void test_against_minisat () {
  const Var n = 50;
  std::mt19937 rng (12345);
  const auto below = [&rng] (uint32_t bound) {
    return static_cast<uint32_t> (rng () % bound);
  };
  std::vector<double> scores (n, 0);
  Heap heap (scores);
  MinisatHeap reference (scores);

  for (int step = 0; step < 50000; step++) {
    const Var v = below (n);
    switch (below (5)) {
    case 0:
    case 1:
      if (!reference.in_heap (v)) {
        heap.push (v);
        reference.insert (v);
      }
      break;
    case 2:
      if (!reference.empty ()) {
        const Var expected = reference.remove_min ();
        CHECK_EQ (heap.top (), expected);
        CHECK_EQ (heap.pop (), expected);
      }
      break;
    case 3:
      if (below (4) == 0)
        scores[v] += 1;
      if (reference.in_heap (v)) {
        heap.update (v);
        reference.decrease (v);
      }
      break;
    case 4:
      if (reference.in_heap (v)) {
        heap.remove (v);
        reference.remove (v);
      }
      break;
    }
    CHECK_EQ (heap.contains (v), reference.in_heap (v));
    CHECK_EQ (heap.empty (), reference.empty ());
  }
}

// Equal scores are not ordered by index: each pop moves the last variable
// to the top, where it stays.
static void test_ties () {
  std::vector<double> scores (5, 0);
  Heap heap (scores);
  for (Var v = 0; v < 5; v++)
    heap.push (v);
  for (Var expected : {0u, 4u, 3u, 2u, 1u})
    CHECK_EQ (heap.pop (), expected);
}

// Removing sifts down only: 6 (score 6) replaces 3 below 1 (score 3) and
// stays there, so 5 (score 5) is popped before it.
static void test_remove_sifts_down_only () {
  std::vector<double> scores{10, 3, 8, 1, 2, 5, 6};
  Heap heap (scores);
  for (Var v = 0; v < 7; v++)
    heap.push (v);
  heap.remove (3);
  for (Var expected : {0u, 2u, 5u, 6u, 1u, 4u})
    CHECK_EQ (heap.pop (), expected);
}

// A heap starting at a later variable (one per quantifier block) works the
// same and never claims variables before its start.
static void test_offset () {
  std::vector<double> scores (50, 0);
  Heap block (scores, 40);
  CHECK (!block.contains (3) && !block.contains (45));
  for (Var v : {45u, 41u, 49u, 40u})
    block.push (v);
  CHECK (block.contains (40) && block.contains (49) && !block.contains (3));
  scores[41] = 100;
  block.update (41);
  CHECK_EQ (block.pop (), 41u);
  CHECK_EQ (block.size (), 3u);
  block.remove (45);
  CHECK (!block.contains (45));
}

int main () {
  test_against_minisat ();
  test_ties ();
  test_remove_sifts_down_only ();
  test_offset ();
  return test_result ();
}
