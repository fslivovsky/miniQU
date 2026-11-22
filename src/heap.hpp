#ifndef MINIQU_HEAP_HPP_INCLUDED
#define MINIQU_HEAP_HPP_INCLUDED

#include "lit.hpp"

#include <cassert>
#include <cstdint>
#include <span>
#include <vector>

namespace miniqu {

// Indexed binary max-heap on variables, ordered by a score vector owned by
// the solver (so that bumping writes the score and calls 'update').  Equal
// scores are ordered by the smaller variable first, which makes decisions
// reproducible and independent of the history of heap operations.
// The score vector must outlive the heap and cover every variable pushed.
class Heap {
  static constexpr uint32_t absent = UINT32_MAX;

  const std::vector<double> *scores;
  std::vector<Var> heap;
  std::vector<uint32_t> position; // per variable, 'absent' if not in heap

  bool before (Var a, Var b) const {
    const double sa = (*scores)[a], sb = (*scores)[b];
    return sa > sb || (sa == sb && a < b);
  }

  void place (Var v, uint32_t i) {
    heap[i] = v;
    position[v] = i;
  }

  void sift_up (uint32_t i) {
    const Var v = heap[i];
    while (i > 0) {
      const uint32_t parent = (i - 1) / 2;
      if (!before (v, heap[parent]))
        break;
      place (heap[parent], i);
      i = parent;
    }
    place (v, i);
  }

  void sift_down (uint32_t i) {
    const Var v = heap[i];
    const uint32_t n = static_cast<uint32_t> (heap.size ());
    for (;;) {
      uint32_t child = 2 * i + 1;
      if (child >= n)
        break;
      if (child + 1 < n && before (heap[child + 1], heap[child]))
        child++;
      if (!before (heap[child], v))
        break;
      place (heap[child], i);
      i = child;
    }
    place (v, i);
  }

public:
  explicit Heap (const std::vector<double> &s) : scores (&s) {}

  bool empty () const { return heap.empty (); }
  size_t size () const { return heap.size (); }

  bool contains (Var v) const {
    return v < position.size () && position[v] != absent;
  }

  Var top () const {
    assert (!empty ());
    return heap[0];
  }

  void push (Var v) {
    assert (!contains (v));
    if (v >= position.size ())
      position.resize ((size_t) v + 1, absent);
    heap.push_back (v);
    position[v] = static_cast<uint32_t> (heap.size () - 1);
    sift_up (position[v]);
  }

  Var pop () {
    assert (!empty ());
    const Var result = heap[0];
    const Var last = heap.back ();
    heap.pop_back ();
    position[result] = absent;
    if (!heap.empty ()) {
      place (last, 0);
      sift_down (0);
    }
    return result;
  }

  // Restores the order after the score of 'v' changed in either direction;
  // inserts 'v' if it is not in the heap.
  void update (Var v) {
    if (!contains (v)) {
      push (v);
      return;
    }
    sift_up (position[v]);
    sift_down (position[v]);
  }

  void clear () {
    for (Var v : heap)
      position[v] = absent;
    heap.clear ();
  }

  // Replaces the contents by exactly the given variables.
  void build (std::span<const Var> vars) {
    clear ();
    for (Var v : vars) {
      if (v >= position.size ())
        position.resize ((size_t) v + 1, absent);
      assert (position[v] == absent);
      heap.push_back (v);
      position[v] = static_cast<uint32_t> (heap.size () - 1);
    }
    for (uint32_t i = static_cast<uint32_t> (heap.size ()) / 2; i-- > 0;)
      sift_down (i);
  }
};

} // namespace miniqu

#endif
