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
//
// A heap only ever holds variables from 'offset' on, and its position table
// starts there: the solver keeps one heap per quantifier block, which would
// otherwise cost a table over all variables per block.
class Heap {
  static constexpr uint32_t absent = UINT32_MAX;

  const std::vector<double> *scores;
  Var offset;
  std::vector<Var> heap;
  std::vector<uint32_t> position; // per variable - offset, or 'absent'

  uint32_t &position_of (Var v) {
    assert (v >= offset);
    if (v - offset >= position.size ())
      position.resize ((size_t) (v - offset) + 1, absent);
    return position[v - offset];
  }

  bool before (Var a, Var b) const {
    const double sa = (*scores)[a], sb = (*scores)[b];
    return sa > sb || (sa == sb && a < b);
  }

  void place (Var v, uint32_t i) {
    heap[i] = v;
    position[v - offset] = i;
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
  explicit Heap (const std::vector<double> &s, Var first = 0)
      : scores (&s), offset (first) {}

  bool empty () const { return heap.empty (); }
  size_t size () const { return heap.size (); }

  bool contains (Var v) const {
    return v >= offset && v - offset < position.size () &&
           position[v - offset] != absent;
  }

  Var top () const {
    assert (!empty ());
    return heap[0];
  }

  void push (Var v) {
    assert (!contains (v));
    heap.push_back (v);
    const uint32_t i = static_cast<uint32_t> (heap.size () - 1);
    position_of (v) = i;
    sift_up (i);
  }

  Var pop () {
    assert (!empty ());
    const Var result = heap[0];
    const Var last = heap.back ();
    heap.pop_back ();
    position[result - offset] = absent;
    if (!heap.empty ()) {
      place (last, 0);
      sift_down (0);
    }
    return result;
  }

  void remove (Var v) {
    assert (contains (v));
    const uint32_t i = position[v - offset];
    const Var last = heap.back ();
    heap.pop_back ();
    position[v - offset] = absent;
    if (i < heap.size ()) {
      place (last, i);
      sift_up (i);
      sift_down (position[last - offset]);
    }
  }

  // Restores the order after the score of 'v' changed in either direction;
  // inserts 'v' if it is not in the heap.
  void update (Var v) {
    if (!contains (v)) {
      push (v);
      return;
    }
    sift_up (position[v - offset]);
    sift_down (position[v - offset]);
  }

  void clear () {
    for (Var v : heap)
      position[v - offset] = absent;
    heap.clear ();
  }

  // Replaces the contents by exactly the given variables.
  void build (std::span<const Var> vars) {
    clear ();
    for (Var v : vars) {
      uint32_t &p = position_of (v);
      assert (p == absent);
      heap.push_back (v);
      p = static_cast<uint32_t> (heap.size () - 1);
    }
    for (uint32_t i = static_cast<uint32_t> (heap.size ()) / 2; i-- > 0;)
      sift_down (i);
  }
};

} // namespace miniqu

#endif
