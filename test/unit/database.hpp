#ifndef MINIQU_DATABASE_TEST_HPP_INCLUDED
#define MINIQU_DATABASE_TEST_HPP_INCLUDED

// A hand-built database of learnt constraints for the tests of 'reduce'
// and 'garbage_collect'.  Prefix "eeaaee": variables 1, 2 existential,
// 3, 4 universal, 5, 6 existential, so clauses must contain 5 or 6 and
// cubes 3 or 4 (INV-REDUCED).
//
//   clauses  glue size            cubes      glue size
//   A {1 5}    1    2             U1 {-1 3}    1    2
//   B {2 5}    2    2             U2 {-1 -3 4} 3    3
//   C {1 2 5}  3    3             U3 {-1 2 4}  3    3
//   D {1 3 6}  3    3             U4 {-1 -2 3 -4}  4  4
//   H {-2 4 5} 3    3             U5 {-1 -2 -3 4}  4  4
//   I {3 6}    4    2             Q  {3 4}     6    2   reason
//   E {1 2 3 5}  4  4
//   G {2 3 4 6}  5  4
//   R {-1 5}   6    2   reason
//
// Deciding 1 and then 3 makes R the reason of 5 and Q that of -4; no
// other constraint propagates.
//
// A traced database has a recorder connected before the first constraint,
// so that its constraints store ids (ARCHITECTURE 5.2); the others do not.

#include "internal_test.hpp"
#include "proof.hpp"
#include "recorder.hpp"
#include "test.hpp"

#include <memory>

struct Database {
  miniqu::Internal internal;
  miniqu::Proof proof{&internal};
  Recorder *recorder = nullptr; // only if traced
  miniqu::Ref A, B, C, D, H, I, E, G, R, U1, U2, U3, U4, U5, Q;

  miniqu::Ref learn (miniqu::Kind kind, std::initializer_list<int> dimacs,
                     uint32_t glue) {
    return internal.new_constraint (internal.next_id++, kind, lits (dimacs),
                                    true, glue);
  }

  // Originals first (they take the first ids and some arena space), then
  // the learnt constraints in the order of the table.
  explicit Database (bool traced = false) {
    using miniqu::Kind;
    if (traced) {
      auto owned = std::make_unique<Recorder> ();
      recorder = owned.get ();
      proof.connect (std::move (owned));
      internal.proof = &proof;
    }
    declare (internal, "eeaaee");
    add (internal, Kind::Clause, {1, 2, 3, 4, 5, 6});
    A = learn (Kind::Clause, {1, 5}, 1);
    B = learn (Kind::Clause, {2, 5}, 2);
    C = learn (Kind::Clause, {1, 2, 5}, 3);
    D = learn (Kind::Clause, {1, 3, 6}, 3);
    H = learn (Kind::Clause, {-2, 4, 5}, 3);
    I = learn (Kind::Clause, {3, 6}, 4);
    E = learn (Kind::Clause, {1, 2, 3, 5}, 4);
    G = learn (Kind::Clause, {2, 3, 4, 6}, 5);
    R = learn (Kind::Clause, {-1, 5}, 6);
    U1 = learn (Kind::Cube, {-1, 3}, 1);
    U2 = learn (Kind::Cube, {-1, -3, 4}, 3);
    U3 = learn (Kind::Cube, {-1, 2, 4}, 3);
    U4 = learn (Kind::Cube, {-1, -2, 3, -4}, 4);
    U5 = learn (Kind::Cube, {-1, -2, -3, 4}, 4);
    Q = learn (Kind::Cube, {3, 4}, 6);
    internal.init_model_cube ();
  }

  // Assigns 5 with reason R and -4 with reason Q.
  void propagate_reasons () {
    decide (internal, 1);
    CHECK (internal.propagate () == miniqu::Ref::none);
    decide (internal, 3);
    CHECK (internal.propagate () == miniqu::Ref::none);
    CHECK (internal.reason (4) == R);
    CHECK (internal.reason (3) == Q);
    CHECK (internal.trail == lits ({1, 5, 3, -4}));
  }

  uint64_t id (miniqu::Ref ref) const {
    return deref (internal.arena, ref).id ();
  }
  bool garbage (miniqu::Ref ref) const {
    return deref (internal.arena, ref).garbage ();
  }
};

#endif
