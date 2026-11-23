#ifndef MINIQU_PROOF_HPP_INCLUDED
#define MINIQU_PROOF_HPP_INCLUDED

#include "lit.hpp"
#include "tracer.hpp"

#include <cstdint>
#include <memory>
#include <span>
#include <vector>

namespace miniqu {

struct Internal;
class Constraint;

// The one object the solver reports proof steps to (ARCHITECTURE 8.1):
// 'Internal::proof' is null when nothing is connected, so that every call
// site is a single 'if (proof) proof->...'.  It translates internal
// literals to signed proof numbers and hands every step to each connected
// tracer in the order they were connected.
//
// Ids are allocated by 'Internal' ('next_id') whether or not a proof is
// written (constraints store them only while one is); the functions that
// take an explicit id are for steps whose constraint is not (or not yet)
// stored: originals before reduction, their reductions, and empty
// constraints.
class Proof {
  Internal *internal;
  std::vector<std::unique_ptr<Tracer>> tracers;
  std::vector<int> lits; // the translated literals of the current step
  uint64_t empty_id = 0; // the last empty constraint logged

  void translate (std::span<const Lit>);

public:
  explicit Proof (Internal *);
  ~Proof ();
  Proof (const Proof &) = delete;
  Proof &operator= (const Proof &) = delete;

  void connect (std::unique_ptr<Tracer>);

  // An original constraint as given (sorted, duplicates removed), before
  // reduction.
  void add_original (uint64_t id, Kind, int gate, std::span<const Lit>);

  // A constraint derived from 'chain'; an empty 'lits' is the empty
  // constraint of that kind.
  void add_derived (uint64_t id, Kind, std::span<const Lit>,
                    std::span<const uint64_t> chain);
  void add_derived (const Constraint &, std::span<const uint64_t> chain);

  void delete_constraint (uint64_t id, Kind, std::span<const Lit>);
  void delete_constraint (const Constraint &);

  // Replaces 'c' by the shorter constraint 'new_lits' derived from
  // 'chain': derived under the fresh id 'internal->next_id++', the old id
  // deleted, the new id stored in 'c'.  The caller rewrites the literals.
  void strengthen (Constraint &c, std::span<const Lit> new_lits,
                   std::span<const uint64_t> chain);

  // An initial cube taken from a satisfying assignment (ARCHITECTURE 4.5).
  void add_model_cube (const Constraint &);

  // The empty constraint of that kind, the last one logged, ends the
  // proof; tracers flush.
  void conclude (Kind);
  void flush ();
};

} // namespace miniqu

#endif
