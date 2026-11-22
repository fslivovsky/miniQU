#ifndef MINIQU_TRACER_HPP_INCLUDED
#define MINIQU_TRACER_HPP_INCLUDED

#include "lit.hpp"

#include <cstdint>
#include <span>

namespace miniqu {

// Receiver of proof steps (ARCHITECTURE 8.1).  All literals are signed
// proof numbers, the numbers the frontend passed to 'Solver::add_var', so
// that a tracer needs to know nothing about internal variables.  Ids are
// allocated by the solver, starting at 1, whether or not a tracer is
// connected.
class Tracer {
public:
  virtual ~Tracer () = default;

  // An original constraint; 'gate' is the proof number of the gate whose
  // definition it belongs to, 0 for the output.
  virtual void add_original (uint64_t id, Kind, int gate,
                             std::span<const int> lits) = 0;

  // A constraint derived by resolution and reduction from 'chain'.
  virtual void add_derived (uint64_t id, Kind, std::span<const int> lits,
                            std::span<const uint64_t> chain) = 0;

  virtual void delete_constraint (uint64_t id, Kind,
                                  std::span<const int> lits) = 0;

  // An initial cube taken from a satisfying assignment (4.5); it has no
  // premises and cannot be expressed in QLRUP.
  virtual void add_model_cube (uint64_t id, std::span<const int> lits) = 0;

  // The empty constraint of the given kind has been derived under 'id'.
  virtual void conclude (Kind empty_kind, uint64_t id) {
    (void) empty_kind, (void) id;
  }

  virtual void flush () {}
};

} // namespace miniqu

#endif
