// Translation of proof steps from internal literals to proof numbers, and
// fan-out to the connected tracers (ARCHITECTURE 8).
//
// A literal of internal variable v is written as the proof number of v
// (static data of the prefix, 4.4), negated for a negative literal.  For
// QCIR input both variables of a gate share the gate's number; the kind of
// the step says which of the two is meant.  For QDIMACS input the number is
// the variable's number in the file.
//
// Where the steps come from is listed in ARCHITECTURE 8.2; deletions come
// only from 'mark_garbage' (and from the reduction of an original, which
// is never stored under the original's id).

#include "proof.hpp"
#include "constraint.hpp"
#include "internal.hpp"

#include <cassert>

namespace miniqu {

Proof::Proof (Internal *i) : internal (i) {}
Proof::~Proof () = default;

void Proof::connect (std::unique_ptr<Tracer> tracer) {
  tracers.push_back (std::move (tracer));
}

void Proof::translate (std::span<const Lit> ls) {
  lits.clear ();
  for (Lit l : ls) {
    const int number = internal->prefix.vars[var (l)].proof;
    assert (number > 0);
    lits.push_back (sign (l) ? -number : number);
  }
}

void Proof::add_original (uint64_t id, Kind kind, int gate,
                          std::span<const Lit> ls) {
  translate (ls);
  if (lits.empty ())
    empty_id = id;
  for (const auto &tracer : tracers)
    tracer->add_original (id, kind, gate, lits);
}

void Proof::add_derived (uint64_t id, Kind kind, std::span<const Lit> ls,
                         std::span<const uint64_t> chain) {
  assert (!chain.empty ());
  translate (ls);
  if (lits.empty ())
    empty_id = id;
  for (const auto &tracer : tracers)
    tracer->add_derived (id, kind, lits, chain);
}

void Proof::add_derived (const Constraint &c,
                         std::span<const uint64_t> chain) {
  add_derived (c.id (), c.kind (), c.lits (), chain);
}

void Proof::delete_constraint (uint64_t id, Kind kind,
                               std::span<const Lit> ls) {
  translate (ls);
  for (const auto &tracer : tracers)
    tracer->delete_constraint (id, kind, lits);
}

void Proof::delete_constraint (const Constraint &c) {
  delete_constraint (c.id (), c.kind (), c.lits ());
}

void Proof::strengthen (Constraint &c, std::span<const Lit> new_lits,
                        std::span<const uint64_t> chain) {
  const uint64_t id = internal->next_id++;
  add_derived (id, c.kind (), new_lits, chain);
  delete_constraint (c);
  c.set_id (id);
}

void Proof::add_model_cube (const Constraint &c) {
  assert (c.kind () == Kind::Cube);
  translate (c.lits ());
  for (const auto &tracer : tracers)
    tracer->add_model_cube (c.id (), lits);
}

void Proof::conclude (Kind kind) {
  assert (empty_id);
  for (const auto &tracer : tracers) {
    tracer->conclude (kind, empty_id);
    tracer->flush ();
  }
}

void Proof::flush () {
  for (const auto &tracer : tracers)
    tracer->flush ();
}

} // namespace miniqu
