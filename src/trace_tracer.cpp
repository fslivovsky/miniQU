// The older '-trace' format (the old 'traceConstraint', 'traceVector' and
// 'traceInitialTerm').  One line per constraint:
//
//   <id> <type> <lit> ... <lit> 0 <premise> ... <premise> 0 \n
//   <id> <type> <lit> ... <lit> 0 0\n                     (no premises)
//
// with type 0 for a clause and 1 for a cube, literals as signed proof
// numbers (for QDIMACS the variable numbers of the file), and the premises
// in the order of the QLRUP chain.  A derived line ends with a blank before
// the newline, a premise-free one does not, exactly as the old solver
// wrote them.
//
// Differences from the old trace, all deliberate:
//
// - Original constraints are written, as premise-free lines.  The old
//   trace wrote none and its premises referred to clauses by position in
//   the QDIMACS file; the ids of the new solver are those of the proof
//   (an original that reduction shortens takes two ids, a tautology none),
//   so a trace without them could not be read.  Reductions of originals
//   appear as derived lines.  With neither tautologies nor reductions the
//   ids of the original clauses are still their file positions.
// - Deletions are not written (the old trace had none either).
// - Variables of QCIR input are written as proof numbers; the old trace
//   used internal aliases (2g and 2g+1 for gate g) and gave every original
//   QCIR clause the same id, so it was unusable there.
// - The old debug builds also wrote reduction detail ('u' lines from
//   'traceReduction'); release builds never did, and neither does this.

#include "trace_tracer.hpp"

namespace miniqu {

TraceTracer::TraceTracer (std::unique_ptr<OutputFile> f)
    : file (std::move (f)) {}

void TraceTracer::number (uint64_t n) {
  file->put_decimal (n);
  file->put_byte (' ');
}

void TraceTracer::step (uint64_t id, Kind kind, std::span<const int> lits) {
  number (id);
  number (index (kind));
  for (int lit : lits) {
    file->put_decimal (int64_t{lit});
    file->put_byte (' ');
  }
  file->put ("0 ");
}

void TraceTracer::premise_free (uint64_t id, Kind kind,
                                std::span<const int> lits) {
  step (id, kind, lits);
  file->put ("0\n");
}

void TraceTracer::add_original (uint64_t id, Kind kind, int,
                                std::span<const int> lits) {
  premise_free (id, kind, lits);
}

void TraceTracer::add_derived (uint64_t id, Kind kind,
                               std::span<const int> lits,
                               std::span<const uint64_t> chain) {
  step (id, kind, lits);
  for (uint64_t premise : chain)
    number (premise);
  file->put ("0 \n");
}

void TraceTracer::delete_constraint (uint64_t, Kind, std::span<const int>) {
}

void TraceTracer::add_model_cube (uint64_t id, std::span<const int> lits) {
  premise_free (id, Kind::Cube, lits);
}

void TraceTracer::flush () { file->flush (); }

} // namespace miniqu
