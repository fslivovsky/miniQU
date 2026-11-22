#ifndef MINIQU_QLRUP_TRACER_HPP_INCLUDED
#define MINIQU_QLRUP_TRACER_HPP_INCLUDED

#include "file.hpp"
#include "tracer.hpp"

#include <memory>

namespace miniqu {

// Writes QLRUP proofs (doc/proof-format.md), as text or in the binary
// encoding, byte for byte as the old solver wrote the same steps.
class QlrupTracer : public Tracer {
  std::unique_ptr<OutputFile> file;
  bool binary;

  void number (uint64_t);
  void literals (std::span<const int>);
  void kind (Kind);
  void end_of_step ();

public:
  // Writes the magic line of the binary format at once.
  QlrupTracer (std::unique_ptr<OutputFile>, bool binary);

  void add_original (uint64_t id, Kind, int gate,
                     std::span<const int> lits) override;
  void add_derived (uint64_t id, Kind, std::span<const int> lits,
                    std::span<const uint64_t> chain) override;
  void delete_constraint (uint64_t id, Kind,
                          std::span<const int> lits) override;
  // Not expressible in QLRUP: a fatal error.
  void add_model_cube (uint64_t id, std::span<const int> lits) override;
  void flush () override;
};

} // namespace miniqu

#endif
