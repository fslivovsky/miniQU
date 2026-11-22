#ifndef MINIQU_TRACE_TRACER_HPP_INCLUDED
#define MINIQU_TRACE_TRACER_HPP_INCLUDED

#include "file.hpp"
#include "tracer.hpp"

#include <memory>

namespace miniqu {

// Writes the older '-trace' format (trace_tracer.cpp), for QDIMACS and QCIR
// input alike.
class TraceTracer : public Tracer {
  std::unique_ptr<OutputFile> file;

  void number (uint64_t);
  void step (uint64_t id, Kind, std::span<const int> lits);
  void premise_free (uint64_t id, Kind, std::span<const int> lits);

public:
  explicit TraceTracer (std::unique_ptr<OutputFile>);

  void add_original (uint64_t id, Kind, int gate,
                     std::span<const int> lits) override;
  void add_derived (uint64_t id, Kind, std::span<const int> lits,
                    std::span<const uint64_t> chain) override;
  void delete_constraint (uint64_t id, Kind,
                          std::span<const int> lits) override;
  void add_model_cube (uint64_t id, std::span<const int> lits) override;
  void flush () override;
};

} // namespace miniqu

#endif
