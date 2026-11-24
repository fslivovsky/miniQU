#ifndef MINIQU_TIER_HPP_INCLUDED
#define MINIQU_TIER_HPP_INCLUDED

#include <array>
#include <cstdint>

namespace miniqu {

// State of tier.cpp: the current glue limits and the usage histogram, both
// per kind (index with 'index (kind)').
struct Tiers {
  // Buckets 0..buckets-2 are one glue each, the last is "that glue or
  // more".
  static constexpr int buckets = 64;

  std::array<int, 2> tier1{}; // glue <= tier1: never reduced
  std::array<int, 2> tier2{}; // glue <= tier2: used for two reductions
  // Analysis uses of redundant constraints by glue, only counted with
  // '--recomputetier'.
  std::array<std::array<int64_t, buckets>, 2> usage{};
};

} // namespace miniqu

#endif
