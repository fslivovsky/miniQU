#ifndef MINIQU_LIT_HPP_INCLUDED
#define MINIQU_LIT_HPP_INCLUDED

#include <compare>
#include <cstddef>
#include <cstdint>

namespace miniqu {

// Literals, kinds and quantifiers (ARCHITECTURE 4.1).  Nothing in this file
// depends on solver state.

using Var = uint32_t; // 0 .. vars-1, in prefix order

// MiniSat encoding, 2*var + sign with sign 1 = negated, because literals
// index the watch lists directly and are stored in arena words.
struct Lit {
  uint32_t x;
  friend constexpr auto operator<=> (Lit, Lit) = default;
};

constexpr Lit mk_lit (Var v, bool negated = false) {
  return Lit{2 * v + (negated ? 1u : 0u)};
}
constexpr Var var (Lit l) { return l.x >> 1; }
constexpr bool sign (Lit l) { return l.x & 1; }
constexpr Lit operator~(Lit l) { return Lit{l.x ^ 1u}; }
constexpr uint32_t index (Lit l) { return l.x; }

inline constexpr Lit lit_undef{UINT32_MAX};

// A clause is falsified when all its literals are false, a cube when all
// its literals are true; both are handled by the same code through the
// "kind value" of a literal (ARCHITECTURE 4.1).
enum class Kind : uint8_t { Clause = 0, Cube = 1 };
enum class Quant : uint8_t { Exists = 0, Forall = 1 };

constexpr size_t index (Kind k) { return static_cast<size_t> (k); }

// The quantifier whose literals a constraint of that kind is resolved on.
constexpr Quant primary (Kind k) {
  return k == Kind::Clause ? Quant::Exists : Quant::Forall;
}
constexpr Kind other (Kind k) {
  return k == Kind::Clause ? Kind::Cube : Kind::Clause;
}

// Word offset into the arena.  A distinct type, so that references cannot
// be confused with literals, ids or counts.
enum class Ref : uint32_t { none = UINT32_MAX };

} // namespace miniqu

#endif
