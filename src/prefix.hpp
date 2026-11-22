#ifndef MINIQU_PREFIX_HPP_INCLUDED
#define MINIQU_PREFIX_HPP_INCLUDED

#include "lit.hpp"

#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace miniqu {

// The quantifier prefix (ARCHITECTURE 4.2).  Internal variables are
// numbered in prefix order (INV-ORDER), so a block is a contiguous range of
// variables and "quantified further inside" is "greater index".

struct Block {
  Quant quant;
  Var begin, end;
  int unassigned; // unassigned decision variables of the block
};

// Static data of a variable, written once when it is created.
struct VarInfo {
  Quant quant;
  bool decision;  // an input variable; gate variables are never decided
  uint32_t depth; // index of its block
  int proof;      // number under which tracers see it (positive)
};

struct Prefix {
  std::vector<Block> blocks;
  std::vector<VarInfo> vars;

  Var size () const { return static_cast<Var> (vars.size ()); }

  // Appends a variable; consecutive variables of one quantifier form one
  // block.
  Var add_var (Quant, bool decision, int proof);

  Quant quant (Var v) const { return vars[v].quant; }
  uint32_t depth (Var v) const { return vars[v].depth; }
  Block &block (Var v) { return blocks[vars[v].depth]; }
  bool is_primary (Kind kind, Var v) const {
    return vars[v].quant == primary (kind);
  }

  // Sorts 'lits' and removes every secondary literal to the right of all
  // primary ones (ARCHITECTURE 4.6).
  void qreduce (std::vector<Lit> &lits, Kind) const;

  // The number of literals of sorted 'lits' that 'qreduce' keeps; for
  // callers that need to know which ones it removes.
  size_t reduced_size (std::span<const Lit> lits, Kind) const;
};

} // namespace miniqu

#endif
