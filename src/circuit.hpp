#ifndef MINIQU_CIRCUIT_HPP_INCLUDED
#define MINIQU_CIRCUIT_HPP_INCLUDED

#include "lit.hpp"

#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <unordered_map>
#include <vector>

namespace miniqu {

// A prenex circuit as read from a QCIR file (ARCHITECTURE 4.4).
//
// Everything is addressed by *proof number* (doc/proof-format.md): the
// quantified variables are 1..n in the order of the quantifier statements,
// the gates follow in the order of their definitions, so that gate k has
// number n+k.  Gate inputs are signed proof numbers.  xor and ite gates are
// expanded into three and/or gates when they are added, because the proof
// numbers of the expansion are part of the proof format.
//
// The circuit is built by a parser (see the construction functions), closed
// by 'resolve', and then analysed: 'remove_redundant', 'compute_polarities'
// and 'gate_depths' are the three questions the encoder asks.

enum class GateType : uint8_t { And, Or };

// The polarities in which the output depends on a gate; the encoding of
// the gate needs only the implications for those (Plaisted-Greenbaum).
enum class Polarity : uint8_t {
  None = 0,
  Positive = 1,
  Negative = 2,
  Both = 3
};

constexpr Polarity operator| (Polarity a, Polarity b) {
  return static_cast<Polarity> (static_cast<unsigned> (a) |
                                static_cast<unsigned> (b));
}
// The polarity of an input that occurs negated.
constexpr Polarity negate (Polarity p) {
  return static_cast<Polarity> (((static_cast<unsigned> (p) & 1) << 1) |
                                (static_cast<unsigned> (p) >> 1));
}

class Circuit {
public:
  // Variables first..last.  Adjacent quantifier statements of the same
  // quantifier are one block, as the old parser has it: the depth of a
  // gate (and with it the place of its variables in the prefix) is a
  // block index, and must not change with the way the file is cut up.
  // 'free' variables are existential, so they merge with a following
  // existential block.
  struct Block {
    Quant quant;
    int first, last;
  };

  // The inputs of the gate are 'size' entries of the flat input array,
  // from 'offset' on.
  struct Gate {
    uint32_t offset, size;
    GateType type;
  };

  // A problem found by 'resolve'.
  struct Defect {
    enum class Kind { Undefined, Cyclic };
    Kind kind;
    std::string name;
    uint64_t line; // of the first use, 0 if not known
  };

  // --- Construction (parsers) -------------------------------------------

  // Declares a quantified variable; false if the name is already defined.
  // Only before the first gate.
  bool add_variable (Quant, const std::string &name);

  // The literal number for an identifier: its proof number if it has
  // been defined, otherwise a provisional number that 'resolve' replaces
  // (gates may be used before they are defined, and the output statement
  // comes first in most files).  'line' is remembered for the error
  // message of an identifier that stays undefined.
  int reference (const std::string &name, uint64_t line);

  // Each returns the proof number of the new gate, or 0 if the name is
  // already defined.  xor and ite take three proof numbers; the new gate
  // has the number of the last one.
  int add_gate (GateType, const std::string &name,
                std::span<const int> inputs);
  int add_xor (const std::string &name, int a, int b);
  int add_ite (const std::string &name, int c, int a, int b);

  void set_output (int literal) { output_ = literal; }

  // Replaces all provisional numbers.  Returns the first identifier that
  // was used but never defined, or a gate that depends on itself.
  std::optional<Defect> resolve ();

  // --- Analysis (after 'resolve')
  // ------------------------------------------

  // Marks the gates outside the cone of influence of the output as removed
  // and returns their number.  Removed gates keep their number and their
  // inputs; they are not encoded, but still get variables (as in the old
  // solver, so that the prefix does not change).
  int remove_redundant ();

  // The polarity of every gate in the cone of the output (None otherwise).
  void compute_polarities ();

  // For every proof number, the index of the innermost block containing a
  // variable it depends on (-1 if none; variables have their own block).
  std::vector<int> gate_depths () const;

  // --- Access
  // ----------------------------------------------------------------

  int variables () const { return variables_; }
  int gates () const { return static_cast<int> (gate_table.size ()); }
  int output () const { return output_; }
  const std::vector<Block> &blocks () const { return blocks_; }

  bool is_gate (int number) const { return number > variables_; }
  const Gate &gate (int number) const;
  std::span<const int> inputs (int number) const;
  bool removed (int number) const;
  Polarity polarity (int number) const;

  // The identifier in the file; empty for the helper gates of an xor or
  // ite.
  const std::string &name (int number) const;

private:
  // Provisional numbers start here; real ones stay below.
  static constexpr int provisional = 1 << 30;

  struct Pending {
    const std::string *name;
    uint64_t line;
    int number; // 0 until defined
  };

  int next_number (int count) const;
  bool define (const std::string &name, int number);
  void append_gate (GateType, std::span<const int> inputs);
  int find_cycle () const;

  int variables_ = 0;
  int output_ = 0;
  std::vector<Block> blocks_;
  std::vector<Gate> gate_table;
  std::vector<int> input_table; // all gate inputs, one array
  std::vector<uint8_t> removed_;
  std::vector<Polarity> polarities;

  // One hash map for all identifiers; the keys are the names (node based,
  // so the pointers in 'names' stay valid).
  std::unordered_map<std::string, int> ids;
  std::vector<const std::string *>
      names; // by proof number - 1, may be short
  std::vector<Pending> pending;
};

} // namespace miniqu

#endif
