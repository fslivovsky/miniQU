#ifndef MINIQU_PARSE_HPP_INCLUDED
#define MINIQU_PARSE_HPP_INCLUDED

#include "circuit.hpp"
#include "lit.hpp"

#include <string>
#include <vector>

namespace miniqu {

// Parsers.  A path may name a plain or gzip-compressed file, "-" is
// standard input.  Errors are reported through 'fatal' with file name and
// line number.

// QCIR (the prenex G14 format): the circuit with every identifier interned,
// helper gates of xor/ite expanded, gates outside the cone of the output
// removed and polarities computed.
Circuit parse_qcir (const std::string &path);

// QDIMACS: the prefix, outermost block first, and the clauses as one flat
// array in which every clause is followed by a 0.  Variables that occur in
// clauses without being quantified are free; they are put into an
// existential block in front of the prefix.
struct Qdimacs {
  struct Block {
    Quant quant;
    std::vector<int> variables;
  };
  std::vector<Block> blocks;
  std::vector<int> literals;
  size_t clauses = 0;
};

Qdimacs parse_qdimacs (const std::string &path);

} // namespace miniqu

#endif
