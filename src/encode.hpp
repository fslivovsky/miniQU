#ifndef MINIQU_ENCODE_HPP_INCLUDED
#define MINIQU_ENCODE_HPP_INCLUDED

#include "circuit.hpp"
#include "miniqu.hpp"
#include "parse.hpp"

namespace miniqu {

// Hand a formula to the solver through the public interface only: first all
// variables in prefix order, then all constraints.

// The dual Plaisted-Greenbaum encoding of a circuit (ARCHITECTURE 4.4). The
// circuit must have been through 'parse_qcir', that is, be resolved with
// redundant gates removed and polarities computed.  With 'early_tseitin'
// the variables of a gate are placed right after the innermost block of the
// variables it depends on, otherwise innermost.
void encode (const Circuit &, Solver &, bool early_tseitin);

// Quantifier prefix and clauses of a QDIMACS file.
void encode_qdimacs (const Qdimacs &, Solver &);

} // namespace miniqu

#endif
