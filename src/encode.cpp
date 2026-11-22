#include "encode.hpp"

#include <cstdlib>

namespace miniqu {

// Dual encoding of a circuit (ARCHITECTURE 4.4), and the much simpler
// transfer of a QDIMACS formula.  Only the public interface of 'Solver' is
// used.
//
// Every gate has two variables: an existential one for the clauses and a
// universal one for the cubes.  Their user variable numbers are fixed by
// the proof number p of the gate and the number n of quantified variables:
//
//     existential variable  n + 2 (p - n) - 1
//     universal variable    n + 2 (p - n)
//
// so input variables keep their number, and the variables of a gate can be
// found without a table.  Both carry p as their proof number, so that
// proof steps are expressed in the numbers of doc/proof-format.md.
//
// The clauses are the Plaisted-Greenbaum encoding of the circuit for the
// polarity of each gate.  The cubes are the clauses of the negated circuit,
// each negated: 'and' gates give the cubes that the clauses of an 'or' gate
// would, and vice versa.  The old solver generated both from one function
// with a flag, and so does 'gate_constraints'.

namespace {

class Encoder {
  const Circuit &circuit;
  Solver &solver;
  const int n; // number of quantified variables
  std::vector<int> scratch;

  static Quant other_quant (Quant q) {
    return q == Quant::Exists ? Quant::Forall : Quant::Exists;
  }

  int gate_var (int p, Quant quant) const {
    return n + 2 * (p - n) - (quant == Quant::Exists ? 1 : 0);
  }

  // The variable of 'number' that occurs in constraints of this kind.
  int var_for (int number, Kind kind) const {
    return number <= n ? number : gate_var (number, primary (kind));
  }
  int lit_for (int literal, Kind kind) const {
    const int v = var_for (std::abs (literal), kind);
    return literal < 0 ? -v : v;
  }

  void add_inputs (const Circuit::Block &block) {
    for (int v = block.first; v <= block.last; v++)
      solver.add_var (v, block.quant, true, v);
  }

  // One group of variables: the 'quant' variables of the given gates.
  void add_gate_vars (Quant quant, const std::vector<int> &gates) {
    for (int p : gates)
      solver.add_var (gate_var (p, quant), quant, false, p);
  }

  void add_tseitin_groups (const std::vector<int> &gates, Quant first) {
    add_gate_vars (first, gates);
    add_gate_vars (other_quant (first), gates);
  }

  // The prefix.  The variables of a gate go right after the innermost block
  // of variables it depends on ('early_tseitin'), the one with the
  // quantifier of that block first so that it extends the block.  Gates
  // without dependencies come before the first block, the existential
  // variables of a gate first only if that block is universal.
  void add_prefix (bool early_tseitin) {
    const auto &blocks = circuit.blocks ();
    std::vector<std::vector<int>> gates_at_depth (blocks.size () + 1);
    if (early_tseitin) {
      const std::vector<int> depth = circuit.gate_depths ();
      for (int p = n + 1; p <= n + circuit.gates (); p++)
        gates_at_depth[static_cast<size_t> (depth[static_cast<size_t> (p)] +
                                            1)]
            .push_back (p);
    } else {
      for (int p = n + 1; p <= n + circuit.gates (); p++)
        gates_at_depth.back ().push_back (p);
    }
    const bool universal_first =
        !blocks.empty () && blocks[0].quant == Quant::Forall;
    add_tseitin_groups (gates_at_depth[0],
                        universal_first ? Quant::Exists : Quant::Forall);
    for (size_t d = 0; d < blocks.size (); d++) {
      add_inputs (blocks[d]);
      add_tseitin_groups (gates_at_depth[d + 1], blocks[d].quant);
    }
  }

  void add_constraint (Kind kind, int proof_gate) {
    solver.add_original (kind, scratch, proof_gate);
    scratch.clear ();
  }

  // The constraints of gate 'p' needed for its polarity.  For an and gate
  // g = and (l_1, ..., l_k) the clauses are (-g, l_i) for every i, needed
  // unless g occurs only negatively, and (g, -l_1, ..., -l_k), needed
  // unless g occurs only positively; or gates are the same with all
  // literals negated, and so is the cube side (flip).
  void add_gate_constraints (int p, Kind kind) {
    const bool flip =
        (kind == Kind::Cube) != (circuit.gate (p).type == GateType::Or);
    const int sign = flip ? -1 : 1;
    const Polarity polarity = circuit.polarity (p);
    const int g = lit_for (p, kind) * sign;
    const auto inputs = circuit.inputs (p);
    if (polarity != (flip ? Polarity::Positive : Polarity::Negative))
      for (int l : inputs) {
        scratch = {-g, lit_for (l, kind) * sign};
        add_constraint (kind, p);
      }
    if (polarity != (flip ? Polarity::Negative : Polarity::Positive)) {
      scratch = {g};
      for (int l : inputs)
        scratch.push_back (-lit_for (l, kind) * sign);
      add_constraint (kind, p);
    }
  }

  void add_constraints (Kind kind) {
    for (int p = n + 1; p <= n + circuit.gates (); p++)
      if (!circuit.removed (p))
        add_gate_constraints (p, kind);
    scratch = {lit_for (circuit.output (), kind)};
    add_constraint (kind, 0);
  }

public:
  Encoder (const Circuit &c, Solver &s)
      : circuit (c), solver (s), n (c.variables ()) {}

  void encode (bool early_tseitin) {
    add_prefix (early_tseitin);
    add_constraints (Kind::Clause);
    add_constraints (Kind::Cube);
  }
};

} // namespace

void encode (const Circuit &circuit, Solver &solver, bool early_tseitin) {
  Encoder (circuit, solver).encode (early_tseitin);
}

void encode_qdimacs (const Qdimacs &formula, Solver &solver) {
  for (const auto &block : formula.blocks)
    for (int v : block.variables)
      solver.add_var (v, block.quant);
  const int *start = formula.literals.data ();
  for (size_t i = 0; i < formula.literals.size (); i++)
    if (formula.literals[i] == 0) {
      const int *end = formula.literals.data () + i;
      solver.add_original (Kind::Clause, {start, end});
      start = end + 1;
    }
}

} // namespace miniqu
