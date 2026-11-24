# Regression instances

Small instances that must stay correct, run by `tests/run_regressions.sh`.
Naming: `NAME.sat.qcir`, `NAME.unsat.qcir`, `NAME.sat.qdimacs`,
`NAME.unsat.qdimacs`; the verdict is part of the name. `.qcir` files are also
proof-checked with the Lean checker. Add an instance for every bug found (by
fuzzing or on a benchmark), shrunk with `qbfdd.py` where possible, and say
below why it exists.

| file | why |
|---|---|
| `true-xor-ite.sat.qcir` | `xor` and `ite` gates; the witness for `c` depends on the universal `u` |
| `false-xor-parity.unsat.qcir` | a gate and its negation in one `and`: constant false after encoding |
| `free-block.sat.qcir` | a `free` block; free variables are outermost existential |
| `output-negated-input.unsat.qcir` | the output is the negation of a universal input, so no gate exists |
| `rightmost-dependency.sat.qcir` | alternating blocks where each existential must follow its universal; the right-to-left order matters for elimination |
| `prenex-pair.sat.qdimacs`, `prenex-pair.sat.qcir` | the same formula in both input formats; verdicts must agree |
| `mode1-minimize-asserting.sat.qcir` | run with `-mode=1 -ccminmode=2` (or 3): minimisation removed every primary literal right of a secondary asserting literal, which the reduction then dropped (failed assertion in `learn`, hang in the M1 binary); tiny corpus seed 16 (M2-T5) |
