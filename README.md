# miniQU

miniQU is a QCDCL solver for quantified Boolean formulas (QBF), built on top of
[MiniSat](http://minisat.se) 2.2. It reads prenex formulas in QDIMACS (CNF
matrix) or QCIR (circuit matrix) format, learns clauses and terms (cubes), and
supports dependency learning as well as propagation and learning with
QU-resolution and long-distance Q-resolution.

## Building

A C++17 compiler and zlib are required.

```bash
make r
```

builds `build/release/bin/miniQU` (use `make d` for a debug build with
assertions and very verbose logging). Alternatively, with CMake:

```bash
cmake -S . -B build-cmake
cmake --build build-cmake
```

## Usage

```bash
miniQU [options] <input-file>
```

The input is parsed as QCIR if the file name ends in `qcir` (or if `-qcir` is
given), and as (optionally gzipped) QDIMACS otherwise. The result is printed as
`SATISFIABLE` or `UNSATISFIABLE`, and the exit code is 10 for true and 20 for
false formulas.

The most important options (see `--help` for all of them):

| Option | Default | Description |
|---|---|---|
| `-dl`, `-no-dl` | off | Dependency learning: decisions may be made in any order, and dependencies between variables are learnt from conflicts. |
| `-mode=<0,1,2>` | 0 | Propagation and learning with Q-resolution (0), QU-resolution (1), or long-distance Q-resolution (2). |
| `-ccmin-mode=<0..3>` | 0 | Minimization of learnt clauses and terms: none (0), MiniSat's local (1) and recursive (2) minimization, or recursive minimization that takes reduction into account (3). |
| `-early-tseitin`, `-no-early-tseitin` | on | QCIR only: quantify the variables that represent gates right after the innermost variable the gate depends on (see below). |
| `-cert` | off | Print the assignment of the outermost quantifier block. |
| `-proof=<file>` | | Write a proof in the QLRUP format (QCIR input, modes 0 and 1); see `doc/proof-format.md`. Disables minimization. |
| `-proof-binary` | off | Write the proof in the binary format. |
| `-trace=<file>` | | Write a trace in the older format. Disables minimization. |
| `-verb=<0,1,2>` | 1 | Verbosity. |

Whether dependency learning pays off depends on the instance: it can be
essential when following the quantifier prefix forces bad decisions, and it
can be slower on formulas with many alternations where the prefix order is a
good guide.

### QCIR support

Prenex QCIR-G14 with `and`, `or`, `xor`, and `ite` gates is supported. Free
variables are treated as outermost existential variables. Malformed or
unsupported input (such as quantifiers inside the matrix) is reported as an
error.

A circuit is encoded twice, with separate variables for the gates: once as
clauses (with existential gate variables) and once as terms (with universal
gate variables), both using the Plaisted-Greenbaum encoding. Gate variables
are never used as decision variables.

## Implementation notes

### Conflict analysis

In mode 0, clauses and terms are learnt by `Solver::analyzeQ()`. Since
propagation ignores the quantifier prefix, every literal of a conflicting
constraint and of the reasons on the trail is assigned, and conflict analysis
is essentially first-UIP learning with one extra condition. Call the
variables that can be resolved on *primary* (existential variables for
clauses, universal variables for terms) and the others *secondary*. A
secondary literal that would be unassigned after backtracking cannot stay in
the learnt constraint, so it must be removed by universal/existential
reduction, which in turn requires that all primary literals to its right are
resolved away first. The analysis is a single pass over the trail:

1. Resolve away primary literals in reverse assignment order until reaching
   one that is the only primary literal on its decision level, and that is to
   the left of all secondary literals assigned on that level or later (the
   *blocked* literals).
2. Keep resolving away the primary literals to the right of the leftmost
   blocked literal.

If a literal that has to be resolved away is a decision, the decision was made
out of order: instead of a constraint, the solver learns that the variable
depends on the leftmost blocked variable. Without dependency learning,
decisions follow the quantifier prefix, and this case does not arise.

With `-ccmin-mode=3`, learnt constraints are then minimized: a literal is
redundant if it can be resolved away, recursively, without introducing new
literals other than secondary literals that disappear by reduction.

Mode 1 still uses the older analysis (`Solver::analyze()`), which can also be
selected in mode 0 with `-legacy-analyze` for comparison. Mode 2 uses
`Solver::analyzeLDQ()`.

### Prefix position of gate variables

The cost of step 2 above depends on how many primary literals are to the right
of a blocked literal. If the variables representing gates were quantified
innermost, this would be every gate literal in the constraint, and analysing a
conflict would amount to expanding gate definitions until only input
variables remain.

However, the value of a gate is a function of the variables it depends on, so
its variables can be quantified right after the innermost such variable
without changing the truth value of the formula. With `-early-tseitin` (the
default), the QCIR front end adds the variables of a gate to the quantifier
block that follows the innermost variable the gate depends on. Since gate
variables are not decision variables, this does not restrict the order of
decisions; quantifier blocks only have to be complete with respect to their
decision variables before the solver moves on to the next block (without
dependency learning).

## Testing

The scripts in `tests/` generate random QCIR instances and compare the result
of the solver with a brute-force evaluator:

```bash
tests/fuzz.sh build/release/bin/miniQU 1 100 -dl
```

runs the solver with option `-dl` on the instances for seeds 1 to 100. If the
environment variable `REFERENCE` is set to another solver binary, larger
instances are additionally checked against the result of that solver.

- `tests/qcir_fuzz.py` generates small random circuits (and CNFs) with a
  random prefix; the expected result is included as a comment.
- `tests/qcir_gen.py` generates instances from several scalable families.
- `tests/qcir_eval.py` evaluates a small QCIR instance by brute force.
- `tests/qdimacs2qcir.py` converts QDIMACS to QCIR.

## License

miniQU is distributed under the MIT license, like MiniSat (see `LICENSE`).
`qbfuzz.py` and `qbfdd.py` are third-party tools with their own licenses.
