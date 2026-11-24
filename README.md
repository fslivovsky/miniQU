# miniQU

miniQU is a QCDCL solver for quantified Boolean formulas (QBF), written in C++20 in the style of
[CaDiCaL](https://github.com/arminbiere/cadical) and descended from the MiniSat-based solver it
started as. It reads prenex formulas in QDIMACS (CNF matrix) or QCIR (circuit matrix) format,
learns clauses and terms (cubes), and supports dependency learning as well as propagation and
learning with QU-resolution and long-distance Q-resolution. Constraints live in an arena and
watch lists are kept in memory in the order of their accesses, as in MiniSat. The structure of
the sources is described in `doc/rewrite/ARCHITECTURE.md`; where the previous implementation lives
is said at the end of "Building".

## Building

A C++20 compiler (GCC 11 or clang), CMake 3.22 and zlib are required. The presets of
`CMakePresets.json` put the build trees next to the repository, in `../miniqu-work/build/<preset>`:

| preset | use |
|---|---|
| `release` | benchmarks: `-O3`, no assertions, no logging code, LTO |
| `release-clang` | the same with clang++ |
| `debug` | development: `-O0`, assertions, logging code (`--log=1`) |
| `asan` | fuzzing: address and undefined behaviour sanitizers, assertions |
| `log` | tracing a long run: optimised, logging code, no assertions |

```bash
cmake --preset release
cmake --build --preset release -j8     # ../miniqu-work/build/release/miniQU
ctest --preset release                 # unit tests, formatting, encoding, tooling, regressions, fuzzing
```

`ctest` needs the Lean proof checker (`qlrup-check`, see `bench/README.md`) and the frozen
baseline binary for the end-to-end tests. Without CMake presets, `cmake -S . -B build` builds the
same targets: `miniQU`, `qlrup-trim` (proof trimmer) and the unit tests.

The previous implementation (commit c39005a, MiniSat layout) is no longer in the tree: its sources are
`git show c39005a:minisat/core/Solver.cc` and the worktree `/home/ec2-user/miniqu-work/baseline-src`, and
its frozen binary, the reference of the benchmarks, is `/home/ec2-user/miniqu-work/baseline/miniQU`.

## Usage

```bash
miniQU [options] <input-file> [result-file]
```

The input is parsed as QCIR if the file name ends in `qcir` (or if `--qcir` is given), and as
(optionally gzipped) QDIMACS otherwise; without a file QDIMACS is read from standard input. The
result is printed as `SATISFIABLE` or `UNSATISFIABLE`, and the exit code is 10 for true and 20 for
false formulas.

Options are written `--name=value`, `--name` (value 1) and `--no-name` (value 0). A single dash and
hyphens inside names are accepted as well, so the spellings of the previous solver keep working
(`-ccmin-mode=3`, `-early-tseitin`, `-no-dl`, `-cpu-lim=60`, `-proof-binary`). `--help` lists every
option with its default and range. The most important ones:

| Option | Default | Description |
|---|---|---|
| `--dl` | off | Dependency learning: decisions may be made in any order, and dependencies between variables are learnt from conflicts. |
| `--mode=<0,1,2>` | 0 | Propagation and learning with Q-resolution (0), QU-resolution (1), or long-distance Q-resolution (2). |
| `--ccminmode=<0..3>` | 0 | Minimization of learnt clauses and terms: none (0), local (1) and recursive (2) minimization, or recursive minimization that takes reduction into account (3). Proofs and traces cover minimization (chain extension, `doc/proof-format.md`). |
| `--earlytseitin` / `--no-earlytseitin` | on | QCIR only: quantify the variables that represent gates right after the innermost variable the gate depends on (see below). |
| `--legacyanalyze` | off | Use the analysis of the previous solver (`analyze_qu`) in mode 0. |
| `--cert` | off | Print the assignment of the decision variables of the outermost block (`V` line). |
| `--proof=<file>` | | Write a proof in the QLRUP format (QCIR input, modes 0 and 1); see `doc/proof-format.md`. |
| `--proofbinary` | off | Write the proof in the binary format. |
| `--trace=<file>` | | Write a trace in the older format (modes 0 and 1). |
| `--cpulim=<s>`, `--memlim=<MB>` | none | Resource limits. |
| `--seed=<n>` | 0 | Randomise the initial variable scores (0 = deterministic). |
| `--verb=<0..3>` | 1 | Verbosity; `--verb=1` also prints the `c stat` counters. |

The remaining options (restart, reduction, tier and stress parameters, `--check`, `--log`,
`--profile`) are described by `--help` and in `doc/rewrite/ARCHITECTURE.md`.

Whether dependency learning pays off depends on the instance: it can be
essential when following the quantifier prefix forces bad decisions, and it
can be slower on formulas with many alternations where the prefix order is a
good guide. Neither setting is recommended here; the benchmark results in
`bench/results/` compare both.

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

In mode 0, clauses and terms are learnt by `analyze_q` (`src/analyze.cpp`). Since
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

Mode 1 still uses the older analysis (`analyze_qu`, `src/analyze_qu.cpp`), which can also be
selected in mode 0 with `--legacyanalyze` for comparison. Mode 2 uses
`analyze_ldq`.

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

## Cores

Benchmark runs (`bench/run.py`) use the upper half of the machine's cores, one job per core
(on 96 cores: `--cores 48-95 --jobs 48`); builds, fuzzing, proof checking and `tests/regress.sh` use
the lower half (`taskset -c 0-47`). Both are computed from the number of cores; see
`bench/README.md`.

## Testing

`ctest --preset release` (or `asan`, `debug`) runs the unit tests of `test/unit`, the format check
(`clang-format`), the comparison of the encoder with the original constraints of the baseline's
proofs, the tests of the benchmark statistics (`bench/test_compare.py`), the regression instances of
`tests/regressions/` and a 20-seed run of `tests/regress.sh` over the default and the `--dl`
configurations. `tests/regress.sh` is the end-to-end driver: it compares verdicts with the
brute-force evaluator and the baseline, checks every proof with the Lean checker and asserts that the
fuzz instances reach restarts, reductions and garbage collection (`tests/matrix.txt` lists the
configurations). Examples:

```bash
tests/regress.sh -s 1:300 -M all ../miniqu-work/build/release/miniQU   # whole configuration matrix
tests/fuzz.sh ../miniqu-work/build/release/miniQU 1 100 -dl            # QCIR fuzzing
tests/fuzz_qdimacs.sh ../miniqu-work/build/release/miniQU 1 200 -dl    # QDIMACS fuzzing
tests/fuzz_cert.sh ../miniqu-work/build/release/miniQU 1 500           # -cert certificates
```

- `tests/qcir_fuzz.py` generates small random circuits (and CNFs) with a
  random prefix; the expected result is included as a comment.
- `tests/qcir_gen.py` generates instances from several scalable families.
- `tests/qcir_eval.py` evaluates a small QCIR instance by brute force.
- `tests/qdimacs2qcir.py` converts QDIMACS to QCIR.
- `tests/check_cert.py` validates the certificate printed by `--cert`.
- `bench/` holds the benchmark harness; see `bench/README.md`.

## License

miniQU is distributed under the MIT license, like MiniSat (see `LICENSE`).
`qbfuzz.py` and `qbfdd.py` are third-party tools with their own licenses.
