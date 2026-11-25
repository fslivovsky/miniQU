# miniQU rewrite: report at hand-over (2026-11-25)

Branch `rewrite/cadical-style`, created from `c39005a` (the previous, MiniSat-derived solver, called
"the baseline" below). This report states what exists and what was checked. Every claim names the
file it rests on; `STATUS.md` is the append-only log of all tasks, with the commands and log
locations of every run. What is still to do is in `HANDOFF.md`.

Reading order for someone new: this file, `HANDOFF.md`, `ARCHITECTURE.md` (design; section 10.0 for
elimination and vivification as built), `reviews/handover.md`.

## 1. Summary

| milestone | content | state | evidence |
|---|---|---|---|
| M1 | port of the baseline to the new structure, same search | done, reviewed, approved in round 3 | `reviews/M1-r3.md`, `bench/results/M1-r3-report.md` |
| M2 | tiers, glue update, conflict schedule of reductions, root simplification, minimisation with proofs, glue-EMA restarts, trail reuse | built and tested up to its gates; **no independent verification, no benchmark stage, no review** (owner decision, STATUS "wrap up in 24 hours") | STATUS M2-T1 ... M2-T11, `bench/results/M2-T7-gate/`, `M2-T8-gate/`, `M2-screen-reports/`, `M2-T11-jctc/` |
| M3 | bounded variable elimination, before the search and as inprocessing, off by default | initial version; short runs only | STATUS M3-T1 ... M3-T4, `reviews/handover.md` |
| M4 | vivification of learnt clauses and cubes, off by default | initial version; short runs only | STATUS M4-T1 ... M4-T3, `reviews/handover.md` |
| hand-over | test run, review, one blocking defect fixed afterwards | fix not reviewed, full matrix not repeated after it | `bench/results/handover-report.md`, `reviews/handover.md`, STATUS "Hand-over defects" |

Not started: everything in ROADMAP "M5+", the optimisation milestone (profiling, parameter tuning),
900 s runs with ablations, the relaxation of the rightmost condition.

No checker or proof-format extension was needed: all techniques of M1 to M4 are logged in the
existing QLRUP format (`ROADMAP.md`, "Summary: what QLRUP can express today"). `~/qu-check` is
unchanged (branch `main`).

## 2. What was built

### 2.1 Structure (`ARCHITECTURE.md` sections 2 and 3)

C++20, CMake with presets, one namespace `miniqu`. Layers: app (`app.cpp`), frontend
(`parse_qcir.cpp`, `parse_qdimacs.cpp`, `circuit.cpp`, `encode.cpp`), API (`miniqu.hpp`,
`solver.cpp`, class `Solver`), `struct Internal` (`internal.hpp`) with one `.cpp` per technique, and
a base layer (`arena`, `constraint`, `watch`, `heap`, `ema`, `options`, `stats`, `profile`, `limit`,
...). There is no `External` class. 79 files in `src/`, 43 in `test/unit/`.

Owner constraints, as reviewed in `reviews/M1-r3.md` section 1:

- **Arena**: constraints live in a region allocator with the MiniSat layout; garbage collection
  copies them in the order of watch accesses (`arena.{hpp,cpp}`, `collect.cpp`; ARCH 5).
  The constraint header is 4 bytes with trailing glue and id words (STATUS M1-R2-T2).
- **Watch lists**: `WatchList` is MiniSat's `vec<Watcher>` in size, growth and allocation (16-byte
  list header, 8-byte `Watch{Ref, blocker}`), one list per literal and kind, lazy cleaning
  (`watch.hpp`; ARCH 6; STATUS M1-R3-T3).

### 2.2 Search features

| feature | file | default | task |
|---|---|---|---|
| QCDCL with Q-resolution (mode 0), QU-resolution (mode 1), long-distance Q-resolution (mode 2) | `analyze.cpp`, `analyze_qu.cpp`, `analyze_ldq.cpp`, `propagate*.cpp` | mode 0 | M1 |
| dependency learning | `depend.cpp` | off (`--dl`) | M1 |
| QCIR front end with dual Plaisted-Greenbaum encoding, early Tseitin placement; QDIMACS front end | `encode.cpp`, `parse_*.cpp` | `--earlytseitin` on | M1 |
| QLRUP proofs (text and binary), older trace format, internal checker (`--check`) | `proof.cpp`, `qlrup_tracer.cpp`, `trace_tracer.cpp`, `checker.cpp` | off | M1 |
| `used` marks, glue update in analysis, three tiers, reductions on a conflict schedule | `tier.cpp`, `reduce.cpp` | on (`--tiers`, `--glueupdate`, `--tier1glue=2`, `--tier2glue=6`, `--reduceint=300`, `--reducetarget=75`) | M2-T2 |
| tier limits per kind from the usage histogram | `tier.cpp` | off (`--recomputetier`) | M2-T3 |
| root-level simplification (units, strengthening, deletion of satisfied constraints), modes 0 and 1 | `simplify.cpp` | on (`--rootsimp`, `--rootsimpdelay`) | M2-T4 |
| minimisation of learnt constraints with proof chains | `minimize.cpp` | off (`--ccminmode=0`) | M2-T5 |
| restarts by glue averages per kind | `restart.cpp` | off (`--restartmode=0`, Luby) | M2-T6 |
| trail reuse at restarts | `restart.cpp` | on (`--reusetrail`) | M2-T6 |
| bounded variable elimination, before the search and in inprocessing rounds | `elim.{hpp,cpp}`, `flags.hpp` | **off** (`--elim`) | M3 |
| vivification of learnt clauses and cubes in inprocessing rounds | `vivify.{hpp,cpp}` | **off** (`--vivify`) | M4 |

The M1-equivalent option string, which reproduces the search of the M1 binary, is
`--no-tiers --no-glueupdate --reducetarget=50 --reducesize --reduceint=0 --no-recomputetier
--no-rootsimp --ccminmode=0 --restartmode=0 --no-reusetrail` (`tests/m1_equiv.sh`; STATUS H5, M2-T7).

### 2.3 Elimination as built (ARCH 10.0; header of `src/elim.cpp`; STATUS M3 plan, M3-T1 ... T4)

- Existential variables are eliminated by clause resolution, universal variables by cube
  resolution (`--elimclause`, `--elimcube`), before the search (`--elimpre`) and every
  `elimint * (rounds + 1)` conflicts at level 0 (`--eliminp`, `--elimint=2000`).
- Owner's side conditions, checked in every round against the constraints present then:
  the variable is **rightmost** (by block depth; the same block is allowed) in every live
  constraint of its kind, **learnt ones included**, and it occurs in **no constraint of the other
  kind**, original or learnt. The review found them to be the owner's conditions, slightly stricter
  (`reviews/handover.md` section 2).
- Candidates are non-decision (gate) variables of QCIR input only. QDIMACS input and mode 2 are
  excluded with a notice at `--verb=1`. Decision variables are never eliminated, so nothing is
  reconstructed for certificates.
- Bound on added constraints `--elimbound=0`, growing to `--elimboundmax=16`; resolvents subsumed
  by a stored irredundant constraint or an earlier resolvent are dropped (`--elimsubsume=1`);
  limits `--elimocclim=100`, `--elimclslim=100`, `--elimticks=100000000`.
- Proofs: each resolvent is a derived step with its two parents, then the parents are deleted. No
  combination is refused.
- Debug builds re-check the two side conditions by a direct scan before every elimination
  (`check_elimination_owner`), and `check_invariants` checks that no live constraint contains an
  eliminated variable.

### 2.4 Vivification as built (ARCH 10.0; header of `src/vivify.cpp`; STATUS M4 plan, M4-T1 ... T3)

- Learnt constraints only, both kinds through one code path, modes 0 and 1, QCIR and QDIMACS, with
  or without `--dl`. Mode 2: notice, nothing done.
- Only constraints of the candidate's kind propagate; in mode 0 a constraint whose last literal is
  secondary does nothing. A root literal is resolved away only through a unit of the same kind.
- Candidates by tier (`--vivifytier=2`), unchanged ones are not retried until all have been tried
  (`--vivifyonce=1`); rounds every `vivifyint * (n + 1)` conflicts (`--vivifyint=2000`), budget
  `--vivifyticks=2000000` propagation ticks per round.
- Proofs: one derived step and one deletion per shortened constraint. No combination is refused.

### 2.5 Options and defaults

`miniQU --help` prints all options with default and range. Defaults as shipped after M2
(STATUS M2-T7): `mode=0 dl=0 ccminmode=0 tiers=1 glueupdate=1 tier1glue=2 tier2glue=6 reduceint=300
reducetarget=75 reducesize=0 recomputetier=0 rootsimp=1 rootsimpdelay=1 restartmode=0 reusetrail=1`.
Added by M3 and M4, all inactive unless `--elim` or `--vivify` is given:

| option | default | meaning |
|---|---|---|
| `--elim` | 0 | bounded variable elimination |
| `--elimclause`, `--elimcube` | 1, 1 | the two kinds |
| `--elimpre`, `--eliminp` | 1, 1 | before the search, in inprocessing rounds |
| `--elimint` | 2000 | conflicts between rounds (growing arithmetically) |
| `--elimbound`, `--elimboundmax` | 0, 16 | constraints an elimination may add; largest value the bound grows to |
| `--elimsubsume` | 1 | drop subsumed resolvents |
| `--elimocclim`, `--elimclslim`, `--elimticks` | 100, 100, 100000000 | occurrence limit, resolvent size limit, literal visits per round |
| `--vivify` | 0 | vivification of learnt constraints |
| `--vivifyclause`, `--vivifycube` | 1, 1 | the two kinds |
| `--vivifyint`, `--vivifyticks` | 2000, 2000000 | conflicts between rounds; propagation ticks per round |
| `--vivifyonce`, `--vivifytier` | 1, 2 | do not retry unchanged constraints; highest tier vivified |

With both options off the search is the search of the binary before M3: verdict and
conflicts/decisions/propagations/ticks equal on 80/80 (M3-T1, M3-T2, M3-T4), 48/48 (M4-T1), 36/36
(M4-T2), 80/80 (M4-T3) and 32/32 (review) corpus runs. `tests/m1_equiv.sh` was not run after M2-T8.

### 2.6 Test and benchmark tooling

- `ctest`: unit tests (one executable per file of `test/unit/`), format check, encoder comparison
  with the baseline, regression instances (`tests/regressions/`, also with `--elim`), a 20-seed
  fuzz run, tests of the bench tools.
- `tests/regress.sh` with `tests/matrix.txt` (67 rows: 43 up to M2, 14 `elim*`, 10 `vivify*`):
  verdicts against the brute-force evaluator and the baseline, every proof to the Lean checker,
  required counters per row, stress rows with time-out limits.
- `tests/fuzz.sh`, `tests/fuzz_qdimacs.sh`, `tests/fuzz_cert.sh` with `tests/check_cert.py`,
  `tests/m1_equiv.sh`, `tests/run_regressions.sh`.
- `bench/run.py`, `compare.py` (plain and paired), `gate.py`, `fidelity.py`, `overhead.py`,
  `load_measure.py`, `l3.sh`/`cross.sh`/`nb.sh` (`bench/README.md`); new at hand-over:
  `bench/cluster/` (Slurm templates and `merge.py`).

## 3. What was verified, per technique

"Lean" means proofs accepted by `qlrup-check`. Seeds are corpus seeds of `tests/corpus.py`.

### 3.1 M1 (port): verified in full

- Independent verification of round 3 (review `M1-r3.md` section 2): matrix seeds 1:300 on the
  release build with Lean, sanitizer build seeds 1:100 at `-t 240`, QDIMACS fuzz 1:300 in four
  modes, regressions: clean. Reviewer's own run on seeds 8001:8060: passed, 3 warnings (solver
  time-outs); 7 of 7 proofs of benchmark instances verified.
- Same search as the baseline where the baseline's order of equal scores is reproduced (STATUS
  M1-T11); round 3 against round 2: 1513 of 1513 compared runs identical (`M1-r3.md` section 1).
- Benchmarks, 376 instances, 60 s, 48 jobs on a 96-core machine, seeds 1-3 for default and `-dl`,
  seed 1 for mode 1, mode 2 and `--ccminmode=3`, against same-machine baseline runs
  (`bench/results/M1-r3-report.md`, tables in `M1-r3-reports/`):
  - no discrepancy, error or mismatch in 9 runs;
  - paired PAR2 difference new - baseline: default +0.00 s [-0.77, +0.80], `-dl` -0.11 s
    [-0.82, +0.56], mode 1 +0.20 s, mode 2 -1.39 s, ccmin3 -1.52 s; all "no measurable difference";
  - identical searches (equal conflict counts), CPU time new/baseline, pooled geometric mean:
    default 0.964 (n=51), `-dl` 0.950 (n=51), mode 1 0.990 (n=36);
  - one gate line not met: family `jctc`, default, 1.330 (n=4). The reviewer closed it as noise
    (the baseline shows the same factor against itself, `M1-r3.md` section 4.2; STATUS H1).
- Proof coverage of the M1 binary on the benchmark set (STATUS M2-T1, tag
  `M1-r3-proofcov-default-s0`): 151 solved in 60 s, proofs attempted for the 117 solved within
  20 s, 117 accepted, 0 rejected; 3.8 GB of binary proofs, slowest check 329 s.
- Reviews: `M1-r1.md` and `M1-r2.md` not approved (engine speed under benchmark load: 12-byte
  header, then 64 bytes of watch-list headers per literal), `M1-r3.md` approved.

### 3.2 M2: verified up to its gates, not benchmarked as a whole, not reviewed

- Gate on the final M2 sources (STATUS M2-T8, `bench/results/M2-T8-gate/`; 43 rows at that time):
  release, debug, asan and clang builds without warnings; `ctest` 43/43; `tests/m1_equiv.sh` passed;
  matrix seeds 1:300 release with smoke set and Lean: passed, 0 wrong verdicts, 0 rejected proofs,
  6 warnings (solver time-outs; stress rows within their recorded limits); asan seeds 1:100 at
  `-t 240`: passed, 0 sanitizer reports; QDIMACS fuzz 8 x 600 instances agreed; 12 regression
  instances.
  Some proof checks reached the checker time limit (row `mode1-dl` 18 in M2-T7) and are warnings.
- Screening of the experiment options (STATUS M2-T7, `bench/results/M2-screen-reports/`), one seed,
  60 s, 24 jobs on a 48-core machine: `--ccminmode=3` default +1.26 s PAR2 and `-dl` +0.40 s,
  `--restartmode=1` default +0.84 s, all "no measurable difference"; none passes the 2.0 s rule, so
  no default changed. **Not screened**: `--recomputetier`, `--ccminmode=2`, `--restartmode=1 -dl`.
- `jctc` family under `-dl` (STATUS M2-T11, `bench/results/M2-T11-jctc/report.md`): 12 instances,
  20 seeds, 60 s, 11 arms. M2 default 70 time-outs of 240 against 66 for the M1 binary and 61 for
  the baseline, p = 0.58: no regression shown. Side observation, not attributed: `jctc10-fail` and
  `jctc14-unrolled-fail` time out more often with trail reuse in the configuration without `-dl`.
- **Missing** (owner decision "wrap up in 24 hours", point 1): the independent verification of M2,
  its benchmark stage against the baseline (no M2 run of the 376 instances with seeds 1-3 exists;
  only the screening runs at seed 4), the M2 proof-coverage run, and the review.
- The only runs of the whole benchmark set with the final defaults are the hand-over runs of
  section 4.

### 3.3 Elimination (M3): short runs only

| check | result | source |
|---|---|---|
| unit tests `unit-elim` (side conditions, resolvent cases, schedule, learnt constraints, `-dl` reset, subsumption, bound, invariants, three death tests) | pass, release and debug | STATUS M3-T1 ... T4 |
| matrix, 14 `elim*` rows, seeds 1:30, release, Lean | passed; 418 proofs accepted, 0 wrong verdicts; 2 time-outs in `elim-noearly` (the plain `noearly` row has time-outs on these seeds too, M3-T1) | M3-T4 |
| same rows, debug build, seeds 1:10 | no assertion or invariant failure, no wrong verdict; run marked FAILED on stress limits and counter coverage (5 search instances, 60 s); **not rerun** | M3-T3 |
| whole matrix seeds 1:50, release, at `b80f334` | no wrong verdict, no rejected proof; row `elim-inp-gc` 1 of 25 time-outs (limit 2%) | `bench/results/handover-report.md` |
| row `elim-inp-gc` after the change to `--reduceint=10` | seeds 1:50 passed, 50 proofs; 100 instances: 0 time-outs | STATUS "Hand-over defects" |
| certificates, `tests/fuzz_cert.sh` | seeds 100:400 and 401:1000 with elimination and vivification stressed: no INVALID after the B1 fix | STATUS "Hand-over defects" |
| real files | 8 smallest per family, with and without `--elim`: same verdicts; 6 proofs Lean-verified (all SAT) | M3-T3 |
| real files in the review | 28 files x 4 configurations (elimination or vivification, each with and without `-dl`) with proofs: 80 verified, 3 solver time-outs at 120 s | `reviews/handover.md` section 5 |
| benchmarks, yield measurement, tuning | **none** | |

### 3.4 Vivification (M4): short runs only

| check | result | source |
|---|---|---|
| unit tests `unit-vivify` (12 cases), `vivified` bit | pass, release and debug | M4-T1, M4-T2 |
| matrix, 10 `vivify*` rows, seeds 1:30, release, Lean | passed; 297 proofs accepted, 3 proof checks timed out (`vivify-mode1-dl`), 0 wrong verdicts | M4-T2 |
| rows `vivify`, `vivify-int1`, debug build | passed, 60 proofs | M4-T1 |
| explicit configurations (mode 1, `-dl`, both, `--elim`, clause only, mode 2), seeds 1:60 | passed, 300 proofs | M4-T1 |
| QDIMACS fuzz with `--vivify` | 60 + 60 + 540 instances agreed; review: 600 runs with `--check`, all verdicts equal to the baseline | M4-T1, M4-T2, review |
| real files | 12 files x 5 configurations: 60 verdicts equal; 6 proofs Lean-verified (4 TRUE, 2 FALSE) | M4-T3, `bench/results/m4-sanity/` |
| benchmarks, ablations, tuning | **none** | |

### 3.5 Hand-over runs

- Test worker at `b80f334` (`bench/results/handover-report.md`): release build without warnings,
  `ctest` 45/45, whole matrix seeds 1:50 without the smoke set: no wrong verdict, rejected proof or
  crash; one failure (row `elim-inp-gc`, a stress time-out limit; the row was changed afterwards);
  some proof checks timed out (warnings).
- Reviewer at `36ffcfa` (`reviews/handover.md` section 5): about 28 minutes of `tests/fuzz.sh` in
  five configurations (debug, asan, release) with both techniques stressed, no failure line (the
  runs were killed before their totals); the certificate runs that found B1.
- After the B1 fix, at `06c3ab6` (STATUS "Hand-over defects"): `ctest` 46/46, release and debug
  builds without warnings, 12 matrix rows seeds 1:30 passed with every proof Lean-checked, search
  unchanged on 60 runs. **Not rerun after the fix**: the whole matrix, sanitizer fuzz, `m1_equiv`,
  smoke set, benchmarks.
- At `95bfa16` (the last commit that changes sources or tests), when this report was written:
  release build up to date, `ctest --preset release` 46/46.

## 4. Benchmark results that exist

All in `bench/results/`. Timings are comparable only between runs of the same machine type and
harness settings (`bench/README.md`, "Core convention"); the machine changed twice (128, 96, 48
cores).

| result | what | use |
|---|---|---|
| `baseline-t180`, `baseline-dl-t180`, `baseline-t900`, `baseline-t180-vs-dl.md` | baseline, 64 jobs on the 128-core machine; 180 s: 167 solved default, 168 `-dl` | verdict checks only |
| `baseline-c96-*-t60-s*` | baseline, 96-core machine, 48 jobs, 60 s | reference of the M1 gates |
| `M1-r1-*`, `M1-r2-*`, `M1-r3-*`, reports `M1-r?-report.md`, `M1-r?-reports/` | the three M1 rounds | section 3.1 |
| `M1-r3-proofcov-default-s0` | proof coverage of the M1 binary | section 3.1 |
| `M2-screen-*`, `M2-screen-reports/` | screening, seed 4, 48-core machine | section 3.2 |
| `M2-T7-gate/`, `M2-T8-gate/` | test gates of M2 (row tables, summaries) | section 3.2 |
| `M2-T11-jctc/` | 5280 runs on 12 `jctc` instances | section 3.2 |
| `m4-sanity/` | 12 files with vivification | section 3.4 |
| `handover-default-t30`, `handover-dl-t30`, `handover-report.md` | final defaults at `b80f334`, 30 s, 24 jobs on the 48-core machine, one run each | below |

Hand-over runs: default 132 of 376 solved (82 SAT, 50 UNSAT), `-dl` 144 (80 SAT, 64 UNSAT), 0
errors; no verdict discrepancy against `baseline-t180`, `baseline-dl-t180` or between the two.
Proofs were not requested. They are one run each at 30 s on a different machine than every
baseline run, so they support no statement about speed.

There is **no** benchmark of elimination or vivification, no same-machine comparison of the final
binary with the baseline, and no run longer than 60 s of the new solver.

## 5. Reviews

| review | verdict | main points |
|---|---|---|
| `00-architecture.md` | not approved, five blocking items in the two documents | all accepted, answered in ARCH 13 |
| `M1-r1.md` | not approved | B1: engine speed under the benchmark protocol |
| `M1-r2.md` | not approved | B1: `DW` family 12-27% slower on identical searches |
| `M1-r3.md` | approved | `jctc` gate line is noise; three follow-ups for the coordinator (STATUS "M2 plan and decisions") |
| M2 | **no review** | owner decision |
| `handover.md` (M3, M4) | not approved as it stood: B1 | below |

Hand-over review: by reading and by its runs the reviewer found no wrong verdict, crash, rejected
proof or changed default in elimination and vivification, and no hole in the soundness arguments of
either (its section 2). **B1**: `-cert` printed an invalid certificate when the formula was decided
at level 0 by a reduction to the empty constraint; the defect was in root simplification (default
configuration, since M2-T4). It was fixed afterwards in commit `06c3ab6` (STATUS "Hand-over
defects"): the constraint before reduction is kept and `record_certificate` takes the move from it;
unit tests, two regression instances and `fuzz_cert.sh` on seeds 100:1000 show no INVALID. The fix
has not been seen by the reviewer. The seven suggestions of the review (shared epilogue of the
three root-level units, unbounded cost of elimination rounds, the vivification budget, two real
files that timed out with a technique on, untested sub-defaults, dead dependency-reset path, silent
no-op in mode 2 and on QDIMACS) are open; none was acted on.

## 6. Known defects and limits

1. **Mode 1 certificates are wrong**, also in the baseline: `fuzz_cert.sh` seeds 100:400 with
   `-mode=1` gives INVALID certificates (28 of 37 kept files with `-mode=1` alone; the baseline is
   INVALID on 29 of them). Not investigated. Files in `/home/ec2-user/miniqu-work/b1fix/keep-d/`
   (on the machine that is given up; reproduce with `tests/fuzz_cert.sh BIN 100 400 -mode=1`).
   STATUS "Hand-over defects", list item 1.
2. `tests/check_cert.py` reports MALFORMED when a `free` block is followed by an `exists` block
   (the solver merges them); therefore `run_regressions.sh` checks certificates of `*-cert-*` files
   only. Same entry, item 2.
3. The vivification and elimination paths of the B1 fix (empty vivified constraint, empty
   resolvent) have no unit test. Same entry, item 3.
4. No proofs in mode 2 and for QDIMACS input (format: `ROADMAP.md` summary table). Vivification on
   QDIMACS input is covered by `--check` and verdict comparison only.
5. A QCIR run that would need an initial cube from a model ends with "unknown" (STATUS M2-T9, J8).
   Not observed after elimination in any run (`modelcubes` 0 on 8 real files, no missing-cube exit
   in the fuzz runs), but that is all the evidence there is.
6. Elimination rounds have no effort limit relative to the search: each round rebuilds the
   occurrence lists of the whole database. Vivification counts propagation ticks only and adds
   them to `stats.ticks` (review suggestions 2 and 3).
7. With proof logging, `jctc8-pass` (`--elim`; `--vivify --vivifytier=3`) and
   `klieber2017q-108-27-t1` (`--vivify --vivifyint=100 --vivifytier=3`) did not finish in 120 s in
   the review, while the default solved them in 4-5 s in the 30 s runs. Not attributed (review
   suggestion 4).
8. Proof checks that reach the checker's time limit are counted as warnings: row `mode1-dl` (18 at
   seeds 1:300 in M2-T7, 3 at 1:50 at hand-over), `vivify-mode1-dl` (3 at 1:30). These proofs are
   unchecked, not accepted.
9. `2.1.qcir` reaches the 8 GB memory limit (baseline too), `5.2-3.qcir` sometimes
   (`M1-r3-report.md`).
10. `jctc9-pass` in the default configuration times out; whether the M2-T8 binary searches as the
    M2-T7 binary on it could not be compared (no conflict limit option; STATUS M2-T8).
11. The debug-build matrix run of the `elim*` rows failed on stress limits and counter coverage
    with a small sample (M3-T3) and was not repeated.
12. Scripts carry absolute paths of the development machine (`HANDOFF.md` section 1.5).
13. Harness pitfall: `xargs -L1` joins a line ending in a blank with the next one; a solver given
    two files takes the second as its result file and overwrites it (STATUS M4-T1).
