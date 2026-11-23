# miniQU rewrite: roadmap

Companion to `ARCHITECTURE.md` (referred to as ARCH). Milestones are done in
order; inside a milestone the numbered work packages are sized for one worker
task each and are done in order unless marked independent. `STATUS.md` records
what is finished.

Classes (D), (R), (N) of a technique are defined in ARCH 11.2; the invariants
INV-* in ARCH 4.3; the admissibility criterion (LO)/(HI) for QDIMACS input
and the facts F1-F4 in ARCH 11.1.

Revision 2 (after review 00): section 0 is largely new (test corpus, stress
configurations, coverage assertion, benchmark statistics, proof coverage,
packages P0.1-P0.4); M2.1 and M3 carry the corrected soundness arguments;
QDIMACS elimination moved to the optional M3.6. ARCH 13 maps review items to
changes.

---------------------------------------------------------------------------

## 0. Rules that apply to every work package

### 0.1 Definition of done

A package is done when all of the following hold, and its `STATUS.md` entry
says so with the commands that were run:

1. `release`, `debug` and `asan` presets build without warnings (GCC), and
   `release` also builds with Clang.
2. Unit tests pass (`ctest`), including new tests for the new code.
3. `tests/regress.sh` passes for the **configuration matrix** below, normal
   and stress configurations, on both corpus tiers, with at least seeds 1:300
   on the `release` binary and seeds 1:100 on the `asan` binary (the
   `asan`/`debug` binaries run the internal `Checker`). Zero wrong answers,
   zero rejected proofs, zero crashes, zero sanitizer reports, **and the
   coverage assertion holds** (below). A failure is reported with its
   reproducing command, never worked around.
4. If the package can affect performance: a benchmark comparison against the
   previous accepted state (0.3).
5. The header comment of each new technique file states class, QBF side
   conditions and proof steps; new options, statistics and profiles are in
   their tables; `ARCHITECTURE.md` is still true.

#### The corpus has two tiers

Measured on the baseline (review 00, B1): the instances `tests/fuzz.sh`
generated so far need 0-5 conflicts, so they test parsing, encoding and the
first conflict, and nothing that is scheduled. From P0.1 on the corpus is:

- **tiny tier**: the existing `qcir_fuzz.py` instances, small enough for
  `tests/qcir_eval.py`. Purpose: ground truth for verdicts.
- **search tier**: generator parameter sets (`qcir_gen.py` families and
  `qcir_fuzz.py` with larger parameters) chosen so that the baseline with
  default options needs **between 10^2 and 10^4 conflicts** and the Lean
  checker finishes the proof within the fuzz limit (120 s). Requirement: at
  least 70% of the search-tier instances fall in that range for the baseline
  default and for `-dl`, and at least 90% of their proofs are checked within
  the limit. Verdicts are checked against the baseline and across
  configurations; proofs by the Lean checker.

`regress.sh` runs both tiers for every seed range (half of the seeds each).
The worker who builds the search tier reports its **conflict histogram**
(buckets 0-9, 10-99, 100-999, 1000-9999, >= 10^4; per parameter set; baseline
default and `-dl`) in `STATUS.md`, and it is re-measured with the new solver
at M1.9 and at every later gate, because heuristics move it. QDIMACS gets the
same two tiers in `tests/fuzz_qdimacs.sh` (M1.8).

#### Configuration matrix

`tests/matrix.txt`, one configuration per line: name; solver options; whether
proofs are checked; the counters that must be nonzero. The matrix grows with
the milestones: every new on/off option adds "default with the option
flipped", and every new scheduled event adds a stress configuration.

Normal configurations (M1):

```
(default)      -dl      -mode=1      -mode=1 -dl      -mode=2      -mode=2 -dl
-ccminmode=3   -dl -ccminmode=3      -no-earlytseitin -legacyanalyze
```

**Stress configurations** make every scheduled event fire many times on an
instance with a few hundred conflicts. The options and their ranges are
specified in ARCH 9.1; each milestone adds its own:

| from | name | options | combined with | counters that must be nonzero |
|---|---|---|---|---|
| M1 | `gc` | `--reduceint=N --tier1glue=0 --gcfrac=0`; N = 2 (default), 30 (`-dl`), 100 (`-mode=1`), 10 (`-mode=2`), see the note below | default, `-dl`, `-mode=1`, `-mode=2` | `reductions`, `reduced`, `collections`, `relocated` |
| M1 | `restart` | `--no-luby --rfirst=1 --rinc=100 --depreset=1`; with `-mode=1 -dl`: `--rfirst=1 --depreset=1` (Luby) | default, `-dl`, `-mode=1 -dl` | `restarts`; with `-dl` also `dependencies`, `depresets` |
| M2 | `tier` | `--tier1glue=0 --tier2glue=0` and `--tier2glue=1`, each with `--reduceint=2 --gcfrac=0` | default, `-dl` | as `gc`, plus `promoted`, `used` |
| M2 | `root` | root simplification with every throttle at its minimum | default, `-dl`, `-mode=1` | `rootunits`, `rootstrengthened`, `rootdeleted` |
| M2 | `min` | `--ccminmode=2`, `--ccminmode=3` (now with proofs) | default, `-dl`, `-mode=1` | `minimized` |
| M2 | `ema`, `stable`, `rephase` | `--restartint=1`; mode switching and rephasing at their smallest intervals | default, `-dl` | `restarts`, `stabilized`, `rephased` |
| M2 | `arena` | `--arenaorder=1 --gcfrac=0 --reduceint=2` | default | `collections`, `relocated` |
| M3 | `elim` | `--inprocessint=3 --elimeffort=<max> --subsumeeffort=<max> --elimbound=16 --gcfrac=0` | default, `-dl`, `-mode=1`, `-no-earlytseitin`, `-mode=2` | `inprocessings`, `eliminated.clause`, `eliminated.cube`, `resolvents`, `subsumed`, `strengthened` |
| M4 | `vivify` | `--inprocessint=3 --vivifyeffort=<max> --gcfrac=0` | default, `-dl`, `-mode=1`, with and without `--elim` | `vivifychecked`, `vivified.clause`, `vivified.cube` |

Counter names are those of `stats.hpp` and may be adjusted by the
implementing package, in `matrix.txt` and here in the same commit. A normal
configuration requires `conflicts`, `restarts`, `learned.clause` and
`learned.cube` to be nonzero, and every option it flips has its counter
listed (`-dl`: `dependencies`; `-ccminmode`: `minimized`; ...). Mode 2
configurations run without proof checking; everything else with it.

#### Coverage assertion

`regress.sh` runs the solver with statistics on, sums the `c stat` lines
(ARCH 9.2) over the search-tier instances of each configuration, prints the
table of sums, and **fails** if a required counter is nonzero on fewer than
10% of those instances. A test that has silently stopped testing is a
failing test. If a counter cannot be made nonzero by options alone (root
units on random instances, say), the generator gets a parameter set that
does it; the requirement is not dropped. The script is itself tested once
with a solver that answers correctly but prints zero counters (must fail).

Stress configurations change the search, so a run may not finish: the solver
limit applies, timeouts are counted per configuration, and more than 2%
timeouts on the search tier is a failure to be investigated, not a warning.
`gc` and `restart` are separate configurations on purpose: restarting after
every conflict while deleting almost every learnt constraint need not
terminate. The arithmetic growth of `reduceint` (ARCH 9.1) is what keeps `gc`
terminating.

*Amended after M1 round 1 (STATUS "Coordinator decisions after M1 round 1",
with the measurements):* the stress options are per row, and a row of
`tests/matrix.txt` may carry its own timeout limit in an optional sixth
field (percent, default 2). M1 values: `gc` 2%, `gc-dl` 2%, `gc-mode1` 5%,
`gc-mode2` 2%, `restart` 2%, `restart-dl` 8%, `restart-mode1-dl` 25%. A
limit above 2% is allowed only with a measurement showing that the baseline
(or the closest configuration it has) times out at a comparable rate on the
same instances, i.e. that the timeouts are a property of the algorithm under
that schedule and not of the port. The solver limit of the gate is 20 s for
the `release` binary and 90 s (`-t 90`) for the `asan` binary, which is 7 to
13 times slower. The extreme setting `--reduceint=2` stays exercised with
`-dl`, `-mode=1` and `-mode=2` by `tests/fuzz_qdimacs.sh` (verdicts only,
timeouts counted), which is part of every gate from M1 on.

### 0.2 Correctness beats everything

Any disagreement (with the baseline, with `tests/qcir_eval.py`, between two
configurations, between QDIMACS and its QCIR conversion) and any proof the
Lean checker rejects is a blocking bug: stop feature work, minimise the
instance (`qbfdd.py` or by hand), fix, add the instance to
`tests/regressions/`. Never weaken a test, the `Checker`, or the Lean checker.

### 0.3 Benchmark protocol

Harness: `bench/run.py`, `bench/compare.py` (see `bench/README.md`; P0.2
adds what this section needs). All 376 instances.

#### Fixed run parameters

*Amended (machine change, STATUS "Coordinator decisions after M1 round 1"):*
the instance type changed from 128 to 96 cores after this section was
written. Every timed run now uses the upper half of the cores
(`nproc/2 .. nproc-1`), `--jobs nproc/2` and `--mem-gb 8`, one core per job;
these are the defaults of `bench/run.py`, computed from `nproc`. Every other
heavy command uses the lower half (`taskset -c 0-$((nproc/2-1))`), at most 16
parallel jobs. Timings are comparable only between runs of the same instance
type and harness settings: `baseline-t180`, `baseline-dl-t180` and
`baseline-t900` (64 jobs on the 128-core machine) serve verdict checks only,
and each comparison needs a same-machine baseline run tagged
`baseline-c<NPROC>-<config>-t<TIMEOUT>` whose `meta.json` matches. The
numbers in the rest of this subsection are the original ones and are kept
for the record.

Originally: every timed run uses `--cores 64-127 --jobs 48 --mem-gb 16`, one core per
job. `compare.py` refuses to compare runs whose `jobs`, `mem_gb`, `cores`,
`timeout` or instance list differ (they are in `meta.json`); the override
flag prints "NOT COMPARABLE" at the top of the report.

- 16 GB is the limit of the arena's 32-bit word offsets, so no run can use
  more for constraints; the three baseline memouts at 8 GB in the first run
  (`numeric/2.1`, `2.2`, `5.2-3`) show that 8 GB decides instances by parser
  memory rather than by search.
- 48 jobs, not 64: 48 x 16 GB is above the machine's RAM only in a worst case
  that the first run shows to be far away (three instances above 8 GB), and
  it leaves memory bandwidth headroom on the socket. P0.4 confirms this with
  the sum of the 48 largest RSS values of the baseline.
- The runs already in the tree, `baseline-t5` and `baseline-t180` (8 GB,
  64 jobs, no seeds), are **informational only**. No acceptance statement may
  cite them.

Tiers: **quick** = 60 s timeout (about 6 minutes per run), **full** = 600 s
(about 50 minutes per run).

#### Seeds: measuring search variance

The solver is deterministic, so running a binary twice measures machine
timing and nothing else. What a code change perturbs is the search, and the
size of *that* effect is measured by perturbing the search on purpose:
`--seed=s` randomises the initial variable scores (ARCH 7.3), for the
baseline `-rnd-init -rnd-seed=s`. A **run set** is one binary with one
configuration over a seed list:

| tier | seeds | used for |
|---|---|---|
| quick | 1, 2, 3, 4, 5 | iterating, screening ablations |
| full | 11, 12, 13 | milestone acceptance, any change of a default |

Both arms of a comparison use the same seed list. The full tier uses seeds
the quick tier has not seen, so that a full-tier result is a replication of a
quick-tier one and not the same draw again. Seed 0 (the deterministic
default, what a user runs) is used for proof coverage and overhead (below).
The spread of solved counts and PAR2 over the seeds of one run set is that
arm's **noise band**; it is reported for every arm and is descriptive.

#### What counts as evidence

`compare.py --paired` takes two run sets A and B and computes, with timeout
`t`:

- per instance and arm, the score `s` = mean over seeds of the PAR2 time
  (the time if solved, `2t` otherwise);
- `d_i = s_i (B) - s_i (A)` and `Δ` = mean of `d_i` over all instances (the
  PAR2 difference), with a **95% bootstrap confidence interval** (resampling
  instances, 10 000 resamples, fixed generator seed, percentile method);
- a **sign test**: wins = instances with `d_i < -m_i`, losses = instances
  with `d_i > m_i`, where `m_i` = max (1 s, 10% of the smaller score);
  two-sided binomial p-value;
- per seed: solved (SAT/UNSAT/total) and PAR2 for both arms.

Definitions used by every gate in this document:

- **B is better than A**: the confidence interval of `Δ` lies entirely below
  0, and the sign test does not point the other way (more losses than wins
  with p < 0.05).
- **B is not worse than A**: the confidence interval of `Δ` does not lie
  entirely above 0, and the sign test does not show more losses than wins
  with p < 0.05.
- Anything else is "no measurable difference" and is reported in those words.

The bootstrap treats instances as independent, and instances of one family
are not; so the per-family table is part of every report, and a result
carried by one family is reported as a result about that family.

Statements and what they need:

| statement | evidence |
|---|---|
| "X helps" / an **experiment** item becomes default | screening: better at the quick tier in at least one main configuration and not worse in the other; then the same at the full tier (fresh seeds). Both steps, on/off with one binary |
| an **adopt** item stays default | not worse at the quick tier in both main configurations; if it is worse in either, it is an experiment item from then on |
| milestone acceptance | the milestone's default against the previous milestone's (M1: against the baseline) at the full tier, both main configurations, criterion as stated per milestone |
| any report | no family that collapses without an explanation; losses reported as prominently as gains |

Screening exists because of cost and because of chance: M2 alone has six
experiment items in two configurations, and at 95% some would pass a single
test by luck. An item that passes must pass twice, on different seeds.

- **Configurations**: default and `-dl` are both first-class (the README
  deliberately recommends neither); every comparison covers both. Modes 1 and
  2 are run at the quick tier (seeds 1-3, default heuristics) once per
  milestone, with this gate: no discrepancy with any other run; mode 1 proofs
  as below; and not worse than the same mode at the previous milestone (M1:
  than the baseline in that mode).
- **Ablations**: a technique is judged by the same binary with its option on
  and off, not by comparing different commits.
- **Report** (markdown from `compare.py`, committed under
  `bench/results/<tag>/` together with the CSVs): the fixed parameters;
  discrepancies first; per-seed solved and PAR2 for both arms; `Δ` with its
  interval and the sign test; instances gained and lost in a majority of
  seeds, by name; per-family table; largest speedups and slowdowns; peak
  memory; the proof coverage table.
- Tags: `<milestone>-<what>-<config>-t<timeout>-s<seed>`, e.g.
  `m2-tiers-on-dl-t600-s11`.

#### Proof coverage

The owner's requirement is that proofs are checked by the Lean checker, and
the runs that matter most are the long ones, in which reduction, garbage
collection and inprocessing rounds happen. So coverage is a reported
quantity with a floor, not a side effect.

- **Coverage table**, in every report that involves proofs: instances solved;
  proofs attempted; accepted; rejected; checker timeout; checker memout;
  proof too large; not attempted (with the reason). Every category except
  "accepted" lists its instances by name. A rejected proof is a blocking bug
  (0.2); the other non-accepted categories are coverage gaps and are reported
  as such, never as "warnings".
- **Routine comparisons** (quick tier): the "on" arm, seed 1, with
  `--proof-check --proof-max-solve-sec 60`, i.e. a proof is attempted for
  **every** solved instance.
- **Milestone gates**: the milestone's default binary with seed 0, in the
  configurations default, `-dl`, `-mode=1`, quick tier: a proof is attempted
  for every solved instance, with a generous checker limit (3600 s, 32 GB);
  on a checker timeout or memout the proof is trimmed with `qlrup-trim` and
  checked again. At most 6 proof jobs at a time on cores 0-63; a proof larger
  than 8 GB is abandoned as "too large" (disk: at most 48 GB of proofs at any
  moment; every proof is deleted after its check).
- **No unexplained drop**: an instance whose proof was accepted at the
  previous gate in the same configuration and that is still solved within
  60 s must be accepted again, or is listed by name with the reason. The
  reference for M1 is the baseline's coverage table from P0.4.
- **Proof overhead**, once per milestone: seed 0, default and `-dl`, quick
  tier, timed on the benchmark cores with the proof written to a file in the
  work directory (binary format) against the same run without a proof.
  Reported on the instances solved by both: total and geometric-mean time
  ratio (instances above 1 s), proof bytes in total and per conflict, and the
  size after `qlrup-trim`. There is no threshold in M1 (the baseline's
  overhead from P0.4 is the reference); from M2 on an increase of the time
  ratio over the previous milestone needs an explanation.
- At the full tier proofs are not attempted beyond what the quick tier
  covers: a 600 s proof can exceed the disk.

### 0.4 Preparatory packages (before M1.3; independent of M1.1 and M1.2)

These exist because of review 00. They change tests and tooling only.

- **P0.1 Search-tier corpus, matrix, coverage assertion** (0.1). Generator
  parameter sets and the histogram; `tests/matrix.txt`; `regress.sh` reads
  it, sums `c stat` counters, enforces the 10% rule and the 2% stress-timeout
  rule. Until the new solver exists, the corpus is validated with the
  baseline (conflict counts from its statistics) and the assertion with fake
  solvers.
- **P0.2 Harness** (0.3). Seeds and run sets; fixed parameters as defaults
  and the comparability check; `compare.py --paired` (bootstrap, sign test,
  per-seed table); coverage table; `--proof-max-solve-sec` up to the timeout,
  trim-and-retry, proof size cap; a `{proof}` placeholder in `--args` for
  timed proof-on runs; storing the `c stat` counters per instance. Unit-test
  the statistics on synthetic CSVs (identical arms give "no measurable
  difference"; a uniformly faster arm gives "better").
- **P0.3 Elimination yield** (review 00, S1; see M3.0). Can run any time.
- **P0.4 Baseline reference runs** (after P0.2): baseline default and `-dl`,
  quick tier seeds 1-5 and full tier seeds 11-13; modes 1 and 2 at the quick
  tier, seeds 1-3; the seed-0 coverage table and proof overhead of the
  baseline at the quick tier. These are the only baseline numbers M1 is
  compared with.

---------------------------------------------------------------------------

## M1. Port with feature parity

Goal: the new tree does everything the baseline binary does, with the same
heuristics, in the structure of ARCH. Not a goal: identical search traces
(hash orders and tie-breaking differ); the gate is equal verdicts and
comparable performance.

Parity list: QCIR (and/or/xor/ite, `free`, case-insensitive keywords, error
messages for malformed input) and QDIMACS (plain and gzip); modes 0/1/2;
`-dl`; `-early-tseitin`; `-legacy-analyze`; `-ccmin-mode` 0-3; `-cert`;
`-proof`, `-proof-binary` (QCIR, modes 0/1); `-trace`; `-cpu-lim`,
`-mem-lim`; `-verb`; result line and exit codes; SIGINT handling.
Intentionally dropped: see ARCH 1 and 9.1.

Work packages:

- **M1.1 Skeleton and base.** CMake/presets/clang-format/unit-test hook;
  `lit`, `arena`, `constraint.hpp`, `watch`, `heap`, `options`, `stats`,
  `profile`, `logging`, `message`, `contract`, `file`. Unit tests: arena
  alloc/free accounting and growth; relocation and forwarding; watch
  smudge/lookup/clean; heap; option parsing including the legacy spellings.
- **M1.2 Frontend.** `circuit`, `parse_qcir`, `parse_qdimacs`, `encode`.
  The old parser builds a `std::string` per token and peaks above 1.5 GB on
  the larger benchmark files before search starts: the new one reads through
  a fixed buffer, interns identifiers once, and stores gate inputs in one
  flat array. Unit tests: every syntax error, xor/ite expansion and gate
  numbering against `doc/proof-format.md`, polarities, depths, block merging,
  the variable order of ARCH 4.4 on hand-written examples.
- **M1.3 Search core, mode 0, prefix order.** `prefix`, `constraint.cpp`,
  `assign`, `propagate` (the one templated watch loop of ARCH 7.2 from the
  start), `decide`, `backtrack`, `analyze`, `learn`, `bump`, `restart`
  (Luby), `reduce` (old policy, see notes), `collect` (arena GC only),
  `model`, `solver`, `app`. Requires P0.1. Also in this package, because the
  tests depend on them: the stress options of ARCH 9.1 (`gcfrac=0`,
  `reduceint`, `tier1glue`, restart ranges), `--seed`, and the `c stat`
  lines of ARCH 9.2. First end-to-end fuzzing against the baseline, with the
  `gc` and `restart` stress configurations and the coverage assertion.
  **Header measurement** (review 00, S3): propagations per second and peak
  RSS against the baseline on the ten largest instances the baseline solves
  and on ten with the highest propagation counts, in `STATUS.md`. If
  propagation is slower or RSS higher than the baseline beyond what the
  parser explains, try the 12-byte header (ARCH 5.2) before going on and
  report both.
- **M1.4 Proofs.** `proof`, `tracer`, `qlrup_tracer`, `checker`; logging
  points of ARCH 8.2 that exist so far. From here on every package runs with
  Lean proof checking.
- **M1.5 Dependency learning.** `depend.cpp`, single heap, eligibility,
  learning and resetting dependencies.
- **M1.6 Modes 1 and 2.** `analyze_qu`, `propagate_ldq`, `analyze_ldq`,
  `-legacy-analyze`.
- **M1.7 Remaining features.** `minimize` (modes 1-3, still off when a
  tracer is connected, as in the old solver), `certificate`,
  `trace_tracer`, limits, signals, statistics output.
- **M1.8 Tests that do not exist yet.** (independent of M1.3-M1.7, can start
  after M1.2)
  - `tests/fuzz_qdimacs.sh`: QDIMACS instances from `qbfuzz.py`; the new
    solver on the QDIMACS file must agree with the baseline on the same file
    and with the new solver on `tests/qdimacs2qcir.py` output (and with
    `qcir_eval.py` when small).
  - `tests/check_cert.py`: validates a `V` line by substituting it into the
    formula and deciding the result with `qcir_eval.py` (small) or the
    baseline (larger). Run on fuzz instances with `-cert`, with and without
    `-dl`. If the inherited partial-certificate behaviour under `-dl`
    (ARCH 10.4) produces invalid certificates, report it in `STATUS.md`
    with instances; the coordinator then decides between printing only
    assigned variables and completing the block by a final search under the
    partial assignment. Do not silently change the output format.
  - `tests/regressions/`: directory of small instances, run by `ctest`.
- **M1.9 Parity gate.** Full configuration matrix including the stress
  configurations, seeds 1:2000 (`release`) and 1:300 (`asan`), with the
  corpus histogram re-measured on the new solver; full-tier run sets of
  default and `-dl` against the baseline's from P0.4; quick-tier run sets of
  modes 1 and 2; proof coverage and overhead tables (0.3).
  **Port-fidelity report** (review 00, S6): search is not trace-identical, so
  "not worse" mixes engine speed with heuristic drift. Per instance solved
  by both with seed 0: propagations per second, conflicts per second, and
  the ratio of conflict counts (new / baseline); summarised as geometric
  means and as a histogram of the conflict ratio, per configuration. A
  faithful port has speed ratios at or above 1 and conflict ratios scattered
  around 1; a systematic shift of the conflict ratio means a behaviour from
  the porting notes was lost and is investigated before the gate is called.

### M1 execution plan (coordinator, supersedes the package order above)

The packages above say *what* is built; this table says in which order and
in which task. Ten tasks, one worker each, done strictly in order; each
leaves the tree building with all tests passing that exist at that point.

| task | content | packages | matrix configurations that must pass from here on |
|---|---|---|---|
| T01 | test tooling: two-tier corpus, `tests/matrix.txt`, coverage assertion and stress-timeout rule in `regress.sh`, `tests/fuzz_qdimacs.sh`, `tests/regressions/` | P0.1, part of M1.8 | (validated with the baseline and fake solvers) |
| T02 | build system, `.clang-format`, base layer, unit-test hook | M1.1 | unit tests |
| T03 | frontend: `circuit`, parsers, `encode`, `miniqu.hpp`, `tracer.hpp`; encoding compared with the baseline's `o` steps | M1.2 | unit tests, encoding diff |
| T04 | core data: `internal`, `prefix`, `constraint.cpp`, `assign`, `propagate` (templated loop, modes 0/1), `backtrack`, `solver.cpp` | M1.3 (a) | unit tests |
| T05 | mode-0 search: `decide`, `analyze`, `learn`, `bump`, `restart`, `model`, `certificate`, `app`, signals, limits; first end-to-end fuzz (no proofs yet) | M1.3 (b), `-cert` and limits of M1.7 | `default` (verdicts only), QDIMACS fuzz |
| T06 | proofs: `proof`, `qlrup_tracer`, `trace_tracer`, `checker`, all logging points | M1.4, `-trace` of M1.7 | `default` with Lean checking |
| T07 | `reduce` (old policy), arena garbage collection, stress options, header measurement | M1.3 (c) | + `gc`, `restart` |
| T08 | dependency learning; mode 1 and `--legacyanalyze` | M1.5, half of M1.6 | + `dl`, `mode1`, `mode1-dl`, `legacy`, their stress rows |
| T09 | mode 2; minimisation | half of M1.6, rest of M1.7 | full matrix |
| T10 | harness (seeds, paired statistics, coverage table), `tests/check_cert.py`, port-fidelity script, full-matrix parity fuzz, removal of `miniQU-old` from the root build | P0.2, rest of M1.8, tooling of M1.9 | full matrix, seeds 1:2000 / 1:300 |

Deviations from the package list, with reasons:

- **Proofs before reduction and garbage collection** (T06 before T07): the
  `gc` stress configuration then runs under the Lean checker from its first
  day, and deletion steps need no second visit (`mark_garbage` logs them).
- **M1.3 is three tasks**: it was far above the size a reviewer can read.
  T04 ends with a solver that answers only formulas decided at input; that
  is deliberate, the acceptance of T04 is unit tests.
- **P0.2 moved to T10**, P0.4 to the benchmark stage after T10 (nothing
  before the gate needs paired statistics; the header measurement of T07 is
  a direct per-instance comparison). **P0.3** (elimination yield) is planned
  with M3.
- `-cert`, CPU/memory limits and signal handling come with the app in T05
  instead of M1.7; `-trace` with the proofs in T06.
- The old solver stays in the root build as `miniQU-old` until T10 (owner:
  "removed from the build once parity is shown").
- `--arenaorder` is not added in M1 (single legal value; arrives in M2).
- In M1 the default-on `Checker` of debug/asan builds is not connected when
  `ccminmode > 0` (ARCH 8.1).
- Until a feature's task is done, the app rejects its option with
  "not implemented yet" (exit 1); each task removes its own rejections.

Matrix names (`tests/matrix.txt`): normal `default dl mode1 mode1-dl mode2
mode2-dl ccmin3 dl-ccmin3 noearly legacy`; stress `gc gc-dl gc-mode1
gc-mode2 restart restart-dl restart-mode1-dl`. Per-task acceptance uses
seeds 1:300 (`release`) and 1:100 (`asan`) on the rows listed above.

Acceptance of M1: no discrepancies; the coverage rule of 0.3 holds against
the baseline's table, with no rejected proof; at the full tier the new
solver is **not worse** than the baseline (definition in 0.3) in both main
configurations; modes 1 and 2 pass their quick-tier gate; peak memory not
higher than the baseline's on any instance by more than 10% (expected to be
much lower on large files; for instances where the baseline's peak RSS is
below 64 MB the rule is an absolute excess of at most 16 MB, since there the
allocator and the learnt-database trajectory dominate: coordinator decision
after M1 round 1); the port-fidelity report shows no unexplained
systematic shift; reviewer accepts structure and readability.

### M1 round 2 (rework after review M1-r1, coordinator)

Review M1-r1 accepted structure, soundness and proofs and blocked on engine
speed under benchmark load (B1). The cause was found by the coordinator
(STATUS.md, "M1 round 2: diagnosis of B1"): the 12-byte constraint header.
Two tasks, in order:

| task | content |
|---|---|
| R2-T1 | tooling and small clean-ups: `bench/load_measure.py` (identical-search CPU time of two binaries under benchmark load, arms separated), the identical-search section and the arm order in the paired report, regenerated M1-r1 reports; `struct Last` removed, `Solver::freeze` documented |
| R2-T2 | constraint layout of ARCH 5.2 (4-byte header, trailing glue word for redundant constraints, trailing id words only with a tracer), `copy_constraint`, creation-order tie-break in `reduce`, stress row `gc-ccmin3`; load measurement before/after; fuzz gate of the budget decision |

Round-2 gate (review M1-r1, B1 step 3): on the instances with equal conflict
counts in both arms (baseline CPU time above 1 s) the CPU-time ratio new /
baseline has a geometric mean of at most about 1.03 in default and `-dl`,
no family (three or more such instances) is above 1.10, and mode 1 is not
"worse" by the sign test. The benchmark stage reuses the same-machine
baseline runs `baseline-c96-<config>-t60-s<seed>` and states the order in
which the arms ran.

Porting notes (behaviour that is easy to lose; each has a test or assertion):

1. **Original constraints**: sort, remove duplicate literals, skip
   tautological clauses and contradictory cubes, log, `qreduce`, then store
   *without* simplifying under the current assignment (the old non-proof path
   did simplify; the new solver has one path, the proof one). Unit originals
   are assigned immediately; an empty or complementary-unit original decides
   the formula at input.
2. **Mode 0 conflict completion** (ARCH 4.7): the unassigned secondary
   literal of a conflict is assigned its vanishing value, without reason, on
   the current level, after the propagation loop.
3. **Variable comparisons are index comparisons** (INV-ORDER); the analyses
   rely on it everywhere.
4. **Analysis switches kind** in `analyze_qu` when it meets a reason of the
   other kind (the old `goto analyzeStart`): the reason of that variable is
   cleared and the analysis restarts from that reason. Port it as a loop.
5. **Root-level literals stay** in learnt constraints.
6. **Initial phase is false**; phase saving level 2.
7. **Old learnt-database policy** (M1 only): reduce when
   `#learnt - #assigned >= max_learnts`, `max_learnts` starts at a third of
   the number of original constraints and grows by 1.1 on the old geometric
   schedule; delete, per kind, the worse half of the constraints with glue
   > 2 that are not reasons, ordered by glue then size (the old tie-break by
   clause activity is replaced by size).
8. **Glue** = number of distinct decision levels among the assigned literals
   of the learnt constraint, computed before backjumping.
9. **Dependency reset** every 20th restart; a reset puts every variable back
   into the heap.
10. **Gate variables are never decided**; a block is complete when its
    *decision* variables are assigned.
11. **`-cert`** prints the outermost block that has decision variables, by
    QCIR identifier or QDIMACS number.
12. **Mode 2 watches** tolerate stale entries (ARCH 6.3).
13. Old out-of-bounds fixes (commit 2d57a9b) are in the baseline: read the
    old code at c39005a, not an earlier version.

---------------------------------------------------------------------------

## M2. Modern search

Each item is one package with an option, statistics and an ablation. Order =
priority. "Adopt" means it becomes default unless the ablation shows a loss;
"experiment" means it becomes default only if the ablation shows a gain.

### M2.1 Root-level simplification (adopt; prerequisite for M3)

`collect.cpp`, at decision level 0 after propagation, when new root
assignments exist. Three steps; (LO)/(HI) refer to ARCH 11.1.

1. **Materialise root units** (class D). A root assignment whose reason is a
   constraint `R` of kind `K` with more than one literal gets a stored unit
   constraint of kind `K` if every other literal of `R` already has a stored
   unit of kind `K`: one derived step, chain = `R`, then those unit ids; the
   unit replaces `R` as the reason. The result is passed through `qreduce`
   like every derived constraint: a unit on a secondary literal (possible in
   mode 1) reduces to the empty constraint and decides the formula. If some
   other literal of `R` has no unit of kind `K` (its root assignment comes
   from the other kind, or from such an `R` in turn), no unit is derived and
   the variable is "root-assigned without a unit". Units are flagged
   irredundant and are never deleted (ARCH 4.3).
2. **Remove root-vanished literals** (class D): a literal is removed from a
   constraint of kind `K` only if it has a stored unit of kind `K`
   (INV-DERIVED); otherwise it stays in the constraint forever, which is
   harmless. Proof: `strengthen` with chain = constraint id, unit ids. Then
   `qreduce`; unit and empty results are handled.
3. **Delete root-disabled constraints** (class R): a constraint with a
   disabling root literal is deleted if that literal has a stored unit **of
   either kind**; a constraint disabled by a literal without a unit stays
   (it is never visited again: its blocker is true).

Soundness:

- QCIR: steps 1 and 2 are derivations. Step 3 cannot affect INV-COMPLETE,
  because root assignments are never undone: a root-disabled constraint can
  neither propagate nor conflict again. (For QCIR alone the unit condition of
  step 3 is not needed; one rule for both input formats is worth more than
  the few constraints it keeps.)
- QDIMACS: step 1 with a clause unit promotes nothing that was not derived;
  storing it as irredundant is the "promote" row of the table in ARCH 11.1.
  Step 2 on an irredundant clause is the "replace `C` by `C' ⊂ C`" row; note
  that the unit may be a *learnt* consequence, which is why the argument goes
  through (LO)/(HI) and not through propositional equivalence. Step 3 is one
  of the two deletion rows: under an irredundant unit clause the clause set
  stays equivalent; under a stored unit cube `(u)` the clause contains `¬u`
  and `G ∨ ⋁T` stays equivalent. Initial cubes hit the remaining irredundant
  clauses *including the unit clauses*, so root literals appear in them
  unless reduced (rule 4 in ARCH 11.1). In mode 2, step 3 under a unit cube
  is skipped for QDIMACS input (end of ARCH 11.1).

Any throttle (minimum number of new units, propagation budget as in
MiniSat's `simpDB_props`) is an option whose range includes "none", for the
`root` stress configuration (0.1).

### M2.2 Tiers, `used` counters, glue-based reduction (adopt; owner requirement)

- Glue is stored in the header; `used` (2 bits) is set when a redundant
  constraint is a reason or conflict in analysis: `used = 1`, or `2` if its
  glue is within tier 2. At that moment the glue is recomputed from the
  current levels and lowered if smaller (promotion).
- Tiers per kind (clauses and cubes have very different glue distributions;
  cubes from satisfying assignments are long): tier 1 `glue <= tier1glue`
  (default 2), tier 2 `glue <= tier2glue` (default 6), tier 3 the rest.
- `reduce ()` every `reduceint * (reductions + 1)` conflicts (the M1 stress
  option becomes the schedule; the old size-based trigger is removed unless
  the ablation says otherwise; `tier1glue` and `tier2glue` accept 0): protect
  reasons; per kind: decrement `used`; keep tier 1 always; keep tier 2 if
  used in the last two intervals; keep tier 3 if used in the last interval;
  of the remaining candidates delete the `reducetarget`% (default 75) worst
  by (glue, size). Deletions go through `mark_garbage` (proof `d`); then
  garbage collection if due.
- Second step, separate ablation: dynamic tier limits from the usage
  histogram per kind (CaDiCaL `recompute_tier`).
- QBF notes: a constraint is redundant-and-deletable regardless of kind;
  deleting learnt constraints never affects soundness or INV-COMPLETE.
  Experiment inside this package: glue counting only *primary* literals'
  levels versus all literals (`--gluemode`).

### M2.3 Proof-producing minimisation (adopt if the ablation agrees)

The old solver learns unminimised constraints by default and cannot minimise
at all when writing proofs. Extend the chain: after minimisation, append the
reason ids of the removed literals in reverse trail order (as CaDiCaL does for
LRAT). In modes 0 and 1 every literal of a reason is assigned and vanished,
so no intermediate resolvent is tautological, and the secondary literals that
`ccminmode=3` introduces are exactly those removed by the final reduction,
which is where the checker reduces. Then `ccminmode` no longer depends on
tracing, the matrix tests it with proofs, and the default is chosen by
benchmark (candidates 0, 2, 3). Also in this package: resolve away root-level
literals that have a stored unit of the same kind (M2.1; unit ids appended to
the chain).
Mode 2 keeps the old behaviour.

### M2.4 EMA restarts (experiment)

Glucose/CaDiCaL-style: restart when `fast > (1 + margin) * slow` of the glue
averages and at least `restartint` conflicts passed. QBF adaptation: separate
fast/slow averages per kind, tested for the kind of the last learnt
constraint, because cube and clause glues are not comparable. Luby stays
available (`--restartmode`). The dependency reset is decoupled from the
restart count (every `depresetint` conflicts), otherwise frequent restarts
would wipe dependencies constantly; tune it in the `-dl` ablation.

### M2.5 Trail reuse (adopt)

On restart keep the decision levels that would be re-decided anyway: the
longest prefix of levels whose decision variable has a score at least that of
the best unassigned candidate of its own block (prefix order) or of the single
heap (`-dl`). Only changes the backtrack level of a restart; no soundness
content. Cheap win when restarts are frequent, so it follows M2.4.

### M2.6 Stable/focused mode switching (experiment, after M2.4)

Alternate, on a geometric tick schedule, between focused phases (EMA
restarts) and stable phases (Luby/reluctant-doubling restarts, slower score
decay). Both phases use EVSIDS on the existing per-block heaps at first. A
VMTF queue per block for the focused phase is a follow-up experiment only if
mode switching itself pays off: in prefix-order QCDCL the choice is confined
to the current block, which limits what a different variable order can
change, and one queue per block is real extra machinery.

### M2.7 Rephasing (experiment, low priority)

Original / inverted / best phases on the CaDiCaL schedule. "Best" = phases at
the longest conflict-free trail since the last rephase. There is no evidence
either way for QCDCL (the phase of a universal variable is the opponent's
move); it is cheap to try and cheap to drop.

### M2.8 Arena order by decision order (experiment)

`--arenaorder=1` (ARCH 5.3): relocation walks variables by descending score
and saved phase first. Measured by propagations per second on the quick tier
(seed 0, instances solved by both arms), in addition to the protocol of 0.3.

### M2.9 Reason-side bumping (experiment, low priority)

Bump the literals of the reasons of learnt literals (bounded depth), as in
CaDiCaL/Maple.

### Decided against for M2

- **Chronological backtracking.** The Q-analysis is one backward pass over
  the trail that relies on levels being monotone along the trail and on
  "blocked = assigned on the pivot's level or later"; dependency learning
  backtracks to "just below the offending decision". Out-of-order trails
  would force all three analyses and the eligibility logic to be re-derived
  for a gain that, in SAT, shows mainly on instances with very long trails.
  Revisit only with evidence from profiles.
- **Shrinking** (replacing the literals of a level by a dominator). The
  replacement literal is a new primary literal; whether the result is still
  asserting depends on its position relative to every blocked secondary
  literal, and it may prevent reductions that the unshrunk constraint allows.
  Needs its own theory; listed under M5.
- **Lucky phases, local search, warmup**: SAT-specific.

Acceptance of M2: every item has its ablation by the protocol of 0.3 (adopt
items: not worse at the quick tier; experiment items that became default:
better at the quick tier and again at the full tier); the combined default
is **better** than M1 at the full tier in at least one main configuration
and **not worse** in the other; modes 1 and 2 pass their quick-tier gate;
the matrix with all M2 stress configurations passes with its coverage
assertion and with minimisation proofs (seeds 1:2000); proof coverage shows
no unexplained drop against M1, and the proof-overhead table is reported.

---------------------------------------------------------------------------

## M3. Inprocessing framework and bounded variable elimination

### M3.0 Measure the yield first (P0.3; review 00, S1)

Which variables elimination may touch at the start is a static property of
the encoding: for QCIR, E2 leaves gate variables only and E3 leaves the gate
variables all of whose consumers are placed in the same block. `bench/
elim_yield.py` computes, for all 376 benchmarks and **both** gate placements
(`--earlytseitin` and without), per kind: gate variables; those satisfying
E3 initially; those that become eligible when eligible consumers are
eliminated first (fixpoint, ignoring the bound E4); and the same counts under
the relaxed condition of M5 item 3. Output: a per-family table in
`STATUS.md` and the CSV under `bench/results/elim-yield/`.

Decision point, **before M3.2 is started**: the coordinator shows the owner
the table together with this fact: for QCIR input, E3 is not needed for
soundness. The verdict rests on INV-DERIVED (resolvents are derivations
wherever the pivot sits), and the INV-COMPLETE argument in M3.3 does not use
E3. E3 is needed for QDIMACS input (M3.2) and is otherwise a restriction
imposed by the owner's requirement. If the yield under `--earlytseitin` is
small, the question about M5 item 3 is asked then, not after M3 has been
built and benchmarked.

### M3.1 Framework

`inprocess.cpp`, `flags.hpp`, `occs`, occurrence mode, budgets, `preprocess`
(ARCH 10.1-10.3); `check_invariants ()` after every pass; backward
subsumption and strengthening for use by elimination (`subsume.cpp`, class D:
a subsumed constraint is deleted; if `D ∨ l` and `C ∨ ¬l` with `D ⊆ C` then
`C ∨ ¬l` is replaced by `C`, one resolution step; pivot of either quantifier,
which is QU-resolution and accepted by the checker in every mode; `qreduce`
afterwards).

Redundant and irredundant constraints (ARCH 11.1, rules 1 and 2):

- an irredundant constraint **may be strengthened** by a redundant one. QCIR:
  it is a derivation, and propagation only gets stronger (INV-COMPLETE).
  QDIMACS: the "replace `C` by `C' ⊂ C`" row;
- an irredundant constraint may be **subsumed away** only by an irredundant
  one; if the subsuming constraint is redundant it is made irredundant first
  (QCIR: otherwise a later `reduce` could delete it and weaken propagation,
  breaking INV-COMPLETE; QDIMACS: the "promote" row, then an equivalent
  deletion).

### M3.2 Elimination: definition and side conditions

Let `x` be a variable, `K` the kind for which `x` is primary (clauses for an
existential `x`: *clause distribution*; cubes for a universal `x`: *cube
distribution*), and `K'` the other kind. `x` is eliminated by replacing all
irredundant `K`-constraints containing `x` or `¬x` by their pairwise
resolvents on `x`. Conditions, all checked at the moment of elimination, at
decision level 0, after propagation and root simplification:

- **E1 (status)** `x` is `Active`, unassigned, not frozen.
- **E2 (other kind)** `x` occurs in no live `K'`-constraint, original or
  learnt. (An existential variable must not occur in any cube; a universal
  variable must not occur in any clause.) Option `--elimdropother=<n>`
  (default 0 = strict) allows deleting up to `n` *learnt* `K'`-constraints
  containing `x` to make the condition true; an irredundant occurrence always
  blocks.
- **E3 (rightmost)** in every irredundant `K`-constraint containing `x` or
  `¬x`, no other variable has greater quantifier depth than `x`. Variables of
  the same block as `x` are allowed (a block is unordered; the internal index
  order inside a block has no meaning here). So the test is on depth, not on
  variable index.
- **E4 (bound)** the number of resolvents kept (non-tautological, after
  `qreduce`) is at most the number of removed constraints plus `elimbound`
  (0, then 1, 2, 4, 8, 16 as rounds complete, as in CaDiCaL), subject to
  occurrence and resolvent-size limits.

Procedure: delete all *learnt* `K`-constraints containing `x`; compute the
resolvents; drop tautological ones (complementary literals of any variable,
either quantifier); `qreduce` each; an empty resolvent decides the formula
(empty clause: false; empty cube: true), a unit resolvent becomes a root
unit; add the others as irredundant; delete the parents; mark `x`
`Eliminated` (heaps, block counter, dependencies; ARCH 10.3); schedule the
variables of the resolvents; backward-subsume with the resolvents.

**Where the conditions are needed.** For QCIR input the verdict never
depends on them (ARCH 11.1; M3.3 shows INV-COMPLETE without E3); there E2 is
what keeps stored constraints meaningful and E3 is the owner's requirement.
For QDIMACS input (existential `x`, clause distribution; modes 0 and 1) they
are exactly what the admissibility criterion of ARCH 11.1 needs. Notation as
there: `G` irredundant clauses, `G_x ⊆ G` those containing `x` or `¬x`, `L`
learnt clauses, `T` stored cubes, `Π' = Π` without `x`, `R` the
non-tautological resolvents on `x` before `qreduce`, and after the step
`G' = (G \ G_x) ∪ qreduce (R)`, `L'` = the learnt clauses without `x`,
`T' = T`.

*(LO): if `Π.(G ∧ ⋀L)` is true, so is `Π'.(G' ∧ ⋀L')`.* Moving `∃x` to the
innermost position cannot make a true formula false, so `Π'.∃x.(G ∧ ⋀L)` is
true. Propositionally `∃x.(G ∧ ⋀L)` implies `(G \ G_x) ∧ R ∧ ⋀L'`
(resolvents are consequences, F2; the rest does not mention `x`). Reducing
the resolvents keeps the value by F3, which holds in any conjunction. This
direction uses neither E2 nor E3, and learnt clauses need not satisfy E3.

*(HI): if `Π'.(G' ∨ ⋁T)` is true, so is `Π.(G ∨ ⋁T)`.* First, `G' ⊨ (G \
G_x) ∧ R` (reduction only strengthens), and `(G \ G_x) ∧ R ≡ ∃x.G`
propositionally (the non-tautological resolvents are exactly `∃x.G_x`;
this is also why resolvents that are tautological on a *universal* variable
may be dropped although Q-resolution could not derive them). By E2 no cube
contains `x`, so `(∃x.G) ∨ ⋁T ≡ ∃x.(G ∨ ⋁T)`. Hence by F1 the formula
`Π'.∃x.(G ∨ ⋁T)`, with `x` quantified innermost, is true. It remains to
move `∃x` back to its block. Fix a winning existential strategy of the
innermost game; let it play all variables other than `x` as before. For `x`,
which may be played last in its own block: let `β` be the play up to and
including `x`'s block. By E3 all variables of `G_x` have been played, so
`G_x|β` is a formula over `x` alone; play a value satisfying it if there is
one, any value otherwise. Take a complete play `α` extending `β`. In the
innermost game some value `c` of `x` makes `G ∨ ⋁T` true at `α`. If a cube
of `T` is true at `α`, the matrix is true whatever `x` is (E2). Otherwise
`G (α, c)` holds, so `G \ G_x` holds at `α` and `G_x|β` is satisfiable, so
the value we played satisfies `G_x` too, and `G` holds. So the strategy wins
`Π.(G ∨ ⋁T)`.

The last step is where both conditions enter: E2 lets the stored cubes ride
along unchanged (they need not be implicants of anything, see ARCH 11.1), and
E3 on the irredundant clauses makes the value of `x` computable when `x` is
played. Without E3 the step fails: for `∃e ∀u ∃f` with clauses
`(e ∨ f ∨ u) (e ∨ ¬f ∨ u) (¬e ∨ f ∨ ¬u) (¬e ∨ ¬f ∨ ¬u)` the formula is
false, but all resolvents on `e` are tautological.

Universal elimination has no QDIMACS case: cube distribution works on
irredundant cubes, and QDIMACS input has none. In mode 2 elimination is not
applied to QDIMACS input (ARCH 11.1).

Why E2 also matters operationally: a cube containing `x` would refer to a
variable that is never assigned again, so it could never fire, and removing
the literal from the cube is not a cube derivation.

### M3.3 Interactions (each one is a test target)

- **Dual encoding of QCIR.** Input variables occur in clauses and cubes, so
  E2 excludes them all: in QCIR runs, elimination removes *gate* variables
  only, existential gate variables from the clause side by clause
  distribution and universal gate variables from the cube side by cube
  distribution, independently. E3 then says: a gate variable can go when every
  gate that uses it as an input (and has not itself been eliminated) is
  placed in the same block. With `--earlytseitin` this blocks a gate that
  feeds a gate depending on deeper variables; eliminating the consumers first
  can unblock it only if the resolvents no longer mix the gate with deeper
  variables. Expect elimination to flatten same-depth gate cones and to be
  blocked at depth boundaries. Without early placement all gate variables of
  a kind share one innermost block and E3 always holds, but reduction is
  weaker; the ablation must cover both placements. M3.0 puts numbers on
  this before anything is built. (Relaxing E3 with a dependency argument is
  M5 item 3 and needs the owner's approval.)
- **INV-COMPLETE (QCIR).** Elimination preserves it: a unit-propagation
  refutation under a total input assignment that propagates `x` from
  `C ∨ x` and uses it in `¬x ∨ D` is simulated by the resolvent `C ∨ D`
  (if the resolvent is tautological, `D` contained a true literal and was not
  usable), `qreduce` and subsumption only strengthen, and E4 guarantees all
  resolvents are present. So after elimination, as before, a full assignment
  of the inputs produces a conflict in one of the two databases. The argument
  does not use E3.
- **Learnt constraints.** Learnt `K`-constraints with `x` are deleted (they
  need not satisfy E3). Learnt `K`-constraints without `x` stay; for QCIR
  they are derivations as before, for QDIMACS they are the `L'` of the (LO)
  argument in M3.2. Learnt `K'`-constraints: E2.
- **Initial cubes / model generation (QDIMACS).** After elimination
  `model.cpp` hits the current irredundant clauses, which include the
  resolvents: the new cube is an implicant of `G'`, which is all that the
  "initial cube" row of ARCH 11.1 asks. Old cubes are kept by E2 and are
  covered by the (HI) argument; nothing claims they are implicants of `G'`.
- **Certificates.** For QCIR nothing is to do (the certificate block
  consists of inputs). For QDIMACS: extension stack, ARCH 10.4, in M3.6.
- **Dependency learning.** Reset dependencies when a decision variable is
  eliminated.
- **Mode 2.** QCIR: only irredundant constraints are resolved, and they
  contain no complementary literals; allowed. QDIMACS: not applied.
- **Trail and reasons.** Root level only; a reason of a root assignment
  consists of assigned literals only and never contains `x`.
- **Root-disabled constraints without a unit** (M2.1 step 3 keeps them) may
  contain the unassigned `x`. They are ordinary members of the irredundant
  database for E2, E3, E4 and for resolution; their resolvents inherit the
  root-true literal and are kept in the same way. Treating them as deleted
  would be a weakening of `G` that ARCH 11.1 does not cover.

### M3.4 Proof logging

Elimination is class (D)+(R) and is **fully expressible in QLRUP as it is**:

- each resolvent is one derived step with the two parent ids as chain; the
  checker resolves on the single clashing literal `x` and reduces, which is
  exactly `qreduce` of the resolvent (tautological resolvents have a second
  clash and are never emitted);
- parents and learnt constraints with `x` are deleted with `d`;
- an empty resolvent is the final step of the proof.

No rule for "removing a variable" is needed, because QLRUP proofs are
derivations of the empty constraint and never have to justify that deleting
something preserves truth. For a **false** formula the refutation simply
continues from the resolvents. For a **true** formula the clause-side
elimination steps appear in the proof and are irrelevant to the cube
derivation that proves truth; cube-side elimination steps are ordinary cube
resolutions. Both directions therefore need nothing new.

What is *not* covered by proofs, honestly:

- QDIMACS input has no proofs at all (initial cubes from models are not
  derivable; this is unchanged from the baseline). Everything specific to
  QDIMACS elimination, namely E2 against learnt cubes, the (HI) argument of
  M3.2, model generation on resolvents, and the extension stack, would be
  validated only by fuzzing and by the run-time check of initial cubes
  (ARCH 4.5). No benchmark exercises it either: all 376 instances are QCIR.
  This is why QDIMACS elimination is a separate, optional package that is
  **off by default** (M3.6), and why M5 item 6 is the better way to close
  the gap.
- The proof shows that the verdict is right; it does not show that E2/E3
  were respected. For QCIR input a violated side condition cannot produce a
  wrong verdict, because both databases still contain only derivable
  constraints (resolvents are sound whatever the position of the pivot); at
  worst it breaks INV-COMPLETE and shows up as a **stuck state**
  (`stats.modelcubes > 0`; the run ends with "unknown", ARCH 4.5). Hence:
  debug builds re-verify E2/E3 for every eliminated variable in
  `check_invariants ()`.
- Mode 2 has no proofs.

### M3.5 Work packages

0. Yield measurement and the owner's answer (M3.0).
1. Framework and subsumption (M3.1), with elimination switched off.
2. Clause distribution for QCIR gate variables, preprocessing only, proofs
   on. Matrix + Lean.
3. Cube distribution (the same code through the kind template; verify that
   no clause-specific assumption crept in).
4. Inprocessing rounds (after search has started: learnt constraints exist,
   bounds increase), dependency reset.
5. Gate-aware elimination (optional): the encoder marks definition
   constraints (`gate` bit); when the complete definition of `x` (both
   implication directions) is present, only definition x non-definition
   resolvents are added. Same proof steps. Plaisted-Greenbaum gates of one
   polarity have no complete definition and take the plain path.

For QDIMACS input `--elim` does nothing in packages 1-5 (subsumption and
strengthening do run, under the rules of M3.1); the QDIMACS fuzz of the M3
gate checks that this is so and that nothing else broke.

Acceptance of M3: matrix extended by `--elim` on/off, `--no-earlytseitin`
with elimination, and the `elim` stress configuration (0.1), with the
coverage assertion on `eliminated.clause`, `eliminated.cube`, `resolvents`
and `inprocessings`; seeds 1:3000 QCIR with Lean checking, 1:3000 QDIMACS;
`stats.modelcubes == 0` on every QCIR benchmark run; the proof coverage and
overhead tables of 0.3; ablation by the protocol of 0.3 in both main
configurations with per-family analysis of where elimination applies (number
of eliminated variables, blocked by E2/E3/E4 each).

### M3.6 Elimination for QDIMACS input (optional, after the M3 gate)

Only on the coordinator's go-ahead, which needs either the owner's interest
in QDIMACS preprocessing or M5 item 6 having been decided against. Option
`--elimqdimacs` (default 0). Contents: E2 bookkeeping against learnt cubes;
the mode-2 exclusion; the extension stack with clause entries only and the
`--cert` freeze until `tests/check_cert.py` validates it (ARCH 10.3, 10.4);
`check_model_cube ()` on in every fuzz run. Gate: 1:10000 QDIMACS seeds on
both tiers against the baseline, the brute-force evaluator and the QCIR
conversion of the same instance, in all three modes, with the `elim` stress
configuration and its coverage assertion. It stays off by default afterwards
unless a benchmark argues otherwise.

---------------------------------------------------------------------------

## M4. Vivification of clauses and cubes

Class (D). For a candidate constraint `C` of kind `K`: at level 0, decide the
*vanishing* value of its literals one by one (for a clause: the literal
false; for a cube: the literal true), propagating after each, and use what
propagation reveals to derive a shorter constraint that subsumes `C`.

QBF side conditions:

- **V1 (one kind only)** during vivification only `K`-constraints propagate
  (`propagate_kind`). An assignment forced by a constraint of the other kind
  is not a consequence in `K`'s calculus, and using it would be unsound, not
  just unprovable. The trail head of the other kind is restored on backtrack
  (ARCH 7.2); units learnt by vivification are propagated for both kinds
  afterwards.
- **V2 (no reduction during propagation)** propagation follows the mode-0/1
  rule: a constraint with a single non-vanished literal forces it if it is
  primary (mode 1: also if secondary). The mode-0 "single remaining secondary
  literal is a conflict" rule is switched off here: such a constraint is
  simply left alone, because the conflict it stands for needs a reduction
  that is only valid in context.
- **V3 (decisions may be of either quantifier and in any order)** the
  decided literals are exactly literals of `C`, so every derived constraint
  consists of literals of `C`.
- **V4 (derivation)** on a conflict, or when a literal of `C` becomes
  disabling, or when literals of `C` were found vanished: resolve the
  conflict/reason backwards along the trail until only decisions remain
  (CaDiCaL's decision-only analysis). Every pivot has a `K`-reason whose other
  literals are all vanished, so no resolvent is tautological and each step
  is a plain resolution step. The result `D` is a subset of `C`, except for
  literals fixed at root by a reason of the other kind, which cannot be
  resolved away (INV-DERIVED; precisely: root literals without a stored unit
  of kind `K`, M2.1): if any such literal is not already in `C`, the
  candidate is skipped.
- **V5** `qreduce (D)`; if `D` is a proper subset of `C`, replace `C` by `D`
  (irredundant stays irredundant; a learnt `C` gets its glue recomputed and
  may be promoted); empty `D` decides the formula; unit `D` is a root unit.
- **V6** mode 2 is excluded at first (its watch invariant differs); modes 0
  and 1 only.

Soundness for QDIMACS input: `D` is one QLRUP step over stored clauses of
`G ∪ L` and `D ⊂ C`, so replacing an irredundant `C` by `D` is the "replace
`C` by `C' ⊂ C`" row of ARCH 11.1, whether the reasons used were irredundant
or learnt (rule 1 there). Vivified cubes are covered by the cube row. V1 is
what makes the step a derivation in the first place; with it, vivification
needs no further QBF condition.

Proof: `strengthen (C, D, chain)` with chain = the conflict or reason id,
then the reason ids in reverse trail order; if `C` itself takes part (the
"all other literals vanished" case) its id leads the chain. One derived step
plus one deletion; nothing new for the checker.

Scheduling as in CaDiCaL: separate effort shares for learnt tier 2, tier 1,
tier 3 and irredundant constraints, for both kinds; candidates sorted so that
constraints sharing literal prefixes are tried consecutively and decisions
are reused; literals within a candidate ordered by occurrence count; a
`vivified` bit avoids retrying unchanged constraints.

Work packages: (1) `propagate_kind` and decision-only analysis with unit
tests; (2) learnt clauses, tier 2; (3) cubes, remaining tiers, irredundant;
(4) scheduling/effort tuning and ablation.

Acceptance: matrix with `--vivify` on/off and the `vivify` stress
configuration with its coverage assertion; Lean-checked seeds 1:3000; QDIMACS
fuzz (with `check_model_cube ()`); ablation by the protocol of 0.3 in both
main configurations, with counts of candidates, strengthened constraints and
removed literals per kind and tier; proof coverage and overhead tables.

---------------------------------------------------------------------------

## M5+. Further techniques, in priority order

Priority weighs expected impact on this benchmark set (QCIR, dual encoding)
against risk. "Proof" says what QLRUP can express today.

| # | technique | class | QBF side conditions | proof | expected impact |
|---|---|---|---|---|---|
| 1 | **Forward/backward subsumption and strengthening of learnt constraints** during inprocessing (beyond the BVE helper of M3.1) | D | same kind only; `qreduce` after strengthening; irredundant subsumed only by irredundant | deletion; one resolution step | medium; cheap; keeps the learnt databases small, helps both kinds |
| 2 | **Failed-literal probing** | D | per kind with V1/V2 of M4: probe a primary literal's vanishing value at level 1, a conflict yields a unit by decision-only analysis; a probe never uses the other kind | derived unit with chain | medium on the clause side of deep circuits; shares all code with vivification |
| 3 | **Relaxed rightmost condition for elimination** (dependency-based: allow deeper variables in `x`'s constraints if they provably do not depend on `x`, e.g. gate variables whose cone does not contain `x`'s consumers) | D+R | needs a written soundness argument per dependency notion, and the **owner's approval**, since it relaxes an explicit requirement | unchanged (resolvents, deletions) | potentially high for QCIR: E3 is what blocks most gates with early placement |
| 4 | **Equivalent-literal substitution** (SCCs of the binary implication graph) | D+R | per kind, over primary variables of that kind that satisfy E2; representative = leftmost variable of the class; a class containing `x` and `¬x` decides the formula; substituted variables need the rightmost condition E3 like elimination, since their defining binaries are removed | rewritten constraints are resolvents with the binaries; removal is deletion | low-medium (xor/ite expansions create equivalences among gate variables) |
| 5 | **Blocked constraint elimination (QBCE)** and the cube dual | R | blocking literal primary, every resolvent on it tautological on a variable not to the right of it; E2 for the blocking variable. QCIR: does **not** preserve INV-COMPLETE in general (propagation gets weaker), so it is only admissible there together with a sound fallback for the stuck state, which does not exist (ARCH 4.5). QDIMACS: weakens `G`, so it needs its own (HI) argument (ARCH 11.1) in the presence of stored cubes, with E2 for the blocking variable; extension stack entry | deletion only | medium for QDIMACS input, doubtful for PG-encoded QCIR (elimination already removes what QBCE would) |
| 6 | **QDIMACS through the dual encoding** (treat the CNF as `and` of `or` gates, so cubes come from the cube encoding instead of from models) | - | none; a different front end for the same engine | makes QDIMACS proofs possible with the unchanged checker (needs QCIR text of the formula for the checker: `qdimacs2qcir`) | closes the QDIMACS proof gap of M3; search behaviour changes, so benchmark before making it default |
| 7 | **Pure literals** | R | a primary variable occurring in one polarity only in its kind and satisfying E2: its constraints are deleted. Never as an assignment that is later used as a premise | deletion only | low (mostly cleans up after elimination) |
| 8 | **Binary-constraint fast path** (blocker-only propagation for size-2 constraints, tag bit in the watch) | engine | none | none | medium on propagation speed: most original constraints of a Tseitin encoding are binary. Keeps the 8-byte watch and the arena; needs care with GC ordering |
| 9 | **VMTF per block**, **shrinking**, **chronological backtracking** | engine | see "decided against" in M2 | chain construction must be redone for shrinking | unknown; only with profile evidence |
| 10 | **Universal expansion** of innermost universal variables | N | copies the inner existential variables; changes the prefix | **not expressible**: needs new variables and a new rule in the checker, with Lean proofs; coordinator decision required; disabled under proofs until then | high on some families (it is what expansion solvers do), but it is a different solver architecture; last |
| 11 | **Long-distance proofs** (mode 2) | N for the checker | merged literals | **not expressible**: needs a checker extension | low priority; mode 2 is not a main configuration |

Techniques considered and not planned: bounded variable addition and
definition introduction (new variables: class N), covered/asymmetric clause
elimination (weak propagation: INV-COMPLETE), transitive reduction and hyper
binary resolution (marginal without a binary-implication-heavy core),
conditioning/globally blocked clauses, sweeping/congruence closure (would
need an incremental SAT kernel).

One frontend idea is independent of all of the above and can be scheduled any
time after M1: **structural hashing** of the circuit before encoding (merging
gates with the same type and inputs). The solver would see fewer gate
variables. The proof format refers to original gate numbers and both
variables of a merged gate would have to be represented by one proof number,
so the encoder must emit every constraint under the number of one surviving
original gate and never use the merged-away gate's number; whether that is
enough for the checker's `o` rule has to be worked out before it is
scheduled.

---------------------------------------------------------------------------

## Summary: what QLRUP can express today

| technique | false formulas | true formulas | note |
|---|---|---|---|
| learning, modes 0/1, with or without `-dl` | yes | yes | baseline |
| minimisation (M2.3) | yes | yes | chain extended by the reasons of removed literals |
| root simplification (M2.1) | yes | yes | only same-kind units are resolved away |
| database reduction, tiers | yes | yes | deletions |
| BVE, clause and cube distribution (M3) | yes | yes | resolvents + deletions; no new rule |
| subsumption, strengthening | yes | yes | |
| vivification (M4) | yes | yes | kind-restricted propagation |
| failed literals, equivalent literals | yes | yes | |
| QBCE, pure literals | yes (deletions) | yes (deletions) | proof is fine, *completeness* of the solver is the issue for QCIR |
| initial cubes from models (QDIMACS) | n/a | **no** | no QDIMACS proofs; M5 item 6 |
| mode 2 (long-distance) | **no** | **no** | checker extension needed |
| universal expansion, new variables | **no** | **no** | checker extension needed |

No checker or format extension is required for M1-M4.
