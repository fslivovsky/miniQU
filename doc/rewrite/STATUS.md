
## Infrastructure (worker, 2026-11-21)

Done:
- Branch `rewrite/cadical-style` (from c39005a). Frozen baseline: worktree
  `/home/ec2-user/miniqu-work/baseline-src`, release binary
  `/home/ec2-user/miniqu-work/baseline/miniQU` (hash in `baseline/GIT_HASH`). Never rebuild from changed sources.
- Lean checker built: `/home/ec2-user/qu-check/.lake/build/bin/qlrup-check [--stats] FORMULA.qcir PROOF`;
  verified on baseline proofs (all 33 smoke proofs accepted).
- `bench/run.py`, `bench/compare.py`, `bench/smoke.txt` (+ `smoke-expected.csv`), `bench/README.md` (usage,
  rebuild instructions for /home/ec2-user/miniqu-work). Baseline results: `bench/results/baseline-smoke`
  (proof-checked) and `bench/results/baseline-t5` (all 376 instances, 5 s timeout; NOT a full baseline run).
- `tests/regress.sh SOLVER [-- OPTS ...]`: fuzz vs brute-force evaluator and vs baseline, Lean proof check of
  every fuzz instance, smoke set with proof check; exit 1 on any disagreement/rejected proof. `tests/fuzz.sh`
  extended (PROOF_CHECKER, reproducing commands, KEEP_DIR). Validated on the baseline
  (`-s 1:16 ... -- -no-luby`: 0 failures, 250 proofs accepted, 16 solver timeouts and 6 checker timeouts as
  warnings) and with a fake always-SAT solver (detected, exit 1).

Known issues / notes:
- Fuzz proof checks with a 120 s checker limit time out for a few larger instances (proofs of ~400 MB from
  baseline); these are warnings, not failures.
- Options starting with `-` passed to run.py must use `--args=...` / `--proof-args=...` form.
- A full-timeout baseline run of all 376 instances has not been made yet (only 5 s); the coordinator should
  schedule it on cores 64-127 before comparing performance.
- Do not use `pkill -f` with patterns matching your own command line when managing runs.

## Architecture and roadmap (coordinator, 2026-11-21)

Done: `doc/rewrite/ARCHITECTURE.md` (target design of `src/`) and `doc/rewrite/ROADMAP.md` (M1-M5+, gates,
benchmark protocol). No solver code yet. Workers: read both before starting; M1 work packages are M1.1-M1.9
in ROADMAP, to be done in order (M1.8 is independent after M1.2).

Decisions (the reasons are in the two documents):

1. Structure: CaDiCaL-like `struct Internal` + one translation unit per technique, thin `External`, public
   `Solver` (pimpl), frontend (`circuit`, parsers, `encode`) on top of the public API only. Namespace
   `miniqu`, C++20 as supported by GCC 11.5/Clang 15 (no `std::format`), warnings as errors, presets
   release/debug/asan/log with build trees in `/home/ec2-user/miniqu-work/build/<preset>`. `minisat/` is
   frozen and no longer built by the root CMake project.
2. Kept from MiniSat/miniQU (owner requirement): region arena with 32-bit refs and copying GC that relocates
   constraints in watch-list order; 8-byte watches (ref + blocker), separate lists per kind, lazy cleaning.
   New: 16-byte constraint header with inline 64-bit id (replaces the CRef->id hash map), glue and flag bits;
   no per-clause activity.
3. Clauses and cubes are one `Constraint` type distinguished by `Kind`; kind-generic code via the "kind
   value" of a literal. The code says "cube" (proof format keeps `t`), and "reduce" means database
   reduction; universal/existential reduction is `qreduce`.
4. Internal variables are numbered in prefix order (INV-ORDER); blocks are contiguous ranges; no variables
   are created after the formula is added.
5. Invariant INV-DERIVED: every stored constraint has a one-step QLRUP derivation from stored constraints of
   the same kind, whether or not a proof is written (exceptions: model cubes for QDIMACS, mode 2). Hence one
   code path for original constraints (the old "proof" path), and root-vanished literals are only removed
   when the unit has the same kind.
6. Invariant INV-COMPLETE (QCIR): with all inputs assigned one of the two databases conflicts. Reaching the
   model-cube fallback on QCIR input is counted (`stats.modelcubes`), fatal with proofs, and a bug.
7. Proofs: `Proof` dispatcher + `Tracer` observers (QLRUP writer, old `-trace` writer, internal `Checker`
   that replays derived steps; on by default in debug/asan builds). `mark_garbage` is the only source of
   deletion steps.
8. Options: all integer, one X-macro table; CLI accepts `--name[=v]`, `--no-name`, and the legacy
   single-dash/hyphenated spellings, so existing scripts (`-verb=0 -proof=F -proof-binary -dl -mode=1`) keep
   working. Dropped: `rnd-freq`, `rnd-init`, `cla-decay`, user polarities, assumptions, SimpSolver, toDimacs.
9. M1 is a port with the old heuristics (Luby, EVSIDS heaps per block, old learnt-size schedule, glue>2
   halving); gate = equal verdicts, all proofs accepted, performance within the noise band of the baseline.
   Not bit-identical search.
10. M2 adopt: root simplification, glue tiers + `used` + reduce (per kind), proof-producing minimisation,
    trail reuse. Experiment (default only on measured gain): EMA restarts with per-kind averages,
    stable/focused switching, rephasing, arena order by decision order, reason-side bumping.
    Rejected for now: chronological backtracking, shrinking, lucky/local search (reasons in ROADMAP M2).
11. BVE (M3): conditions E1-E4. Eliminated variable must be rightmost by *quantifier depth* (same-block
    variables allowed) in every irredundant constraint of its kind, and must not occur in any live
    constraint of the other kind (strict by default; `--elimdropother` may delete learnt ones). For QCIR this
    means only gate variables are eliminated. Fully expressible in QLRUP today (resolvent = one derived step,
    parents deleted) for true and false formulas; no checker extension needed through M4. Not covered by
    proofs: everything QDIMACS-specific (model cubes on resolvents, extension stack), validated by fuzzing.
12. Vivification (M4): only constraints of the candidate's kind propagate, mode-0 conflict completion is off,
    decision-only analysis; modes 0/1 only at first. Expressible in QLRUP.
13. `--cert`: extension stack for eliminated variables of the outermost block; that block stays frozen under
    `--cert` until `tests/check_cert.py` (M1.8) validates the stack.

Open points (need a decision when they come up):
- Certificates under `-dl` can be partial in the old solver (unassigned variables printed positive). M1.8
  measures whether such certificates are valid; coordinator decides on the fix.
- Relaxing the rightmost condition with dependency arguments (ROADMAP M5 item 3) would unblock many gates
  under `--earlytseitin`; it relaxes an explicit owner requirement and needs the owner's approval.
- A full-tier (600 s) baseline run and the noise-floor double run are still to be made (ROADMAP 0.3); a
  180 s baseline run appears to be in progress (`bench/results/baseline-t180`).
- Benchmark memory limit: ROADMAP asks for `--mem-gb 16`; the baseline parser exceeds 1.6 GB RSS within 5 s
  on the largest files, so check MEMOUT counts of the baseline before fixing the limit.

## Revision 2 of architecture and roadmap after review 00 (coordinator, 2026-11-21)

`reviews/00-architecture.md` did not approve revision 1 (five blocking items). All five are accepted and
worked into `ARCHITECTURE.md` / `ROADMAP.md`; ARCH section 13 ("Review responses") maps every review item to
the changed sections. Still no solver code. Workers: re-read ARCH 3, 7.2, 9.1, 9.2, 11.1 and ROADMAP 0 before
starting anything; **P0.1-P0.4 (ROADMAP 0.4) come before M1.3**, M1.1 and M1.2 are unaffected except for
formatting (decision 23).

Decisions added or changed (numbers continue the list above; 1, 7, 11, 13 are amended):

14. **Tests must reach the scheduled machinery (B1).** Corpus = tiny tier (brute-force ground truth) + search
    tier (10^2-10^4 baseline conflicts, checkable proofs; histogram to be reported here by P0.1).
    `tests/matrix.txt` holds normal and *stress* configurations (reduce every few conflicts with `tier1glue=0`
    and `gcfrac=0`; restart every conflict with `depreset=1`; later tiers, root simplification, inprocessing
    every few conflicts). Option ranges must allow this (ARCH 9.1); the solver prints `c stat <name> <int>`
    lines; `regress.sh` fails if a counter required by a configuration is nonzero on fewer than 10% of the
    search-tier instances, and if a stress configuration times out on more than 2%.
15. **Benchmark evidence (B2).** `--seed=s` randomises initial scores (baseline: `-rnd-init -rnd-seed=s`).
    Run sets: quick tier (60 s) seeds 1-5, full tier (600 s) seeds 11-13, same seeds for both arms. Claims
    need `compare.py --paired`: bootstrap 95% interval of the mean per-instance PAR2 difference plus a sign
    test; "better" and "not worse" are defined in ROADMAP 0.3 and used by every gate. Experiment items must
    pass at the quick tier and again at the full tier. Fixed limits: `--jobs 48 --mem-gb 16 --cores 64-127`;
    `compare.py` refuses runs with different limits. `bench/results/baseline-t5` and `baseline-t180`
    (8 GB, 64 jobs, unseeded) are informational only; the reference baseline numbers are P0.4's.
16. **Proof coverage (B3).** Every report carries a coverage table (solved / attempted / accepted / rejected /
    checker timeout / memout / too large, non-accepted ones by name). A proof is attempted for every instance
    solved at the quick tier: routinely for the "on" arm with seed 1; at milestone gates with seed 0 for
    default, `-dl`, `-mode=1`, checker limit 3600 s and 32 GB, `qlrup-trim` retry, at most 6 proof jobs and
    8 GB per proof (disk). No unexplained drop between gates. Proof overhead (time ratio, bytes, bytes per
    conflict, trimmed size) is measured once per milestone.
17. **QDIMACS soundness (B4).** The old criterion ("stored cubes stay implicants of the irredundant
    clauses") was wrong once learnt clauses strengthen irredundant ones. New invariant INV-SANDWICH: with `G`
    irredundant clauses, `L` learnt clauses, `T` stored cubes, `Π.(G ∧ ⋀L)` and `Π.(G ∨ ⋁T)` both have the
    input's truth value. A step is admissible if the first value does not decrease (LO) and the second does
    not increase (HI); ARCH 11.1 argues every step of M1-M4, ROADMAP M3.2 gives both directions for
    elimination (E2 and E3 are used only in (HI)). Consequences for the code: irredundant constraints MAY be
    strengthened using redundant ones; a redundant constraint that justifies removing an irredundant one is
    promoted first; unit constraints are irredundant and never deleted; a root-disabled constraint is deleted
    only if the disabling literal has a stored unit (either kind), for both input formats; initial cubes hit
    the current irredundant clauses including units and are verified by `check_model_cube ()` under `--check`
    and in debug/asan builds; for QDIMACS in mode 2 only equivalent shrinking of `G` is allowed (no
    elimination, no deletion under a unit cube). QCIR verdicts still rest on INV-DERIVED alone.
18. **No `External` class (B5, S10; amends decision 1).** Layers are app / frontend / `Solver` / `Internal` /
    base with no upward pointer. `Solver` owns the user<->internal variable maps and only translates. The
    extension stack (`extend.cpp`), certificate values (`certificate.cpp`) and frozen marks are `Internal`
    state in internal literals. Proof numbers are per-variable static data in `prefix.hpp`, read by `Proof`.
19. **QDIMACS elimination is optional and off by default (S2; amends decisions 11 and 13).** It moved to
    ROADMAP M3.6 (`--elimqdimacs`, default 0), to be built only on the coordinator's go-ahead; the extension
    stack (clause entries only) and the `--cert` freeze belong to that package. For QCIR the stack is always
    empty (inputs are never eliminated).
20. **Model-cube fallback on QCIR input.** M1 keeps the old behaviour. From M2.1 on, reaching the fallback on
    QCIR input ends the run with "unknown" and an error, with or without a proof (no argument covers such a
    cube next to the cube encoding once irredundant constraints change); counted in `stats.modelcubes`.
21. **One watch loop (S4).** `template <Kind, Lone> propagate_watches` with `Lone::{Conflict, Propagate,
    Ignore}` serves search modes 0/1 and vivification; mode 2 and occurrence propagation have their own code;
    mode dispatch is outside the loop (ARCH 7.2).
22. **Technique touch points (S5).** ARCH 3.6 lists what adding a technique touches; per-technique state is
    one struct member of `Internal`; an edit to `propagate*`, `analyze*`, `learn.cpp` or `assign.cpp` made
    for a technique is a design change and must be noted in this file.
23. **Formatting is CaDiCaL's (S9; owner may reverse).** `.clang-format` = copy of `~/cadical/.clang-format`
    (76 columns, `SpaceBeforeParens: Always`). Revision 1 had chosen LLVM style at 100 columns. Changed now
    because no code exists; reversing it later is one file plus a reformat.
24. **Constraint header is provisional (S3).** 16 bytes as designed, measured against the baseline in M1.3
    (propagations/s, RSS); 12-byte fallback if it costs.
25. Smaller changes: `--arenasort` renamed `--arenaorder` (name clash with CaDiCaL); `Flags` statuses and
    header bits are introduced with the technique that uses them; signal handlers only set the termination
    flag and the app flushes the proof (S7); the internal `Checker` has a stated scope per input format and
    mode, and tracers get `add_model_cube` (S8); modes 1 and 2 have a quick-tier gate per milestone (S12);
    M1.9 reports port fidelity: propagations/s, conflicts/s, conflict-count ratios against the baseline (S6).

Interpretations of the owner's requirements that the owner may veto:

- **"Watcher lists stored in memory based on accesses"** is read as MiniSat's `relocAll`: the arena garbage
  collector copies constraints in the order in which the watch lists reference them (variables in index
  order, both signs, both kinds), so that the constraints a watch list visits are adjacent in memory. The
  watch lists themselves stay ordinary per-literal vectors (ARCH 5.3, 6). `--arenaorder=1` (walk variables in
  decision order) is an M2 experiment on top of the same mechanism. If the owner meant something else (for
  example watch lists allocated inside the arena, or reordered by access frequency), ARCH 5.3 and 6.1 change.
- **"The variable eliminated occurs rightmost"** is read by quantifier depth: other variables of the same
  block are allowed, deeper ones are not; checked on irredundant constraints of the variable's kind (E3).
- **"Only eliminate existential (universal) variables if they do not occur in cubes (clauses)"** is read
  strictly, including learnt constraints of the other kind (E2).

Open points (replace the list above where they overlap):

- **For the owner, with the numbers from P0.3/M3.0:** for QCIR input the rightmost condition E3 is not needed
  for soundness (verdicts rest on derivations; the completeness argument does not use it); it is needed for
  QDIMACS. With `--earlytseitin` it may block most gate variables. Whether to relax it (ROADMAP M5 item 3) is
  the owner's call and is asked before M3.2, once the yield table exists.
- Certificates under `-dl` can be partial in the old solver; M1.8 measures validity; `certificate.cpp` is the
  one place where the decision will be implemented.
- P0.2 must find out what proof coverage is achievable at all at the quick tier with the baseline (checker
  speed on multi-GB proofs is unknown); the limits in decision 16 are first values and may be adjusted by the
  coordinator once measured, in ROADMAP 0.3, not ad hoc.
- A full-tier ablation costs about 10 hours of the benchmark cores (2 arms x 2 configurations x 3 seeds x
  ~50 min); the screening rule keeps the number of such runs small, but M2 will still need several days of
  machine time.
- `bench/results/baseline-t180/` is untracked and its run (PID 38377, started by the infrastructure worker)
  was still in its proof phase when this revision was written; whoever owns it commits or discards it.

## M1 planned as ten tasks (coordinator, 2026-11-21)

State at planning time: no `src/` yet; P0.1-P0.4 not started; only docs, harness v1 and `regress.sh` v1
exist. The task order is in ROADMAP "M1 execution plan" (T01-T10) and supersedes the M1.x / P0.x order;
the deviations and their reasons are listed there. Decisions added:

26. Order: test tooling, base, frontend, core data, mode-0 search, proofs, reduce + GC, `-dl` + mode 1,
    mode 2 + minimisation, gate tooling. Proofs come before reduce/GC so that the `gc` stress row is
    Lean-checked from the start.
27. The old solver stays in the root CMake build as `miniQU-old` until T10 (ARCH 2 amended).
28. `--arenaorder` is deferred to M2; the default-on `Checker` is not connected when `ccminmode > 0`
    (M1 only, ARCH 8.1 amended); unimplemented options are rejected by the app until their task lands.
29. M1 benchmark configurations: `default`, `-dl`, `-mode=1`, `-mode=2`, `-ccmin-mode=3`, all spelled so
    that the baseline binary accepts the same arguments. M1 adds no technique, so there is no on/off
    ablation; the comparison is new binary against frozen baseline per configuration.

Note for whoever runs benchmarks: a baseline run started earlier (`bench/run.py ... --tag baseline-t900`,
then `baseline-dl-t180`, 64 jobs on cores 64-127) was still running at planning time; do not start timed
runs on cores 64-127 while it is alive (`pgrep -f bench/run.py`), and do not kill it.

## Owner decision on the rightmost condition E3 (2026-11-21)

Answer to the open point "For the owner" above; no need to ask again before M3.2.

- First build bounded variable elimination with the rightmost condition E3 as specified, and get that
  version working, verified (fuzzing, Lean-checked proofs) and benchmarked.
- Once that version exists, the coordinator may try relaxing E3 (for QCIR input, where the coordinator
  argues it is not needed for soundness) as a separate, optional step behind its own option, with the
  rightmost version kept as the comparison arm in the ablation. The relaxed variant needs the same
  evidence as any other technique: no discrepancies, proofs accepted by the Lean checker.

## Paused during M1-T01 (2026-11-21 18:38)

The run was stopped while the M1-T01 worker was validating the configuration matrix against the baseline;
T01 is NOT finished. State left for whoever restarts T01:

- Committed in 99f4f74: `tests/corpus.py`, `corpus_stats.py`, `matrix.txt`, `regress.py`, `regress.sh`,
  `tests/fake/`. Committed afterwards as work in progress, not validated: `tests/fuzz_qdimacs.sh`,
  `tests/run_regressions.sh`, `tests/regressions/`.
- Not done or not recorded: the conflict histogram over seeds 1..400 required by the T01 spec, the proof
  acceptance rate, the full-matrix validation run. Scratch output of the interrupted run is in
  `/home/ec2-user/miniqu-work/regress` and may be incomplete.
- Two defects observed from outside while T01 ran, to be fixed in T01:
  1. `tests/qcir_fuzz.py` does not terminate for `--vars 80 --gates 400 --blocks 4 --cnf` and
     `--vars 100 --gates 800 --blocks 10` (seeds 3, 4, 5): 15 such processes ran at 100% CPU for over an
     hour and had to be killed by hand.
  2. Timeouts in the regress engine do not kill the whole process tree: `tests/fake/stat-wrapper.sh`
     processes with a baseline solver child were left running (reparented to init) for up to 45 minutes,
     mostly with `-no-early-tseitin`. Kill the process group on timeout and on exit.
- Baseline results (`bench/results/baseline-t180`, `baseline-dl-t180`, `baseline-t900`) are complete and
  committed.

## Owner decision: M1-T01 is time-boxed (2026-11-22)

- M1-T01 (test tooling) must be finished by 01:30 on 2026-11-22, 90 minutes after its restart.
- The corpus thresholds of the T01 spec (>= 70% of search-tier instances with 100 to 10000 baseline
  conflicts, >= 90% of proofs accepted within 120 s, seeds 1..400) are targets for this task, not gates.
  The worker reports the numbers it measured, on a smaller sample if necessary, and which targets were
  missed.
- For the reviewer: do not block M1 because these T01 targets were missed or measured on a reduced sample,
  as long as the tooling works (stress configurations exist, the coverage assertion fires, timeouts kill
  the process tree) and the shortfall is reported honestly. Treat the shortfall as a suggestion for later
  tuning, not as a blocking item. This relaxation applies to T01 only.

## M1-T01 finished: test tooling (worker, 2026-11-22)

Delivered and validated with the frozen baseline (`/home/ec2-user/miniqu-work/baseline/miniQU`) and the fake
solvers in `tests/fake/`; no solver code and no checker code was touched. Files: `tests/corpus.py`,
`corpus_stats.py`, `matrix.txt`, `regress.sh` + `regress.py` (engine), `fuzz_qdimacs.sh`,
`run_regressions.sh`, `regressions/`, `fake/`.

Fixes of the two defects noted in the pause entry:
1. `qcir_fuzz.py` did not hang by itself: with `--vars 80` it brute-forces a truth table of 2^80 bits. It now
   exits with an error above 22 variables unless `--no-expected` is given. The search tier does not use it.
2. `regress.py` runs every solver, checker and `bench/run.py` child in its own process group
   (`run_group`), kills the whole group on timeout and on exit, SIGINT or SIGTERM. Verified with a script
   that forks a sleeping grandchild: nothing survives the timeout.

Search tier (`tests/corpus.py --list-sets`): `qcnf-sat`, `qcnf-mixed`, `qcnf-unsat` (qcir_gen.py `qcnf`),
`reach-48`, `reach-44` (`reach`); `game`, `synth` and larger `qcir_fuzz.py` instances were dropped (baseline
needs under 10 conflicts, or no useful spread). Seed selects the set round-robin.

Measured with `taskset -c 0-63 python3 tests/corpus_stats.py --check` (seeds 1..400, baseline, `-verb=1`,
`conflicts :` line, 20 s timeout; raw numbers in `/home/ec2-user/miniqu-work/regress/final-stats.csv`).
Instances per conflict bucket:

| default | 0-9 | 10-99 | 100-999 | 1000-9999 | >=10000 | timeout | in [100,10000) | max s |
|---|---|---|---|---|---|---|---|---|
| qcnf-mixed | 0 | 0 | 1 | 72 | 7 | 0 | 91% | 0.4 |
| qcnf-sat | 0 | 0 | 1 | 77 | 2 | 0 | 98% | 0.1 |
| qcnf-unsat | 0 | 1 | 13 | 45 | 21 | 0 | 72% | 0.4 |
| reach-44 | 14 | 1 | 36 | 29 | 0 | 0 | 81% | 0.2 |
| reach-48 | 11 | 4 | 30 | 35 | 0 | 0 | 81% | 0.2 |
| all | 25 | 6 | 81 | 258 | 30 | 0 | 85% | 0.4 |

| `-dl` | 0-9 | 10-99 | 100-999 | 1000-9999 | >=10000 | timeout | in [100,10000) | max s |
|---|---|---|---|---|---|---|---|---|
| qcnf-mixed | 0 | 0 | 9 | 58 | 13 | 0 | 84% | 0.4 |
| qcnf-sat | 0 | 11 | 38 | 31 | 0 | 0 | 86% | 0.1 |
| qcnf-unsat | 0 | 0 | 10 | 52 | 18 | 0 | 78% | 1.2 |
| reach-44 | 6 | 10 | 20 | 44 | 0 | 0 | 80% | 0.8 |
| reach-48 | 7 | 7 | 16 | 48 | 2 | 0 | 80% | 15.5 |
| all | 13 | 28 | 93 | 233 | 33 | 0 | 82% | 15.5 |

Requirements: 85% / 82% in range (need 70%); baseline time at most 0.4 s / 15.5 s (need under 20 s; the
`-dl` maximum is on one `reach-48` instance, so the 20 s solver timeout of `regress.sh` is tight for it);
Lean-checked binary proofs of the default run: 400 of 400 accepted, longest check 5.4 s (need 90% in 120 s).

Acceptance runs (logs in `/home/ec2-user/miniqu-work/regress/`):

| command | result |
|---|---|
| `tests/regress.sh -s 1:100 -M all tests/fake/stat-wrapper.sh` | exit 0, `REGRESSION TESTS PASSED (4 warnings)`; warnings are timeouts of the baseline under the stress-free rows (`noearly` 9, `mode1-dl`, `mode2-dl`, `restart-mode1-dl` 1 each) |
| same with `tests/fake/zero-stat.sh` | exit 1, `99 problem(s)`, all `counter X is nonzero on 0%` coverage failures, no verdict failure |
| same with `tests/fake/always-sat.sh` | exit 1, `796 problem(s)`: 697 `wrong verdict SAT, expected UNSAT` plus coverage failures (no stat lines) |
| `tests/regress.sh -s 1:20 /home/ec2-user/miniqu-work/baseline/miniQU` (old interface) | exit 0, coverage assertion skipped with a note |
| `tests/run_regressions.sh /home/ec2-user/miniqu-work/baseline/miniQU` | `7 instances, 0 failures` (proofs Lean-checked) |
| `tests/fuzz_qdimacs.sh BASELINE 1 300 OPT`, OPT = `''`, `-dl`, `-mode=1`, `-mode=2` | `0 failures, 0 timeouts, 600 instances agreed` for the first three; `-mode=2`: `0 failures, 1 timeouts, 599 instances agreed` |

QDIMACS fuzz tiers: tiny `-v 14 -c 50 -s 4 -r 0.6 --min=2 --max=4` (checked against `qcir_eval.py`); large
`-v 70 -c 300 -s 3 -r 0.8 --min=4 --max=4` (baseline conflicts on seeds 1..30: 275 to 9751, all in
[100,10000)). No baseline disagreement with itself or the evaluator was found, so `tests/regressions/` holds
only hand-written instances.

Notes for later tasks: the fake `stat-wrapper.sh` takes its counter list from `tests/matrix.txt`, so a new
counter name must be added there only. Counter names in the matrix are the interface the new solver's
`c stat NAME VALUE` output must satisfy (ROADMAP 0.1).


## M1-T02 finished (worker, 2026-11-22)

Built: `.clang-format` (copy of CaDiCaL's), root `CMakeLists.txt` (C++20, targets `miniqu` static library from
`src/*.cpp`, `qlrup-trim`, `unit-tests` plus one `unit-<name>` executable per `test/unit/*.cpp`, each a ctest
test; ctest test `format` runs `clang-format --dry-run -Werror` over `src/` and `test/unit/`; old solver as
`miniQU-old`, its library as `miniqu-old-lib`, C++17, no -Werror), `CMakePresets.json` (release, release-clang,
debug, asan, log, with matching build and test presets; build trees in `/home/ec2-user/miniqu-work/build/<preset>`),
and the base layer in `src/` (`lit arena constraint watch heap ema random util options stats profile limit
message logging contract file`, namespace `miniqu`, no reference to `Internal`) with ten unit tests (`arena
constraint lit watch heap ema random options stats file`; `stats` also covers `profile`).

Commands (all pass, zero warnings, 11/11 tests incl. `format`, for P in release debug asan release-clang log):
`taskset -c 0-63 cmake --preset P && taskset -c 0-63 cmake --build --preset P -j16 && taskset -c 0-63 ctest --preset P`.
`tests/regress.sh -s 1:20 .../build/release/miniQU-old`: passed (20 proofs Lean-checked, smoke passed). I also
confirmed that the `format` test fails on a misformatted file.

Decisions and deviations (ARCH 2 updated for the first two):
- The asan preset needs a CMake workaround: this machine's GCC 11 has `libasan.so.6.0.0` but no `libasan.so.6`
  or `libubsan.so.1` link, so the binaries could not start. `CMakeLists.txt` creates the symlinks in
  `<build>/sanitizer-runtime` and adds an rpath (GCC only).
- The two old ctest entries (`tests/fuzz.sh` on the old binary) were dropped from the root `CMakeLists.txt`; the
  new ctest set is the unit tests and `format`, and ARCH 2 says the fuzz tests return with T05. The scripts are unchanged.
- `Watches::lookup`, `clean` and `clean_all` take a `const Arena &` for the garbage test (spec allowed either).
  `clean_all` cleans only the lists that were smudged; a list that was not smudged keeps garbage (tested).
- Verbosity and the `log` switch are process-wide (`set_verbosity`, `set_logging`) because the printing helpers
  sit below `Internal`; `MSG` prints at verbosity >= 1, `VERBOSE (l, ...)` at >= l, `PHASE` at >= 2.
- `Stats::print` takes the elapsed seconds for the rate table. `START (name)` / `STOP (name)` expect a
  `Profiles profiles` member in scope; `PROFILE_SCOPE (name)` is the RAII form. Profile levels (parse 0, search 1,
  reduce 2, collect 2, analyze 3, propagate 3) are a first guess for the core task to adjust.
- `Constraint` has `alloc_constraint (Arena &, span, Kind, redundant, id)` as the only way to create one, and
  `shrink (n)` returns the words to report as wasted. `parse_option` does not check the name against the table;
  `Options::set` does (unknown or out of range gives false).
- `Limit`, `Inc`, `Last` contain only the M1 fields: restart, reduce, plus the user limits `conflicts` and
  `decisions` (-1 = unset) in `Limit`.


## M1-T03 finished: frontend (worker, 2026-11-22)

Built (namespace `miniqu`, formatted, no warnings with GCC and Clang): `src/miniqu.hpp` (public `Solver`, ARCH 3.5,
declarations only), `src/tracer.hpp` (ARCH 8.1), `src/circuit.{hpp,cpp}`, `src/parse.hpp` + `parse_qcir.cpp` +
`parse_qdimacs.cpp`, `src/encode.{hpp,cpp}`. There is no `solver.cpp`; `Solver` is defined only by
`test/unit/fake_solver.cpp`. CMake: the four frontend sources form the object library `miniqu-frontend` (not part of
the static library `miniqu`); unit tests `circuit parse_qcir parse_qdimacs encode` link it with `miniqu-fake-solver`;
tool `encoding-dump` (`test/tools/`); ctest test `encoding-diff` runs `tests/encoding_diff.sh 1 50`.

Verification (all measured):
- `ctest --preset P`, P in release, debug, asan, release-clang: 16/16 pass each (unit tests, `format`, `encoding-diff`).
- `tests/encoding_diff.sh 1 500`: 1006 instances (500 seeds x both tiers + 6 regressions), 0 differences, with and without
  `-no-early-tseitin`. The check is not vacuous: a tool wrapper that deletes one line is reported on every instance.
- The 30 smallest files of `/home/ec2-user/benchmarks/qcir` (list by size) plus 6 regressions: 215048 constraints
  compared, 0 differences. The script interrupts the baseline as soon as it prints `Parse time` (it writes the `o`
  lines while it parses), so no baseline solving time is spent.
- `tests/regress.sh -s 1:20 .../build/release/miniQU-old`: passed. No proofs were produced by new code (no solver
  yet), so there was nothing for the Lean checker to check.
- The add_var order (prefix, group order, decision flag, proof number) is not visible in the baseline's proofs; it is
  covered by hand-derived expectations in `test/unit/encode.cpp` (with and without early Tseitin, a gate without
  dependencies, first block universal, no block at all, output an input literal with an unused gate, `free` block,
  QDIMACS with a free variable).

Memory and time on the 5 largest benchmark files (`encoding-dump --count`, release build, `taskset -c 0-63`, wall time
and peak RSS from `/usr/bin/time -v`; baseline = `miniQU -verb=1`, VmHWM read from `/proc` when it printed `Parse time`
and wall time to that point, which includes its encoding into the solver):

| file | size | new wall | new peak RSS | baseline wall to parse | baseline RSS at parse |
|---|---|---|---|---|---|
| 2.2.qcir | 1.6 GB | 69.5 s | 6.0 GB | 139.6 s | 40.5 GB |
| 2.1.qcir | 495 MB | 19.2 s | 1.9 GB | 41.4 s | 12.8 GB |
| 5.2-3.qcir | 411 MB | 16.8 s | 1.6 GB | 34.9 s | 10.8 GB |
| 5.2-2.qcir | 79 MB | 3.0 s | 0.34 GB | 7.1 s | 2.3 GB |
| lift3.tlsf.qcir | 67 MB | 2.2 s | 0.26 GB | 6.1 s | 2.0 GB |

(RSS in GiB = kB / 2^20: new 6314180, 1975268, 1686192, 357256, 271116 kB; baseline 42485184, 13448788, 11345956,
2388184, 2074552 kB.) The new frontend uses 6 to 7 times less memory than the baseline's parser and is 2 times
faster. This is parse + circuit + encode into a recording fake that only counts; the real solver will add its own
memory. Totals reported by `--count` for 2.2.qcir: 109148560 variables, 88487180 clauses, 75224781 cubes.

Design decisions and deviations from the spec (ARCH 3.5 updated):
- **Circuit merges adjacent blocks of equal quantifier at insertion**, instead of keeping them separate and merging in
  the encoder. The depth of a gate (the index of the innermost block) decides where its variables go; the baseline
  computes it with merged blocks, so unmerged indices would put gate variables elsewhere. `free` is an existential
  statement wherever it occurs, as in the baseline.
- **Forward references.** The baseline accepts gates used before their definition (the output statement usually comes
  first, and `g = and(h)` before `h = ...` is accepted). The new parser accepts them too: `Circuit::reference` hands out a
  provisional number (>= 2^30) and `resolve ()` replaces them in one pass. Numbers are always definition order, as the
  proof format says. The baseline orders the variables of the groups by *first mention* of an identifier, so for files
  with forward references between gates the order of gate variables inside one group can differ from the baseline.
  The constraints are identical (checked on forward-reference files); no benchmark relies on this.
- Gates removed by `remove_redundant` still get both variables in `encode`, exactly as `initSolver` of the old code
  (they appear in `gates_at_depth`), so that the prefix is the same as in the baseline; they get no constraints.
- The encoder passes the raw constraints of a gate (duplicate literals, complementary literals, e.g. `and(a, -a)`) to
  `Solver::add_original`; the header documents that the solver removes duplicates and drops tautologies, as the old
  `addOriginalWithProof` does. The next task must implement exactly that, since the `o` lines of the proof show the
  reduced constraint. An empty clause from QDIMACS (a line `0`) is also passed through as an empty constraint.
- Messages: the baseline prints `Done parsing` and `Removed N redundant gates` on stderr always; the new parsers print one
  `c parsed ...` line at verbosity >= 1 through `VERBOSE`.
- `encode.hpp` and `tracer.hpp` are additional headers (the spec named only `parse.hpp`).

Behaviour against the baseline on malformed or unusual input (each case run on both binaries; file and line number in
the new messages):
- Both reject: undefined identifier, gate defined twice, gate named like a variable, variable quantified twice, xor
  arity != 2, ite arity != 3, unknown gate type, missing output, repeated output, `output(-)`, `output()`,
  quantifier statement after a gate, malformed line, trailing characters, empty gate input (`and(a,,b)`, `and(,a)`).
  (Baseline: `output(a, a)` ends with "undefined output" because it reads the identifier `a,a`; new: "output takes exactly
  one literal".)
- Both accept, same meaning: gates used before their definition (also xor/ite), a trailing comma `and(a,)`, header and
  comments, case-insensitive keywords, any amount of blanks around tokens, empty `and()` / `or()`.
- Baseline accepts, new parser gives a clean error (list of divergences): (1) cyclic definitions (`g = and(h)`,
  `h = or(g)` or `g = and(g)`): the baseline answers with garbage, new: "gate 'g' depends on itself"; (2) an empty
  identifier in a quantifier list (`exists(a,,b)` creates a variable named ""); (3) whitespace inside an identifier
  or between the identifiers of a list (`exists(a b)` is the single variable `ab` for the baseline, whose parser deletes
  all blanks of the line); (4) identifiers that start with '-' in a definition. The characters `( ) , =` cannot occur in
  identifiers of the new parser. A statement must fit on one line, as in the baseline.
- QDIMACS: a variable that occurs in a clause but is not quantified is an outermost existential variable (the old
  parser uses an uninitialised map entry: undefined behaviour). Quantifier lines are accepted between clauses, the
  header counts are not checked (both as the old parser); errors (missing `0`, non-number, number out of range, variable
  quantified twice, negative variable in the prefix, bad header) end with file and line.

Notes for later tasks:
- `Solver::add_var` contract used by the encoder: user variable numbers are not dense (gate variables are
  `n + 2 (p - n) - 1` and `n + 2 (p - n)`), strictly increasing numbers are not guaranteed, consecutive calls of one
  quantifier form a block; input variables use their proof number, QDIMACS variables proof number 0.
- `-cert` needs the name of an input variable: `Circuit::name (number)` (the file's identifier). The app keeps the
  `Circuit` (or only the names) alive after encoding; `parse_qcir` returns the circuit by value.
- `tests/encoding_diff.sh` needs the baseline binary and `encoding-dump`; the ctest entry sets `ENCODING_DUMP` itself.

## M1-T04 finished: core data layer (worker, 2026-11-22)

Built (namespace `miniqu`, formatted, no compiler warnings with GCC and Clang): `src/internal.{hpp,cpp}` (`struct
Internal`, `add_var`, `solve` = status only), `src/prefix.{hpp,cpp}` (`Block`, `VarInfo`, `Prefix::add_var`, `qreduce`,
`is_primary`), `src/constraint.cpp` (`add_original`, `new_constraint`, `mark_garbage`, `shrink_constraint`, `attach`,
strict `detach`, `found_empty`), `src/assign.cpp`, `src/propagate.{hpp,cpp}` (the templated watch loop
`propagate_watches<K, Lone>`, the driver `propagate_trail<Lone>`, `propagate ()` with mode-0 completion),
`src/propagate_ldq.cpp` (mode 2: `fatal ("mode 2 not implemented yet")`), `src/backtrack.cpp`, `src/check.cpp`
(`check_invariants`, all builds, fatal on violation), `src/solver.cpp` (the real `Solver`; contracts, user<->internal
maps), `Internal::log` (constraint printing) in `src/logging.cpp`. Unit tests `original propagate backtrack solver
regressions` (+ heap offset test); `regressions` parses every file of `tests/regressions` through the real frontend into
the real `Solver`, modes 0/1, with and without early Tseitin, propagates at the root and runs `check_invariants`.

Verification: `ctest --preset P` for P in release, debug, asan, release-clang: 21/21 pass (unit tests, `format`,
`encoding-diff`). `tests/regress.sh -s 1:20 .../build/release/miniQU-old`: passed (there is no new binary yet, so no
new proofs exist and nothing new was Lean-checked; this task emits no proof steps). The release builds print
`lto-wrapper: warning: using serial compilation of 2 LTRANS jobs` when linking `unit-encode` (already before this task)
and now also `unit-regressions`: a GCC LTO partitioning note from the linker, not a compiler warning.

Behaviour of the old `propagate` that was ambiguous, and what the port does:
1. **Order of kinds**: per trail literal the clause loop runs before the cube loop, as in the old code.
2. **After a conflict** the old code set `qhead = trail.size ()` but did *not* leave the `for ct_` loop: after a clause
   conflict the cube loop of the same literal still ran, could assign further literals (which were then propagated,
   since the while loop tests `qhead < trail.size ()` again) and could overwrite the conflict, its kind and `q` with a
   later one; a cube propagation could even assign the secondary literal `q` of a pending mode-0 clause conflict,
   which then skipped completion and left a "conflict" that was not falsified. The port stops at the **first**
   conflict (remaining watches of the list are copied, the cube loop of that literal does not run) and leaves
   `propagated` at the conflicting literal, so `propagated` means "propagated completely in both kinds" (ARCH 7.2
   amended). Backtracking resets it to `min (propagated, start of the undone levels)`.
3. **Conflict condition**: old `value(first) == l_vanishing || (mode == 0 && first is secondary)` after no replacement
   was found; `first` cannot be disabling there (that case was handled before). Same in the port, with the secondary
   case selected by `Lone` at compile time. Completion (mode 0) assigns the vanishing value of the remembered literal
   (`~q` for a clause, `q` for a cube), reason none, current level; with the first-conflict rule that literal is always
   unassigned when completion runs (asserted).
4. **Phase saving 1** follows MiniSat's `c > trail_lim.last ()`: only the implied literals of the highest undone level
   are saved, not its decision.

Deviations from the spec / ARCH (ARCH updated in the same commit where marked):
- `Heap` takes a variable offset (`Heap (scores, first)`): with one heap per block, position tables over all variables
  would cost blocks x variables words (`heap.hpp`, ARCH 3.1).
- `Watches::resize` (variables are created one at a time) and a const `operator()`.
- INV-WATCH as checked: both watched literals have a watch whose blocker is *another literal of the constraint*, not
  necessarily the other watched literal (MiniSat never updates the blocker of the watch that stays; ARCH 6.1 amended);
  plus, once propagation is complete, a vanished watched literal only in a disabled constraint.
- Unit originals of different kinds can never meet on one variable (after `qreduce` a unit clause is existential, a
  unit cube universal), so "already assigned by the other kind" is an assertion, not a branch; the unit test checks a
  unit clause and a unit cube together decide nothing.
- After the formula is decided, further originals are counted and consume their ids but are not stored (old proof
  path). `stats.originals[kind]` counts originals that survive the tautology check (= future `o` steps).
- Ids as the old proof path: the given original one id, its reduction (if any) the next, the empty constraint from two
  complementary units another one.
- `Solver::set` REQUIREs a known option name and returns false only for an out-of-range value (`miniqu.hpp`, ARCH 3.5).
  The app (T05) must check names against `option_table ()` before calling it.
- `miniqu.hpp` befriends `Internal &internal_of (Solver &)` for white-box tests (ARCH 3.5).
- `enum class Lone` is declared in `internal.hpp` (member template declarations need it); `propagate_trail<Lone>` is the
  shared driver of both kinds (ARCH 7.2).
- `detach` is strict only; the lazy form is `mark_garbage` (smudge), since smudging cleans only garbage entries.
  `mark_garbage` asserts size >= 2 (units are never deleted).
- `Block::unassigned` is maintained in every mode (the old code skipped it under `-dl`); `assign` and `backtrack` keep it.
- `check_invariants` lives in a new `check.cpp` (ARCH 3.2) and is compiled in all builds (needed by `--check`).
- `logging.cpp` includes `internal.hpp` for `Internal::log` (ARCH 3.1); `LOG` now calls `log` unqualified so that it
  reaches `Internal::log` inside member functions.

Left for later tasks:
- Proof hooks: no `Proof` interface exists, so `mark_garbage` and `add_original` contain no `if (proof)` call sites;
  T06 adds them (ids are already allocated exactly as the proof needs). `Solver::connect_tracer` is
  `fatal ("proofs not implemented yet")`; `flush_proof` does nothing.
- `Solver::val` / `certificate` are `fatal ("certificates not implemented yet")`; `freeze` only checks its argument
  (nothing eliminates yet). `Proof *proof`, `lim`, `inc`, `last`, `scores`, `terminated`, `redundant` exist but are not
  used by this task's code.
- Heaps are filled in `add_var` (as the old `newVar`); with `--seed` T05 must rebuild them after setting scores.
- `Profiles` is not yet a member of `Internal` (no profiled phase exists).

## M1-T05 finished: mode-0 search and the `miniQU` binary (worker, 2026-11-22)

Built (namespace `miniqu`, formatted, no compiler warnings with GCC and Clang): `internal.cpp` (`solve`, `search`: the
loop of ARCH 7.1 with propagate / analyze, terminated, restarting / restart, decide, initial cube), `decide.cpp`
(first block with `unassigned > 0`, pop its heap until an unassigned variable, saved phase, `eligible` = old
`isEligibleDecision` as an assertion), `bump.cpp` (EVSIDS as MiniSat: `+score_inc`, rescale at 1e100, decay
`1000/vardecay` after each learnt constraint; `--seed=s` gives each variable in creation order `drand * 1e-5` from
`Random (s)`, set in `add_var`, so no heap rebuild is needed), `analyze.cpp` (port of `analyzeQ`, see below),
`learn.cpp` (`qreduce`, empty -> `found_empty`, asserting literal at 0, highest other level at 1, glue before the
backjump, backtrack, `new_constraint (redundant)`, assign `forced (kind, lit)`, decay, `learned`/`learnedlits` per
kind), `restart.cpp` (Luby / geometric, `restart_interval (k) = (int64) (rfirst * luby (rinc/100, k))`, restart when
`conflicts >= lim.restart`), `model.cpp` (buffer constraint of capacity `vars`, `initial_cube` = old `getInitialTerm`
incl. bumping the reduced-away variables, `check_model_cube` with assertions or `--check`, `stats.modelcubes`),
`certificate.cpp` (outermost block with decision variables, recorded before the final `backtrack (0)`, unassigned ->
positive), `report.cpp` (one `PHASE` line per restart at verbosity >= 2), `Solver::val` / `certificate`, and the
application `app.cpp`, `signal.{hpp,cpp}`, `resources.{hpp,cpp}` (target `miniQU`, not part of the library). Base
additions: `no_var` (compares greater than every variable, so "no blocked variable" needs no special case),
`Constraint::set_size` (only for the model-cube buffer), `Prefix::reduced_size`, `forced (kind, lit)` in
`internal.hpp`. Unit test `unit-search` (Luby/geometric intervals, glue, learnt clause and cube by hand, continued
resolution right of a blocked literal, unit learnt stored irredundant, root literal kept, empty clause, decisions and
phases, seeded scores, initial cube with bumping, `Solver` runs with certificates). ctest now also runs `fuzz`
(`tests/regress.sh -n -S -s 1:20 -M default`) and `run-regressions` (`-n`); T06 should drop the `-n`.

Analysis (`analyze.cpp`): resolution over primary literals in reverse trail order with `seen`, `level_count`,
`level_blocked`, the asserting condition of the old code (unique primary on a level > 0 and left of every blocked
secondary), then continued resolution of the primary literals right of the leftmost blocked literal; all comparisons
are index comparisons; antecedent hook `if (proof) chain.push_back (c.id ())`. **The "decision in the way" branch is
unreachable without `--dl`** (argument in the file header: a blocked secondary variable left of a decision pivot lies
in an earlier block and would have been assigned on a lower level; it needs the blocked variable to be a decision
variable, which holds for every constraint except a QCIR initial cube, unreachable by INV-COMPLETE). It is a `fatal`
internal error, not an assertion only, because a release build would otherwise resolve with `Ref::none`; T08 replaces
it by the dependency outcome (`clear_analyzed ()` exists for that early exit). `stats.modelcubes` stayed 0 on every QCIR
run of the acceptance (coverage tables below).

Porting notes, how each is covered: 1 original constraints: `unit-original` (T04). 2 conflict completion:
`unit-propagate` (T04), exercised by every fuzz run. 3 index comparisons: `unit-search` (`test_resolve_right_of_blocked`
needs `v > blocked` on indices). 4 kind switch: mode 1, T08. 5 root literals stay: `test_root_literal_stays`. 6 initial
phase false, phase saving: `test_decide`, `unit-backtrack`. 7 learnt-database policy: T07 (no reduce yet). 8 glue
before backjump: `test_glue`, `test_learn_clause` (glue 2), `test_root_literal_stays`. 9 dependency reset: T08. 10 gate
variables never decided: `test_decide` (an `E` variable), heaps hold decision variables only (`check_invariants`).
11 `-cert`: byte-identical `V` lines with the baseline on the six regression instances where it prints one.

Acceptance (all with `taskset -c 0-63`; logs in `/home/ec2-user/miniqu-work/logs/t05/`):

| command | result |
|---|---|
| build + `ctest --preset P`, P = release, debug, asan, release-clang | no warnings (release prints only the known `lto-wrapper: using serial compilation` linker note); 24/24 tests pass each |
| `tests/regress.sh -n -s 1:300 -M default R` | PASSED, 0 failures, 0 timeouts; coverage over 150 search instances: conflicts 100%, restarts 90%, learned.clause 99%, learned.cube 91% (modelcubes 0%) |
| `tests/regress.sh -n -s 1:100 -M default A` | PASSED, 0 failures, 0 timeouts; conflicts 100%, restarts 90%, learned.clause 96%, learned.cube 94% |
| `tests/fuzz_qdimacs.sh R 1 300` / `A 1 100` | `0 failures, 0 timeouts, 600 instances agreed` / `0 failures, 0 timeouts, 200 instances agreed` |
| `tests/run_regressions.sh -n R` | `7 instances, 0 failures` |
| `tests/regress.sh -n -S -s 1:100 R -- --seed=1 -- ... -- --seed=5` | PASSED: all five seeds agree with the baseline / evaluator on 100 instances, 0 timeouts |

(R = `/home/ec2-user/miniqu-work/build/release/miniQU`, A = `.../build/asan/miniQU`.) No proofs exist yet, so nothing
was Lean-checked in this task.

Conflict counts against the baseline (default options, search-tier seeds 151-170; new / baseline): 5454/5298,
5121/7696, 2499/6680, 4/4, 2016/1888, 5761/8580, 6032/6284, 3721/2879, 1714/1904, 809/101, 4125/4300, 2354/10322,
14137/14367, 5/6, 1/1, 2228/1608, 2691/9710, 13784/32566, 17/105, 418/244: same order, no systematic shift (the new
solver has no database reduction yet, the baseline has).

Smoke set (`python3 bench/run.py --solver R --tag m1-t05-smoke --timeout 60 --jobs 32 --instances bench/smoke.txt`,
result in `bench/results/m1-t05-smoke/`): all 31 verdicts equal `bench/smoke-expected.csv`; **31/33 solved** (baseline
33/33), total wall time on the 31 solved by both 26.5 s (baseline 30.5 s). Not solved within 60 s: `jctc1-pass.qcir`
(baseline 0.09 s, 623 conflicts) and `jctc9-pass.qcir` (baseline 1.3 s). This is the baseline's luck with its
unseeded order, not a lost behaviour: with `-rnd-init -rnd-seed=s` the baseline also fails to solve jctc1-pass within
20 s for s = 1, 2, 3 (54k-56k conflicts) and jctc9-pass for s = 1, 3; the new solver with `--seed=s` behaves the same
(46k-60k conflicts in 20 s). RSS stays below 400 MB on both at 60 s. Not tuned, as asked.

Behaviour of the binary, and deviations from the old one:
- Options: `parse_option` with the legacy spellings; unknown names or out-of-range values are errors (exit 1).
  Rejected with "not implemented yet" (stderr, exit 1): nonzero `--mode --dl --ccminmode --legacyanalyze --check
  --reduceint`, and `--proof=` / `--trace=`. `--help`, `-help`, `-h` print usage and the option table.
- Input: QCIR when the name ends in `qcir` or with `--qcir`, else QDIMACS (gzip allowed); stdin without a file. The
  old binary used QCIR only when there was no second (result) file argument; the new one decides by the input name
  alone. Its stdin notice was an unprefixed stdout line; it is now `c reading QDIMACS from standard input` at
  verbosity >= 1.
- Result file (second file argument): receives `SAT`, `UNSAT` or `INDET`. The old binary truncated it and wrote
  `UNSAT` only for formulas decided while parsing; writing every result is the MiniSat behaviour it was derived from.
- Output: at `--verb` >= 1 banner, the parser's `c parsed ...` line, parse time, the `c stat` block and table, peak
  RSS; then the result line and with `--cert` the `V` line. `-verb=0` prints only those two. The `V` line is printed
  also when the input decided the formula (the old binary exited early without one).
- Signals (SIGINT, SIGTERM, SIGXCPU): while parsing a signal ends the run at once (`c interrupted`, exit 1, as the old
  `*** INTERRUPTED ***` path); during the search the first one sets the termination flag and the run ends normally
  with statistics and `INDETERMINATE`, exit 0 (checked with `--cpulim=5` and with SIGINT on `5.1-2.qcir`); a second
  one exits at once. `--memlim`: a failing `std::bad_alloc` ends with `INDETERMINATE`, exit 0 (old behaviour, checked
  with `--memlim=300`); a failing arena `realloc` still ends through `fatal` (exit 1).
- `stats.decisions` counts decisions made (the old counter was also incremented when no variable was left).

Known issues / for later tasks:
- **`tests/regress.sh` smoke step is vacuous after its first run** (T01 tooling, not changed here): `regress.py` calls
  `bench/run.py` with the fixed tag `regress` in `REGRESS_WORK/smoke-<config>`, and `run.py` resumes, i.e. skips every
  instance already in that `results.csv`. `/home/ec2-user/miniqu-work/regress/smoke-default/regress/meta.json` still
  names `tests/fake/stat-wrapper.sh` (the baseline wrapper of T01), so every later `regress.sh` smoke "pass" re-reads
  the baseline's results. Fix: delete the run directory before calling `run.py` (or pass a fresh tag). The smoke
  numbers above come from a fresh `bench/run.py` run, not from `regress.sh`.
- **The machine now exposes 96 cores** (`nproc` = 96, `taskset -c 96` fails with "Invalid argument"). `bench/run.py`
  with its default `--jobs 48 --cores 64-127` gives instances 33+ an unusable core: the first smoke attempt reported
  `test_5_5_tippy.pg-7.qcir` as ERROR (`taskset: failed to set pid ...'s affinity`), which is why the run above uses
  `--jobs 32`. The benchmark protocol (48 jobs on 64-127) needs the coordinator's decision.
- T07 (garbage collection) must relocate `Internal::model_cube`, which is in no list (ARCH 4.5 amended). The buffer is
  allocated with proof id 0; T06 decides which id an initial cube gets for `add_model_cube`.
- No `Profiles` member yet (no `START`/`STOP` in the search); limits `lim.conflicts` / `lim.decisions` exist in
  `limit.hpp` but no option sets them, so the loop checks only `terminated`.
- Without reduce, memory grows with the learnt constraints (651 MB after 4 s on `5.1-2.qcir`).
