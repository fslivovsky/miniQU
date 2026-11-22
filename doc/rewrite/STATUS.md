
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

## M1-T06 finished: proofs (worker, 2026-11-22)

Built (formatted, no compiler warnings with GCC and Clang): `src/proof.{hpp,cpp}` (`Proof`: literal translation to
proof numbers, fan-out to tracers, `strengthen`, `conclude`), `src/qlrup_tracer.{hpp,cpp}` (text and binary QLRUP
through `OutputFile`), `src/trace_tracer.{hpp,cpp}` (older `-trace` format), `src/checker.{hpp,cpp}` (online
`Checker`), the logging points of ARCH 8.2 that exist in M1 (originals, reduction of originals, complementary units,
learnt and empty constraints, `mark_garbage` deletions, initial cubes), `Solver::connect_tracer` / `flush_proof`, and
`--proof=FILE` / `-proof=FILE`, `-proof-binary`, `--trace=FILE`, `--check` in the app. Base additions:
`Constraint::set_id`, `OutputFile::put_decimal`, `stats.checked` (steps the `Checker` replayed). Unit tests `unit-tracer`
(text, binary and trace bytes of a fixed step list, ids/literals above 127; QLRUP model cube is fatal), `unit-checker`
(accepts plain chains, a no-clash premise, a chain that needs reduction after every step, model cubes; rejects a missing
literal, a missing/deleted premise, the other kind, two clashing literals, a reused id, no premises, complementary
literals, unknown variables, wrong deletions, a non-empty conclusion; the gate variable of each kind at its own prefix
position), `unit-proof` (the exact step sequence of originals with reductions and complementary units, ids equal
without a proof, `Proof::strengthen` through the `Checker`, solving through the API with learnt clauses and with model
cubes). ctest `fuzz` and `run-regressions` now check proofs with the Lean checker (`-n` dropped).

Acceptance (all with `taskset -c 0-63`; logs in `/home/ec2-user/miniqu-work/logs/t06/`; R = release, A = asan):

| command | result |
|---|---|
| build + `ctest --preset P`, P = release, debug, asan, release-clang | no warnings (only the known `lto-wrapper: using serial compilation` linker note); 27/27 tests pass each |
| `tests/regress.sh -S -s 1:300 -M default R` (binary proofs) | PASSED: 300 proofs checked by Lean, 0 rejected, 0 wrong verdicts, 0 solver timeouts, 0 checker timeouts |
| `tests/regress.sh -S -s 1:60 -M default -P '' R` (text proofs) | PASSED: 60 proofs checked, 0 rejected, 0 timeouts |
| `tests/regress.sh -S -s 1:100 -M default A` | PASSED, 0 aborts; `checked` = 152367 = `conflicts` summed over the search tier, nonzero on 100% of the instances (every learnt and empty constraint replayed); 100 Lean-checked proofs |
| `tests/run_regressions.sh R` (with proofs) | `7 instances, 0 failures` |
| `qlrup-trim` on 20 new proofs (corpus search seeds 401-420, text and binary) | 40/40 trimmed proofs and their originals accepted by Lean (12 false, 8 true); trimmed to 2%-101% of the size (trimming adds deletions) |
| smoke set: `bench/run.py --tag m1-t06-smoke-proof --timeout 60 --jobs 32 --cores 64-95 --proof-check --proof-max-solve-sec 60` | 31/33 solved (the same two jctc instances as in T05 time out), verdicts equal `bench/smoke-expected.csv`, **31/31 proofs accepted** (Lean total 64.7 s, largest proof 27.9 MB); proof files deleted; `bench/results/m1-t06-smoke-proof/` |

Byte compatibility: on all six `.qcir` instances of `tests/regressions/` the new text and binary proofs are
byte-identical to the baseline's (`cmp`; the searches coincide there). The format of every step is also pinned by the
golden bytes of `unit-tracer`.

Proof overhead (binary proof vs none, R pinned to core 70, three runs each, median wall seconds):

| instance | no proof | binary proof | overhead | proof size |
|---|---|---|---|---|
| test_5_5_snaky.pg-7.qcir | 5.41 | 5.53 | +2.1% | 27.5 MB |
| 9.1.qcir | 1.98 | 2.10 | +6.1% | 27.9 MB |
| hadw10-11.qcir | 1.82 | 1.89 | +4.2% | 17.8 MB |
| 9.3.qcir | 1.55 | 1.58 | +2.3% | 10.5 MB |
| lift_gr1+2.tlsf.qcir | 1.48 | 1.51 | +1.7% | 7.9 MB |

`-trace`: validated on 40 QDIMACS instances (`qbfuzz.py` seeds 1-20 with the tiny and large parameters of
`tests/fuzz_qdimacs.sh`) against the baseline's trace of the same instance: every line of both files matches one of the
two old line forms (`^id [01] (lit )*0 (premise )+0 $` and `^id [01] (lit )*0 0$`), ids are consecutive, every premise
refers to an earlier id of the same kind (baseline: or to an original clause position); verdicts equal. On
`prenex-pair.sat.qdimacs` the derived and initial-cube lines are identical to the baseline's. 8 QCIR traces checked for
the same grammar. Signals: SIGINT after 2 s on `jctc1-pass.qcir` with `--proof` ends with INDETERMINATE, exit 0, and a
proof file that ends with a complete step. `--check` in the release build: replays every step (`checked` = `conflicts`
on three smoke instances) and runs `check_invariants` at every restart; with `--proof` the written proof is still
accepted.

Decisions and deviations (ARCH 8.1 amended in the same commit where marked):
- **Proof API** (ARCH 8.1 amended): originals are logged only through `add_original (id, kind, gate, lits)`, since an
  original is logged before reduction and is never the stored constraint when reduction shortens it; a `Constraint`
  overload would be dead code. `add_derived_empty` is `add_derived (id, kind, {}, chain)`, and the steps whose
  constraint is not stored take the id explicitly, so that `next_id` is consumed by the call site whether or not a proof
  is written (`unit-proof` checks this). `new_constraint` takes the id as its first argument. `strengthen` takes its
  fresh id from `next_id`; its M2 caller must renumber the same way without a proof.
- **`conclude`** is called by `found_empty`; `Proof` remembers the id of the last empty constraint it logged (an empty
  original, a reduction to empty, two complementary units, or an empty learnt constraint) and flushes every tracer.
  Steps for originals that arrive after the formula was decided are still logged, as by the old solver.
- **Default `Checker`** (ARCH 8.1 amended): connected by `Solver` with the first original (the prefix is then complete)
  if `--check`, or in builds with assertions if the caller connected no tracer and `ccminmode == 0`; never in mode 2.
  ARCH said "no QLRUP file"; `Solver` cannot tell tracers apart without RTTI, so a debug run with only `--trace` is not
  checked by default (use `--check`).
- **QDIMACS proof numbers**: `Solver::add_var` with proof number 0 now uses the user variable number (`miniqu.hpp`), so
  the trace names QDIMACS variables as the file does and the `Checker` works on QDIMACS. The encoder is unchanged.
- **Initial cubes** get a fresh id (`next_id++`) each time the buffer is filled; the `Checker` keeps each one live as a
  premise-free cube (they are never deleted: nothing in the old solver deleted them either).
- **`-trace` format** (ARCH 8.1 amended), intentional narrowings/changes for the coordinator to confirm: original
  constraints are written as premise-free lines (the old trace wrote none and its premises meant QDIMACS file positions;
  the new ids follow the proof, where a reduced original takes two ids and a tautology none, so a trace without them
  could not be interpreted); reductions of originals appear as derived lines; deletions are not written (as before);
  QCIR literals are proof numbers (the old trace used internal aliases 2g/2g+1 for gates and gave all QCIR clauses one
  id, i.e. it never worked for QCIR); the old `u` reduction lines existed only in debug builds of the old solver and
  are not reproduced.
- **Messages**: "Proofs are only available for QCIR input in modes 0 and 1." and "Proof logging does not support terms
  obtained from satisfying assignments." keep their text but go to stderr through `fatal` (`miniQU: error: ...`, exit 1)
  instead of the old `ERROR! ...` (the first one on stdout). Unopenable proof/trace files are fatal errors. The
  `--proof` check uses the input name, so it applies before parsing, like the old binary.
- `--check` disabling minimisation (ARCH 8.1, M1) is not implemented: minimisation does not exist yet (T09), and
  `--ccminmode` is still rejected by the app.

Notes for later tasks:
- T07: `mark_garbage` already emits the deletion; `reduce` needs no proof code. The model-cube buffer keeps its current
  id across collections (relocation copies the header).
- T08/T09: modes 1 and 2 must fill `chain` in their analyses; `connect_checker` already skips mode 2. Minimisation
  must either add its reasons to the chain (M2.3) or stay off while a tracer is connected.
- The `tests/regress.sh` smoke step is still vacuous after its first run (T05 note); the smoke numbers above come from a
  fresh `bench/run.py` run.


## M1-T07: learnt-database reduction (old policy), arena garbage collection, stress options, header measurement

Commits on `rewrite/cadical-style`: reduce and collect (`3c06676`), one-pass `check_invariants` and
`bench/header_measure.py`, and the 12-byte header with the documentation (the last commit of this task).

What exists now:
- `src/reduce.cpp`: `init_reduce`, `adjust_learnt_limit` (called by `learn` once per learnt constraint, port of the old
  `learntsize_adjust_*` counters: 100, then x1.5; `max_learnts` x1.1), `reducing`, `protect_reasons`/`unprotect_reasons`,
  `reduce`. Per kind, candidates are redundant, not a reason, glue > `tier1glue`; the worse half by (glue, size, both
  descending, then id ascending) goes through `mark_garbage` (proof `d` steps).
- `src/collect.cpp`: `collecting`, `garbage_collect` (ARCH 5.3 steps 1-4 plus the model buffer). `gcfrac = 0` collects at
  every safe point. `check_invariants` runs after every collection in builds with assertions and with `--check`.
- `reduceint` is accepted by the app (rejection removed); `profile` now prints with `--profile=N` (rows of profiles not
  wired yet, `search`, `analyze`, `propagate`, stay 0.00); `Profiles::enable` sets the level when the search starts.
- `check_invariants` also checks: no list or reason refers to a moved constraint, clean watch lists hold no garbage or
  moved constraint; the watch check is one pass over all lists (it was a list scan per constraint, quadratic in the list
  length; the asan gc stress row still needed the longer timeout below, so its effect was not measured separately).
- `assertions_enabled` moved to `contract.hpp` (was duplicated in `model.cpp` and `solver.cpp`).
- Tests: `unit-reduce` (schedule, both triggers, selection with tier1glue 2 and 0, reasons kept and unprotected,
  deletion steps through a recording tracer, collection after reduce by `gcfrac`), `unit-collect` (due, nothing wasted,
  deleted constraints, contents/ids/glue preserved, first-met constraints contiguous in watch order, reasons remapped,
  repeated collection gives identical references, units). Shared fixtures: `test/unit/database.hpp`, `recorder.hpp`
  (moved out of `proof.cpp`).

Decisions and deviations (ARCH amended in the same commit where marked):
- **Loop** (ARCH 7.1 amended): `reduce` does not end the iteration; the loop decides right after it. The old size
  trigger stays true after a reduction, so `else if (reducing ()) reduce ();` would reduce forever (found by reading the
  old `search`, which decides after `reduceDB`). The old behaviour (several halvings in a row at consecutive decisions
  while the trigger holds) is thereby kept.
- **`reduceint` schedule** (ARCH 9.1 amended): after a reduction `lim.reduce = conflicts + reduceint * reductions`
  (`reductions` already counting this one), not `+=`: the conflict counter can overshoot the limit by several
  conflicts and `+=` would then reduce in a burst. First fire at `conflicts >= reduceint`.
- **Half of the candidates**, not half of all learnt constraints of the kind as the old `reduceDB` (`learnt_counts / 2`
  counts the protected ones too). Learnt units are irredundant now, so they are not in the old trigger's count either.
  `max_learnts` starts at a third of the stored irredundant constraints (old: `num_clauses`).
- The constants of the old schedule (1/3, 1.1, 100, 1.5) are `constexpr` in `reduce.cpp`, not options: the owner's list of
  M1 options has none of them, and the stress options cover the events.
- **Model buffer**: not copied but allocated afresh (it is dead between two cubes); only its id is kept (ARCH 5.3 step 5).
- **Header** (ARCH 5.2 amended): see below, 12 bytes.

### Header measurement (ROADMAP M1.3, review S3)

`bench/header_measure.py`: baseline and new release binary, default options, `-verb=1`, one core each (cores 0-7, 8 in
parallel), `/usr/bin/time -v`; per instance propagations, conflicts, CPU seconds, props/s = propagations / (CPU time -
parse time), peak RSS. Groups: the ten largest by file size among the instances the baseline solved in
`baseline-t180`, and the ten of the 30 longest baseline runs with the most baseline propagations; an instance that either
binary does not solve in 180 s, or with different verdicts, is replaced by the next one. **A ratio measurement, not a
benchmark claim**: the two binaries take different search paths (different conflict counts, see tables), one run each.
Results: `bench/results/header-orig16/` (16-byte header), `bench/results/header-h12/` (12-byte header).

Geometric means of new/baseline, 16-byte header:

| group | instances | props/s | RSS | CPU time |
|---|---|---|---|---|
| largest | 10 | 1.004 | 0.818 | 0.802 |
| propagations | 10 | 1.290 | 1.093 | 0.939 |
| all | 20 | 1.138 | 0.946 | 0.868 |

12-byte header:

| group | instances | props/s | RSS | CPU time |
|---|---|---|---|---|
| largest | 10 | 1.018 | 0.801 | 0.792 |
| propagations | 10 | 1.301 | 1.076 | 0.931 |
| all | 20 | 1.151 | 0.928 | 0.859 |

Per instance, 16-byte header (the baseline columns of the second run are within a few percent of these):

| group | instance | props base | props new | props/s base | props/s new | ratio | conflicts base | conflicts new | RSS base MB | RSS new MB | RSS ratio | time base | time new |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| largest | 5.2-2.qcir | 542843356 | 651091731 | 7.34e+06 | 7.63e+06 | 1.04 | 10992 | 16941 | 2332 | 1882 | 0.81 | 80.8 | 90.0 |
| largest | 1.3.qcir | 21542927 | 6782483 | 4.31e+06 | 3.01e+06 | 0.70 | 313 | 120 | 1682 | 1341 | 0.80 | 9.5 | 5.5 |
| largest | 1.4.qcir | 21616315 | 6781054 | 4.33e+06 | 3.07e+06 | 0.71 | 300 | 120 | 1681 | 1340 | 0.80 | 9.4 | 5.5 |
| largest | 3.1.qcir | 193562586 | 394936826 | 7.17e+06 | 8.23e+06 | 1.15 | 425 | 739 | 1503 | 1189 | 0.79 | 31.0 | 50.8 |
| largest | 11.1.qcir | 147907027 | 162470145 | 7.25e+06 | 7.96e+06 | 1.10 | 1193 | 1281 | 631 | 491 | 0.78 | 22.0 | 21.5 |
| largest | 9.1.qcir | 7021615 | 9900703 | 5.4e+06 | 6.31e+06 | 1.17 | 326 | 187 | 475 | 384 | 0.81 | 2.5 | 2.4 |
| largest | 5.2-1.qcir | 250482366 | 110053225 | 8.01e+06 | 9.15e+06 | 1.14 | 31558 | 12637 | 462 | 373 | 0.81 | 32.4 | 12.8 |
| largest | 10.1.qcir | 13162569 | 5175879 | 5.7e+06 | 5.28e+06 | 0.93 | 637 | 251 | 413 | 322 | 0.78 | 3.3 | 1.6 |
| largest | 10.2.qcir | 3463109 | 7165204 | 4.68e+06 | 6.02e+06 | 1.29 | 204 | 407 | 413 | 322 | 0.78 | 1.7 | 1.8 |
| largest | 8.1.qcir | 31011476 | 31816864 | 1.07e+07 | 1.08e+07 | 1.01 | 723 | 1127 | 165 | 177 | 1.08 | 3.5 | 3.3 |
| propagations | klieber2017q-066-16-eq.qcir | 2861859791 | 3520581348 | 2.68e+07 | 3.49e+07 | 1.30 | 3343658 | 4048979 | 11 | 11 | 1.06 | 106.6 | 100.8 |
| propagations | test_5_5_domino.pg-15.qcir | 2299480813 | 2785816494 | 1.44e+07 | 1.91e+07 | 1.33 | 13378891 | 15257634 | 11 | 11 | 1.01 | 159.4 | 145.5 |
| propagations | klieber2017q-086-21-t1.qcir | 2266775483 | 3073768426 | 2.81e+07 | 3.87e+07 | 1.38 | 1869484 | 2524968 | 10 | 11 | 1.07 | 80.7 | 79.4 |
| propagations | klieber2017q-076-19-eq.qcir | 1892686950 | 1958511289 | 2.76e+07 | 3.28e+07 | 1.19 | 1858429 | 2107057 | 14 | 14 | 1.00 | 68.5 | 59.8 |
| propagations | klieber2017q-084-21-eq.qcir | 1777041076 | 1823859970 | 2.17e+07 | 3.06e+07 | 1.41 | 2157859 | 2177921 | 14 | 16 | 1.10 | 81.8 | 59.5 |
| propagations | bt-2x5_17.ig.qcir | 1717642508 | 1968348491 | 1.5e+07 | 1.73e+07 | 1.15 | 2097002 | 2424041 | 29 | 31 | 1.05 | 114.3 | 113.6 |
| propagations | bt-3x4_19.ig.qcir | 1617324173 | 2326751094 | 1.66e+07 | 2.02e+07 | 1.22 | 1473858 | 2125027 | 31 | 32 | 1.03 | 97.3 | 114.9 |
| propagations | klieber2017q-100-25-t1.qcir | 1604417303 | 2478228150 | 2.84e+07 | 3.97e+07 | 1.40 | 1214171 | 1808393 | 11 | 12 | 1.14 | 56.5 | 62.4 |
| propagations | klieber2017q-076-19-t1.qcir | 1603826840 | 1486807220 | 2.82e+07 | 3.8e+07 | 1.35 | 1539807 | 1411458 | 8 | 8 | 1.00 | 56.8 | 39.1 |
| propagations | amba2f9n.sat.qcir | 1569742266 | 2107432587 | 2.26e+07 | 2.74e+07 | 1.21 | 1480707 | 2019764 | 19 | 29 | 1.56 | 69.4 | 76.9 |

Per instance, 12-byte header:

| group | instance | props base | props new | props/s base | props/s new | ratio | conflicts base | conflicts new | RSS base MB | RSS new MB | RSS ratio | time base | time new |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| largest | 5.2-2.qcir | 542843356 | 651091731 | 7.39e+06 | 7.87e+06 | 1.07 | 10992 | 16941 | 2332 | 1847 | 0.79 | 80.3 | 87.4 |
| largest | 1.3.qcir | 21542927 | 6782483 | 4.28e+06 | 3.07e+06 | 0.72 | 313 | 120 | 1681 | 1316 | 0.78 | 9.5 | 5.5 |
| largest | 1.4.qcir | 21616315 | 6781054 | 4.28e+06 | 3.08e+06 | 0.72 | 300 | 120 | 1681 | 1315 | 0.78 | 9.5 | 5.4 |
| largest | 3.1.qcir | 193562586 | 394936826 | 7.1e+06 | 8.41e+06 | 1.18 | 425 | 739 | 1503 | 1167 | 0.78 | 31.1 | 49.7 |
| largest | 11.1.qcir | 147907027 | 162470145 | 7.23e+06 | 8.08e+06 | 1.12 | 1193 | 1281 | 631 | 482 | 0.76 | 22.0 | 21.2 |
| largest | 9.1.qcir | 7021615 | 9900703 | 5.49e+06 | 6.6e+06 | 1.20 | 326 | 187 | 475 | 377 | 0.79 | 2.5 | 2.3 |
| largest | 5.2-1.qcir | 250482366 | 110053225 | 7.96e+06 | 8.95e+06 | 1.12 | 31558 | 12637 | 462 | 366 | 0.79 | 32.6 | 13.1 |
| largest | 10.1.qcir | 13162569 | 5175879 | 5.72e+06 | 5.28e+06 | 0.92 | 637 | 251 | 413 | 316 | 0.76 | 3.3 | 1.6 |
| largest | 10.2.qcir | 3463109 | 7165204 | 4.62e+06 | 6.07e+06 | 1.32 | 204 | 407 | 413 | 316 | 0.77 | 1.8 | 1.8 |
| largest | 8.1.qcir | 31011476 | 31816864 | 1.08e+07 | 1.07e+07 | 1.00 | 723 | 1127 | 165 | 169 | 1.03 | 3.5 | 3.3 |
| propagations | klieber2017q-066-16-eq.qcir | 2861859791 | 3520581348 | 2.6e+07 | 3.51e+07 | 1.35 | 3343658 | 4048979 | 11 | 11 | 0.99 | 110.1 | 100.4 |
| propagations | test_5_5_domino.pg-15.qcir | 2299480813 | 2785816494 | 1.44e+07 | 1.89e+07 | 1.31 | 13378891 | 15257634 | 11 | 11 | 1.00 | 159.3 | 147.1 |
| propagations | klieber2017q-086-21-t1.qcir | 2266775483 | 3073768426 | 2.82e+07 | 3.86e+07 | 1.36 | 1869484 | 2524968 | 10 | 11 | 1.15 | 80.2 | 79.7 |
| propagations | klieber2017q-076-19-eq.qcir | 1892686950 | 1958511289 | 2.76e+07 | 3.43e+07 | 1.24 | 1858429 | 2107057 | 14 | 16 | 1.10 | 68.7 | 57.1 |
| propagations | klieber2017q-084-21-eq.qcir | 1777041076 | 1823859970 | 2.28e+07 | 3.09e+07 | 1.36 | 2157859 | 2177921 | 14 | 15 | 1.08 | 78.1 | 59.1 |
| propagations | bt-2x5_17.ig.qcir | 1717642508 | 1968348491 | 1.49e+07 | 1.73e+07 | 1.16 | 2097002 | 2424041 | 29 | 31 | 1.04 | 115.0 | 113.7 |
| propagations | bt-3x4_19.ig.qcir | 1617324173 | 2326751094 | 1.65e+07 | 2.04e+07 | 1.24 | 1473858 | 2125027 | 31 | 33 | 1.06 | 98.2 | 114.1 |
| propagations | klieber2017q-100-25-t1.qcir | 1604417303 | 2478228150 | 2.83e+07 | 4.01e+07 | 1.42 | 1214171 | 1808393 | 11 | 12 | 1.14 | 56.7 | 61.8 |
| propagations | klieber2017q-076-19-t1.qcir | 1603826840 | 1486807220 | 2.83e+07 | 3.84e+07 | 1.36 | 1539807 | 1411458 | 8 | 8 | 1.01 | 56.7 | 38.7 |
| propagations | amba2f9n.sat.qcir | 1569742266 | 2107432587 | 2.17e+07 | 2.69e+07 | 1.24 | 1480707 | 2019764 | 19 | 23 | 1.22 | 72.3 | 78.4 |

Reading: propagation speed is not below the baseline (geometric mean 1.14 / 1.15, the two large `1.3`/`1.4` instances are
0.70 / 0.72: 2.2 million gates parsed, 100-300 conflicts, so the number is dominated by the first propagations and the
cold arena). The first RSS result had one instance clearly above the baseline that parsing does not explain (`amba2f9n`
1.56; with a 0.5 s and 3 s timeout the new binary's RSS is below the baseline's, so the excess grows during the search),
so by the rule of the task the 12-byte variant was implemented (`constraint.hpp` only, plus the constants in
`unit-constraint`) and measured: props/s 1.151 vs 1.138 (the difference is noise), RSS ratios lower on every instance
(amba 1.22, geometric means 0.928 vs 0.946 and 1.076 vs 1.093 on the propagation group). **Decision: keep the 12-byte
header**, since it is no slower and smaller. Costs: constraint size at most 2^27-1 literals (fatal error beyond),
ids below 2^44 (asserted), glue saturating at 16383, 6 reserved bits (M2 needs 3). The remaining RSS excess on the
long, small-memory runs is not the header; likely sources are the different learnt-database trajectory (the new binary
has up to 40% more conflicts there) and `std::vector` watch lists growing by doubling; not investigated further.

### Acceptance (all with `taskset -c 0-63`; logs in `/home/ec2-user/miniqu-work/logs/t07/`; R = release, A = asan)

| command | result |
|---|---|
| build + `ctest` in release, debug, asan, release-clang | no warnings (besides the known `lto-wrapper` note); 29/29 tests pass each |
| `tests/regress.sh -S -s 1:300 -M default,gc,restart R` (proofs checked by Lean) | PASSED: 0 wrong verdicts, 0 rejected proofs, 0 timeouts in any row, 300 proofs checked per row; gc row: reductions 98%, reduced.clause 93%, reduced.cube 91%, collections 98%, relocated 98% of the finished search instances (default row: the old trigger reduces on 58%) |
| `tests/regress.sh -S -s 1:100 -M default,gc,restart -t 90 A` | PASSED: 0 sanitizer reports, 100 proofs checked per row, `checked` (internal replay) = conflicts; gc row: reduced.clause 92%, reduced.cube 92%, collections 96%, relocated 96% |
| `tests/fuzz_qdimacs.sh R 1 300 --reduceint=2 --tier1glue=0 --gcfrac=0` (R = the release binary) | 0 failures, 0 timeouts, 600 instances agreed |
| same with A, seeds 1 100 | 0 failures, 0 timeouts, 200 instances agreed |
| smoke set, `bench/run.py --tag m1-t07-smoke --timeout 60 --jobs 32 --cores 64-95 --proof-check` | 31/33 solved (the same two `jctc` instances time out as in T05/T06; baseline 33/33), verdicts equal `bench/smoke-expected.csv`, 31/31 proofs accepted; total wall of the 31 common instances 29.6 s vs 30.5 s for the baseline; `bench/results/m1-t07-smoke/` |

Notes:
- The A run of the `gc` row needs a longer solver timeout than the default 20 s: with `--reduceint=2 --tier1glue=0` the
  search takes 30 times more conflicts on some instances (seed 60: 1751 conflicts by default, 54886 with the stress
  options), and asan makes that 7-13 times slower than the release build (3.3 s release, 29 s asan, 43 s with the
  invariant check after each of its 234 collections). With the default 20 s, 6-7 of 50 search instances timed out in A
  (limit 2%); with `-t 90` none do, and in R none do at 20 s. The tests were not changed; if the 20 s limit is meant to
  hold for A too, the stress `reduceint` or the timeout of A runs has to change (coordinator).
- `reduced.cube` reaches 91-92% in the gc row, so the corpus was not extended.
- `jctc1-pass`, `jctc9-pass` still time out at 60 s (as before this task: not caused by reduction).

Notes for later tasks:
- T08: `adjust_learnt_limit` is called from `learn` only; dependency learning has no learnt constraint and must not call
  it. Dependencies need no Ref, so the safe-point rule of the collector is unaffected.
- T09/M2: tiers replace the `tier1glue` test in `reduce`; the loop shape of ARCH 7.1 (reduce, then decide) stays.
- The model buffer is reallocated by every collection (it is `prefix.size ()` literals).

## M1-T08: dependency learning; mode 1 (QU-resolution) and `--legacyanalyze` (worker, 2026-11-22)

What exists now (commits 59774b0, f6aa784):
- `src/depend.cpp`, `struct Depend depend` (one member of `Internal`): per variable the dependency list `on[v]` (first
  entry watched), the reverse lists `watching[u]`, the lazy trail head `depend.propagated` processed by
  `update_dependency_watches ()` before each decision, `record_dependency`, `reset_dependencies`,
  `resetting_dependencies`, `stays_eligible`, `waits_for_dependency`. Counters `dependencies`, `depresets`.
- `decide.cpp`: with `--dl` one heap (`heaps[0]`, `heap_of (v)`) over all decision variables; popped variables that are
  assigned or ineligible are dropped, as in the old `pickBranchLit`; they come back when their watch is assigned
  (`update_dependency_watches`) or when a backtrack leaves the watch assigned on a level <= the new level (old
  `cancelUntil`). `Block::unassigned` stays maintained and terminates the search. Without `--dl` unchanged (eligibility
  asserted).
- `analyze.cpp`: `analyze ()` counts the conflict and dispatches (mode 1 or `--legacyanalyze` -> `analyze_qu`, else
  `analyze_q`); dependency outcome -> `learn_dependency (x, y)` (backtrack to `level (x) - 1`, record). No constraint, no
  proof step, no decay, no learnt-limit adjustment.
- `src/analyze_qu.cpp`: port of the old `analyze` (`LevelAnalyzer`, one object per round): resolvent per block
  (`LevelAnalysis qu`), level-by-level resolution, secondary pivots in mode 1, the kind switch as a loop (porting
  note 4: the switched variable is treated as reason-less and taken as it occurs in its reason; a new chain per round as
  the old `premise_ids`), dependency outcome. In mode 1 the asserting literal may be secondary (verified against the old
  propagate: conflict completion is `mode == 0` only, so mode 1 has none).
- `app.cpp` accepts `--dl`, `--mode=1`, `--legacyanalyze` (rejects only `mode > 1`, `ccminmode > 0`).
- Tests: `unit-depend` (watch movement, heap leave/re-enter, backtrack re-insertion, reset schedule, a learnt
  dependency in mode 0, whole runs prefix order vs `--dl` with the known verdict), `unit-analyze_qu` (universal pivot
  for a clause, existential pivot for a cube, kind switch, switch ending in a dependency, legacy mode 0).

Edits outside the new files (ARCH 3.6): `backtrack.cpp` (re-insert into `heap_of (v)`, only if `stays_eligible` under
`--dl`; reset `depend.propagated`), `bump.cpp` (`heap_of`), `heap.hpp` (`remove`, for `record_dependency`),
`check.cpp` (an unassigned decision variable may wait for its dependency; each watch is listed once), `internal.cpp`
(`--dl` single heap; the reset after the restart, as in the old `solve_`), `learn.cpp` (only `learn_dependency` and an
assertion). `propagate.{hpp,cpp}` and `assign.cpp` are unchanged.

Decision (deviation from the old code): **a dependency reset is skipped when no constraint was learnt since the last
reset** (`resetting_dependencies`). A dependency counts as a conflict for the restart schedule, so the `restart-dl` row
(restart after every conflict, `depreset=1`) repeated decision, dependency, restart, reset forever: 137 of 150 search
instances timed out before, 6 after. With the default `depreset=20` a reset without any learnt constraint in 19
restarts is practically impossible, so the default behaviour is the old one.

### Acceptance (`taskset -c 0-63`; logs `/home/ec2-user/miniqu-work/logs/t08/`; R release, A asan; binary f6aa784)

| command | result |
|---|---|
| build + `ctest`, release, debug, asan, release-clang | no warnings; 31/31 tests pass in each |
| `tests/regress.sh -S -s 1:300 -M default,dl,mode1,mode1-dl,legacy,noearly,gc,gc-dl,gc-mode1,restart,restart-dl,restart-mode1-dl R` | 0 wrong verdicts (incl. cross-configuration), 0 rejected proofs; coverage holds (`dependencies` 92-99% in the dl rows, `depresets` 99-100% in the restart dl rows); proof checks timed out (warning only): mode1 3, mode1-dl 10, noearly 3, gc-mode1 14. **FAILED on stress timeouts**: gc-mode1 44/150, restart-dl 6/150, restart-mode1-dl 63/150 (limit 2%); see below |
| same rows, `-s 1:100 -t 90` on A | 0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports; stress timeouts gc-mode1 19/50, restart-dl 3/50, restart-mode1-dl 20/50 (same failure) |
| `tests/fuzz_qdimacs.sh R 1 300 OPT`, OPT `-dl`, `-mode=1`, `-mode=1 -dl`, `-legacyanalyze` | 0 failures, 0 timeouts, 600 agreed each (`-dl`, `-mode=1 -dl` rerun on f6aa784) |
| same on A, seeds 1 100 | 0 failures; timeouts: `-dl` 1, `-mode=1` 2, `-mode=1 -dl` 17, `-legacyanalyze` 0 |
| smoke `bench/run.py ... --args=-dl` / `--args=-mode=1`, `--timeout 60 --proof-check` | 31/33 each, verdicts equal `bench/smoke-expected.csv`, 31/31 proofs accepted; the two `jctc` instances time out as in T05-T07; `bench/results/m1-t08-smoke-dl/`, `m1-t08-smoke-mode1/` |
| port fidelity: conflicts R / baseline, search seeds 151-200 (`bench/results/m1-t08-fidelity/`) | `-dl`: geometric mean 1.14, min 0.21, max 33.1 (the large ratios are on instances where the baseline needs < 300 conflicts); `-mode=1`: geometric mean 0.98, min 0.33, max 3.16; all 100 verdicts agree |

### Stress timeouts: measured, not caused by the port (coordinator decision needed)

Search seeds 151-300, 20 s, release, 16 parallel on cores 0-63 (`/home/ec2-user/miniqu-work/stress-t08/`):

| configuration | new | baseline |
|---|---|---|
| restart every conflict, `-dl` (new `--depreset=20`, baseline `-rinc=1.000001`, which keeps the interval 1) | 6 | 6 (the same six seeds: 155 174 184 199 234 280) |
| same with `--depreset=1` (the matrix row; the baseline cannot) | 6 (60 s: 3) | - |
| restart every conflict, `-mode=1 -dl`, `depreset=20` | 31 | 28 |
| same with `--depreset=1` (the matrix row) | 63 (60 s: 49) | - |
| `-mode=1 -dl` default | 1 | 6 |
| `-mode=1` default / `-mode=1 --tier1glue=0` | 0 / 0 | - |
| `-mode=1 --reduceint=2` / gc-mode1 row | 35 / 44 (60 s: 18) | - (no `reduceint` in the baseline) |
| gc row (mode 0) | 0 | - |

Reading: restart-dl and restart-mode1-dl time out like the baseline under the closest configuration it has; mode 1
needs roughly 2-1000 times the conflicts of mode 0 on the same instances (baseline too, e.g. seed 279: mode 0 4, mode
1 2908 baseline / 2978 new), and with a reduction every two conflicts it keeps too little. So the three stress rows
are too hard for the 2% limit by design, not through a lost behaviour. Not changed (it would weaken a test): the rows
in `tests/matrix.txt`. Options for the coordinator: a larger `reduceint` for gc-mode1 (e.g. 20), restarts every few
conflicts (`--rinc` > 100) for the restart dl rows, or a higher timeout limit for these rows.

Notes for later tasks:
- `ARCH 7.4`: dependencies must also be reset when inprocessing fixes or eliminates a decision variable
  (`reset_dependencies` puts every unassigned decision variable back into the heap).
- The kind switch relies on later rounds only seeing variables assigned before the switched one; if analysis ever
  becomes non-chronological (e.g. chronological backtracking), the old code's clearing of the reason must come back.

## M1-T09: mode 2 (long-distance Q-resolution) and learnt minimisation (worker, 2026-11-22)

Commits 1762520 (code and unit tests), cb42d73 / 5305566 ('minimized' counter), 4ffbcc2 (no tracer in mode 2; ARCH
6.3, 7.5, 8.2 amended), 59b1a69 (analyze_ldq scans as the old code), and this STATUS commit. Final binary: 59b1a69.

What exists now:
- `src/propagate_ldq.cpp`: `propagate_ldq_watches<K>` (port of `propagateLDQ`, both kinds through `kval`) and the trail
  driver `propagate_ldq`. Prefix-aware unit rule, conflict when no primary literal is left (no completion), watches on a
  primary literal and a primary or left secondary one, watches of position 0 move, stale entries are dropped when met.
  `attach` is unchanged: originals are watched by their two leftmost literals and learnt constraints by the positions
  `analyze_ldq` chooses, as in the old code.
- `src/analyze_ldq.cpp`: port of `analyzeLDQ` as a class (no goto); resolvent per block as literals with per-literal
  positions (`LongDistanceAnalysis ldq`), asserting literal and second watch as `getAssertingVarLDQ`/`isAsserting`,
  dependency outcome as `getBlockedVariable`, empty constraint at the root. `learn.cpp` has `learn_watched` (positions 0/1
  set by the caller) and `learn_empty`; `learn` (modes 0/1) uses them.
- `src/minimize.cpp`: `minimize (lits, kind)` for ccminmode 1 (basic), 2 (deep, `litRedundant` with an explicit
  stack), 3 (bounds with reduction, recursion cut at depth 1000), state in `Minimizer minimizer`. Called from `learn`
  before `qreduce` for `analyze_q` and `analyze_qu` (the old `finishLearnt` callers); never for long-distance resolvents.
  Off while any tracer is connected (`Internal::minimizing`); `solve` prints one `c warning` line when `--ccminmode` is
  set but a tracer (explicit `--check`, `--proof`, `--trace`) disables it. The default Checker of debug/asan builds is not
  connected when ccminmode > 0 (was already so in `solver.cpp`).
- Mode 2 and proofs: `--proof` rejected (as before), `--trace` rejected too (see decisions), `Solver` REQUIREs that no
  tracer is connected in mode 2, the Checker is not connected, `--check` runs `check_invariants` (restarts, after GC).
  QDIMACS initial cubes are still verified by `check_model_cube` in debug/asan and with `--check`.
- `collect.cpp`: in mode 2 garbage is removed from every watch list before relocation (`Watches::clean_every_list`):
  a stale entry of a deleted constraint can sit in a list deleting did not smudge, and the relocator must not copy it.
- `check.cpp`: in mode 2 clean lists may hold stale entries of deleted constraints; a constraint whose watches are as
  mode 2 keeps them must not be long-distance unit once propagation is complete (originals before their first watch
  move are exempt, see below); reasons are checked on their primary literals only.
- The app rejects no option as "not implemented" any more. The obsolete death test of mode 2 in `unit-propagate` is gone.
- Tests: `unit-propagate_ldq` (both kinds: an unassigned secondary literal to the left blocks and its assignment then
  propagates, a secondary literal to the right does not block, conflict with an unassigned secondary literal, a stale
  entry created and dropped, a stale entry of a deleted constraint accepted by `check_invariants` and dropped by GC),
  `unit-analyze_ldq` (both kinds: the long-distance resolvent (1 4 3 -3) with its watches, backjump and glue; a
  dependency; the empty constraint), `unit-minimize` (each ccminmode on a literal removable by basic minimisation, one
  only by deep, one only with reduction; the decision literal kept; off with a tracer).

Decisions and deviations (ARCH amended in 4ffbcc2):
- **Duplicate watch entry not ported**: the old code compares `first != c[h]` after overwriting `c[h]`, so the test is
  always true and a second entry is pushed when the old position 0 comes back as position 1; the port compares with the
  new position-1 literal. Only affects the number of list entries.
- **`--trace` rejected in mode 2** ("Traces are only available in modes 0 and 1."): `Proof` requires antecedents and
  `conclude` an empty-constraint step; the old solver accepted `-trace` in mode 2 but traced no learnt constraint, so
  its trace was incomplete anyway. The coordinator may prefer premise-free steps instead (needs a change in `Proof`).
- **Minimisation off for all three modes under a tracer**: the old code disabled only ccmin-mode 3 under a proof/trace
  and ran modes 1/2 regardless (with proofs whose chains miss the removed literals); the M1 rule of the task is applied.
- **`stats.minimized`** counts literals minimisation removes beyond those the following `qreduce` removes anyway. The
  resolvents of `analyze_q` still hold reducible secondary literals (the old analysis reduced them inside), and in
  ccminmode 3 minimisation removes such literals itself; counting plain removals made ccminmode 3 look 5x stronger than
  2 on identical searches. The definition matches the old `conflict literals ... (x % deleted)`.
- `analyze_ldq` scans only primary blocks for the asserting literal and only secondary blocks for blocked literals, as
  the old helpers do; the first version scanned all literals and spent 90% of a mode-2 `-dl` run there (seed 174: 21.5 s
  vs 10.3 s after, baseline 10.9 s, same conflicts).
- Observation (not changed, port of the old behaviour): originals start watched by their two leftmost literals, which may
  both be secondary or a primary one with a secondary one right of it; until a watch moves, mode 2 can miss a unit or a
  conflict there (never produce a wrong one). A mode-2-aware initial watch choice is a possible M2 improvement.

### Acceptance (`taskset -c 0-63`; logs `/home/ec2-user/miniqu-work/logs/t09/`; R release, A asan)

| command | result |
|---|---|
| build + `ctest`, release, debug, asan, release-clang (59b1a69) | no warnings in `src/`/`test/unit/`; 34/34 tests pass in each |
| `tests/regress.sh -S -s 1:300 -M all R` (binary 5305566; Lean checking on rows with proofs) | 0 wrong verdicts incl. cross-configuration, 0 rejected proofs; coverage holds in every row (`minimized` 99% in ccmin3 and dl-ccmin3; gc-mode2 reductions/reduced/collections/relocated 88-98%). Proof checks timed out (warning only): mode1 3, mode1-dl 10, noearly 3, gc-mode1 14. Stress failures: only the three known rows of T08 (gc-mode1 44/150, restart-dl 6/150, restart-mode1-dl 64/150). Normal-row timeouts: mode1-dl 1, mode2-dl 8, noearly 37 |
| same rows mode2, mode2-dl, gc-mode2 rerun on 59b1a69 (R, 1:300) | PASSED: 0 wrong verdicts, gc-mode2 0 timeouts, mode2-dl 1 timeout (was 8 before 59b1a69) |
| `tests/regress.sh -S -s 1:100 -M all -t 90 A` (binary 4ffbcc2) | 0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports, coverage holds. Stress failures: the three known rows (gc-mode1 19/50, restart-dl 3/50, restart-mode1-dl 20/50) **and gc-mode2 2/50** (see below) |
| mode2, mode2-dl, gc-mode2 rerun on 59b1a69 (A, 1:100, -t 90) | 0 wrong verdicts, 0 sanitizer reports; gc-mode2 2/50 timeouts (same two seeds), mode2-dl 1 |
| `tests/fuzz_qdimacs.sh R 1 300 OPT`, OPT '', -dl, -mode=1, -mode=2, -mode=2 -dl, -ccminmode=2, -ccminmode=3, -mode=2 --reduceint=2 --tier1glue=0 --gcfrac=0 | 0 failures, 0 timeouts, 600 agreed each (4ffbcc2; the three mode-2 options rerun on 59b1a69: same) |
| same on A, seeds 1 100 | 0 failures; timeouts (counted only): -dl 1, -mode=1 2, -mode=2 1, -mode=2 -dl 10, gc mode 2 2, others 0 (59b1a69 for the mode-2 options: same counts) |
| smoke `bench/run.py --args=-mode=2` / `--args=-ccminmode=3`, `--timeout 60`, cores 64-95 | 31/33 each, verdicts equal `bench/smoke-expected.csv` (the two `jctc` instances time out as in T05-T08); baseline `-mode=2` 33/33, common-instance wall 145.4 s new vs 150.8 s baseline; `bench/results/m1-t09-smoke-mode2/`, `m1-t09-smoke-ccmin3/`, `m1-t09-smoke-baseline-mode2/` |
| port fidelity, search seeds 151-200, conflicts new / baseline (`bench/results/m1-t09-fidelity/`) | `-mode=2` vs `-mode=2`: geometric mean 1.011 (min 0.09, max 6.56); `-ccminmode=3` vs `-ccmin-mode=3`: 1.045 (0.16, 8.00); default: 1.114; all 150 verdicts agree |
| `-mode=2 -dl` on search seeds 151-300, 20 s, new vs baseline | 0 disagreements; timeouts new 1 (seed 280), baseline 2 (199, 280); conflict ratio geometric mean 1.118 over 148 (`mode2-dl-timeouts.csv`) |
| learnt-literal reduction by minimisation (45 of those instances with >= 100 baseline conflicts) | ccminmode 3: share of literals removed by minimisation, new `minimized / (minimized + learnedlits)` mean 11.3% median 10.7%, baseline `% deleted` mean 9.6% median 9.9%; baseline with ccmin-mode 0 deletes 0% (its analysis output is already reduced) |

### gc-mode2 in asan: 2 of 50 stress timeouts (coordinator decision needed, like T07/T08)

Search seeds 99 and 60 (`/home/ec2-user/miniqu-work/t09/gcm2/times.txt`): release 14.7 s / 12.6 s, asan 99 s / 89 s
(limit 90 s), baseline `-mode=2` 0.3 s. The stress options cause it, not mode 2: conflicts with `-mode=2` 2274 / 1809
(baseline 1718 / 1731), with `-mode=2 --reduceint=2` 50528 / 25862, with the full gc-mode2 row 134538 / 130184; the mode-0
gc row on the same seeds needs 62402 / 54886 (seed 60 is the T07 example). In R the row has 0 timeouts. Not changed: the
row, the timeout. Options are those of T07/T08 (larger `reduceint` for the gc rows, or a longer A timeout).

Open points carried over: the three stress rows of T08 (gc-mode1, restart-dl, restart-mode1-dl) still exceed 2% in R and A,
unchanged by this task; awaiting the coordinator.
