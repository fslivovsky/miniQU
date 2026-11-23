
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

## M1 gate tooling (M1-T10, worker, 2026-11-22)

Commits 2b202aa, be574cc, fd96d51, 468e0b1, 31cb4be, feeebf6, dceacd0 and this STATUS commit. No solver source
changed (`src/` is as in 7555d53); the gate was run on that code. The full benchmark runs (P0.4, the M1 gate runs)
were **not started**, as instructed; only 10-instance, 20 s rehearsals of every command form.

### What exists now

- `bench/run.py`: defaults `--jobs 48 --mem-gb 16 --cores 64-127`; `--seed S` (recorded in `meta.json`, `{seed}` in
  `--args`, `--seed-args` appended only for S > 0); `-verb=1` and per-instance counters in `stats.csv`
  (`instance,counter,value`: the `c stat` lines, or conflicts/decisions/propagations/restarts parsed from the baseline);
  `meta.json` with jobs, mem_gb, cores, timeout, seed, hash of the instance list; resume refused when any of these
  differs; `--proof-max-solve-sec` up to the timeout, `--proof-solve-timeout` (default 2 x timeout), `--proof-mem-gb 32`,
  `--proof-max-gb 8` (status `too_large`, via `prlimit --fsize`), trim-and-retry with `qlrup-trim` on checker timeout or
  memout, `{proof}` in `--args` for timed proof-on runs (`--trim-size` records the trimmed size), at most 6 proof jobs
  when `--proof-timeout >= 3600`; core dumps disabled (a killed 8 GB proof run otherwise sat in the core dump until the
  timeout). Exit status 1 only for errors and rejected proofs; coverage gaps are printed as such.
- `bench/compare.py --paired A_TAGS -- B_TAGS [--force]` (with `bench/paired.py`, `bench/benchlib.py`): refusal
  (exit 3) or `# NOT COMPARABLE`; discrepancies first; Δ with the 10000-resample percentile bootstrap (fixed generator
  seed), the sign test with margin max(1 s, 10% of the smaller score), verdict words and the "not worse" line per ROADMAP
  0.3, per-seed table and noise band, gained/lost in a majority of seeds, per-family table, largest differences, peak
  memory (instances solved by both in every seed where B exceeds A by more than 10%), proof coverage table. The plain
  mode gained the coverage table too. `bench/fidelity.py`, `bench/overhead.py` (proof overhead report, not in the spec
  but needed by the gate), `bench/test_compare.py` (9 tests: identical arms, 20% faster arm, slower arm, mismatched
  limits and seeds refused, discrepancy first, coverage table, binomial, bootstrap), run by ctest.
- `tests/check_cert.py`, `tests/fuzz_cert.sh` (tiny + search corpus instance, tiny + large QDIMACS per seed), see below.
- Root `CMakeLists.txt`: `miniQU-old` and every reference to `minisat/` removed (`make r` still builds the old tree
  from `minisat/`; the baseline binary is untouched); ctest now also runs `bench/test_compare.py`,
  `tests/test_qcir_eval.py` and the 20-seed `regress.sh -M default,dl`. Root `README.md` rewritten for the new tree.
- Rehearsals (work dir `/home/ec2-user/miniqu-work/rehearsal*`, not committed): every form of the README block on the 10
  instances of `/home/ec2-user/miniqu-work/ten.txt` with `--timeout 20`: seeds for new and baseline, `-dl`, modes 1/2,
  seed-0 coverage with `--proof-timeout 3600`, proof-on runs with `--trim-size`, `overhead.py`, `fidelity.py`, paired
  compare; trim-and-retry (a 3 s checker limit: 9.1.qcir checked after trimming, 1.57 MB of 27.9 MB) and `too_large`
  (`--proof-max-gb 0.005`). The rehearsal found one harness bug (the `stats.csv` header written twice when jobs finish
  at the same time; fixed in 468e0b1).

### Bugs found in test tooling (fixed; no solver bug found)

1. `tests/qcir_eval.py` did not know `xor`, `ite` or `free`: an `xor` gate was evaluated as `or`. Three "invalid
   certificates" of the first `check_cert` run (tiny seeds 399, 243, 34, all with xor/ite) were this. Fixed, with
   `tests/test_qcir_eval.py`. (`fuzz.sh`/`regress.py` compared `qcir_fuzz` instances against the generator's own
   expected verdict, so no earlier result depended on it; `qcir_gen` instances have no xor/ite.)
2. `tests/regress.py` checked the proof file of a proof run that had been **killed by the timeout**: a truncated file
   is rejected by the checker ("unexpected end of file"), so a stress run at the 20 s limit gave two false "proof
   rejected" failures (restart-mode1-dl, search seeds 1137 and 1987: 19.8 s without proof, over 20 s with). Both
   proofs verify with a longer limit (`VERIFIED FALSE`, 87.5 MB and 86.2 MB). Now a timed-out proof run is "skipped"
   (counted: "proof runs unfinished").
3. `tests/regress.py` smoke test: `bench/run.py` resumes, and the smoke directory of an old row was reused, so a smoke
   "pass" could consist of the results of an older binary. The directory is removed first. (With the new harness, which
   refuses to resume a run with unknown metadata, the first gate attempt failed all 17 smoke rows with
   "cannot resume": that is how this was found.)

### Parity fuzz (M1.9), release binary 7555d53 sources, cores 0-63, 16 jobs

`tests/regress.sh -j 16 -s 1:2000 -M all R` (log `/home/ec2-user/miniqu-work/logs/m1-gate-release.log`; 1000 tiny + 1000
search instances per row, tiers as in `regress.sh`). Every row: **0 wrong verdicts** (tiny against the evaluator,
search against the baseline, and across all 17 rows), **0 rejected proofs** (apart from the two false alarms of bug 2),
coverage assertions hold in every row. That log's smoke part failed because of bug 3; the smoke rows were rerun alone
(`tests/regress.sh -F ... -M all R`, log `m1-gate-release2.log`): **0 failures in all 17 rows**.

| row | instances | proofs accepted | checker timeouts | solver timeouts |
|---|---|---|---|---|
| default, dl, ccmin3, dl-ccmin3, legacy, gc, gc-dl, restart | 2000 | 2000 | 0 | 0 |
| mode1 | 2000 | 1996 | 4 | 0 |
| mode1-dl | 2000 | 1941 | 49 | 10 |
| mode2, mode2-dl, gc-mode2 | 2000 | (no proofs in mode 2) | - | 0, 5, 3 |
| noearly | 2000 | 1759 | 19 | 222 |
| gc-mode1 (stress) | 2000 | 1620 | 63 | 317 |
| restart-dl (stress) | 2000 | 1964 | 0 | 36 |
| restart-mode1-dl (stress) | 2000 | 1641 (+2 false alarms, verified by hand) | 0 | 357 |

Proof coverage in that run = accepted / (accepted + checker timeouts + proofs not attempted because the plain run
timed out); there are no other categories in `regress.sh`. The three stress rows (gc-mode1, restart-dl,
restart-mode1-dl) exceed the 2% stress timeout limit as in T08 (**open coordinator decision, not changed**).

`tests/regress.sh -j 16 -s 1:300 -M all -t 90 A` (asan; `-t 90` as in T07-T09, at the default 20 s asan is 5-10 times
slower than the limit allows): **0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports**, smoke 0 failures in all 17
rows, coverage holds. Stress timeout failures: gc-mode1 58/150, restart-mode1-dl 68/150, restart-dl 6/150 (the three
known rows) and, only in asan, gc-dl 8/150 and gc-mode2 4/150 (the T09 note on gc-mode2: the stress options need 10-100
times the conflicts and asan is slow; gc-dl has 0 timeouts in 2000 release seeds). Normal-row timeouts (warnings):
mode1 3, mode1-dl 15, mode2-dl 1, noearly 40. Proofs accepted 300/300 in every row that has proofs and no timeout.

`tests/fuzz_qdimacs.sh R 1 1000 OPT` for OPT '', `-dl`, `-mode=1`, `-mode=2`: **0 failures, 0 timeouts, 2000 instances
agreed in each** (`m1-gate-qdimacs.log`). `tests/run_regressions.sh R`: 7 instances, 0 failures. `ctest --preset X`:
36/36 pass in release, asan, debug, release-clang; clean rebuilds of all four presets (`--clean-first`) have no compiler
warning (only the existing linker note "using serial compilation of N LTRANS jobs" in release).

### Corpus conflict histogram, new solver (seeds 1..400, `corpus_stats.py --check`, 20 s, `c stat conflicts`)

| default | 0-9 | 10-99 | 100-999 | 1000-9999 | >=10000 | timeout | in [100,10000) | max s |
|---|---|---|---|---|---|---|---|---|
| qcnf-mixed | 0 | 0 | 0 | 70 | 10 | 0 | 88% | 0.3 |
| qcnf-sat | 0 | 0 | 0 | 78 | 2 | 0 | 98% | 0.1 |
| qcnf-unsat | 0 | 1 | 13 | 51 | 15 | 0 | 80% | 0.7 |
| reach-44 | 15 | 3 | 33 | 29 | 0 | 0 | 78% | 0.2 |
| reach-48 | 12 | 4 | 27 | 37 | 0 | 0 | 80% | 0.2 |
| all (new) | 27 | 8 | 73 | 265 | 27 | 0 | 84% | 0.7 |
| all (baseline, T01) | 25 | 6 | 81 | 258 | 30 | 0 | 85% | 0.4 |

| `-dl` | 0-9 | 10-99 | 100-999 | 1000-9999 | >=10000 | timeout | in [100,10000) | max s |
|---|---|---|---|---|---|---|---|---|
| qcnf-mixed | 0 | 0 | 5 | 66 | 9 | 0 | 89% | 0.3 |
| qcnf-sat | 0 | 0 | 31 | 48 | 1 | 0 | 99% | 0.1 |
| qcnf-unsat | 0 | 0 | 10 | 54 | 16 | 0 | 80% | 0.4 |
| reach-44 | 14 | 2 | 23 | 41 | 0 | 0 | 80% | 0.3 |
| reach-48 | 12 | 1 | 20 | 46 | 1 | 0 | 82% | 2.2 |
| all (new) | 26 | 3 | 89 | 255 | 27 | 0 | 86% | 2.2 |
| all (baseline, T01) | 13 | 28 | 93 | 233 | 33 | 0 | 82% | 15.5 |

Lean-checked binary proofs of the default run: 400 of 400 accepted, longest check 10.9 s (baseline 5.4 s). The corpus
keeps its properties with the new solver (84% / 86% in range, no timeout). The `-dl` shape differs (the dependency
learner of the new solver has fewer 10-99 and more 0-9 instances): heuristic drift from tie-breaking, see the fidelity
note below.

### Certificates (`tests/check_cert.py`, `tests/fuzz_cert.sh`, seeds 1:500, JOBS 12)

Per seed: tiny and search corpus instance, tiny and large QDIMACS instance (2000 instances per run). Statuses:
VALID = certificate substituted and the verdict stays (SAT with outermost existential, UNSAT with outermost
universal block); WELLFORMED = the other combinations, the line lists exactly the block's variables.

| binary | options | VALID | WELLFORMED | INVALID | no V line (MALFORMED) |
|---|---|---|---|---|---|
| new (7555d53) | none | 1261 | 739 | 0 | 0 |
| new | `-dl` | 1261 | 739 | 0 | 0 |
| baseline | none | 1254 | 730 | 0 | 16 |
| baseline | `-dl` | 1254 | 730 | 0 | 16 |
| new, seeds 501:3000 | `-dl` | 6283 | 3717 | 0 | 0 |
| baseline, seeds 501:3000 | `-dl` | 6234 | 3679 | 0 | 87 |

### Certificates under -dl (for the coordinator)

**No invalid certificate was found**, for either binary, with or without `-dl`, in 12000 (new) and 12000 (baseline)
instances with `-dl` (seeds 1:3000, the first 500 also without `-dl`); so there are no examples of a partial
assignment that is invalid, and the decision of ARCH 10.4 / ROADMAP M1.8 (print only assigned variables, or complete the
block by a search) is not forced by this evidence. Limits of the evidence: 37% of the instances are not checkable
(SAT with an outermost universal block, UNSAT with an existential one); the corpus instances are small and mostly
decided within few conflicts, so a block left partially assigned at the end of a `-dl` search is probably rare there.
The tool makes the check cheap, so a targeted generator for such instances is the next step if the decision matters.

One **behaviour difference** was found instead (benign): when the formula is decided at input (an empty clause, an empty
`and()`, ...: 16 of 2000 instances at seeds 1:500, 87 of 10000 at 501:3000, all tiny corpus instances) the baseline
prints no `V` line at all, and the new solver prints the outermost block with unassigned variables as positive
literals, as ARCH 10.4 specifies; those certificates are valid or well-formed. Three small examples (instance, size):
`tiny-342.qcir` (211 bytes), `tiny-135.qcir` (388), `tiny-157.qcir` (423); generate with
`python3 tests/corpus.py --tier tiny --seed N --out f.qcir`, N = 342, 135, 157, and run the baseline with `-cert`:
`UNSATISFIABLE` and no `V` line; new: `V v1 v2 v3 0`. The instances of all bad rows are kept in
`/home/ec2-user/miniqu-work/cert/baseline-miniQU*/` (lists in `bad.txt`; the 501:3000 list replaced the first for `-dl`,
the first is `logs/cert-baseline-dl-bad-1-500.txt`). Whether to match the baseline (print nothing) or keep printing is a
coordinator decision; nothing was changed.

### Fidelity note: `-no-early-tseitin` (the 11% timeouts of the noearly row)

222 of 2000 (R) and 40 of 300 (A) search instances time out with `-no-earlytseitin`. Checked against the baseline on
search seeds 1001-1200, 20 s, six parallel: with the deterministic default (seed 0) new 30 timeouts, baseline 22 (8
only new, 0 only baseline); with `--seed=1` / `-rnd-init -rnd-seed=1` new 26, baseline 24 (3 only new, 1 only baseline),
no verdict differs. Instance `search-1014` explains the seed-0 gap: baseline 11 conflicts, new more than 12000; but
with seeds 1, 2, 3, 6 both need exactly the same number of conflicts (104, 104, 104, 17) and with seed 4 3705 against
23437, seed 5 19298 against more than 10 s: the instance family is heavy-tailed in the tie-breaking of equal initial
scores, not a lost behaviour. The timeouts of the row are inherent to the option, not to the port.

### Not done, open, for the coordinator

- The three stress rows over the 2% limit (gc-mode1, restart-dl, restart-mode1-dl), unchanged and unresolved; in asan
  also gc-dl (8/150) and gc-mode2 (4/150) at `-t 90` under load.
- No full benchmark run was made (the benchmark stage does them); no number of this entry is a performance claim.
- The 1:2000 release run used `regress.py` before bug 2 and 3 were fixed (fixes change only how a timed-out proof run
  and the smoke directory are treated); the two proof alarms were re-verified by hand, the smoke part was rerun on its
  own. The asan run and the smoke rerun used the fixed script. The release run was not repeated as a whole (3 h).
- The asan run used `-t 90`, not the default 20 s of the spec's command line.
- The two `jctc` smoke instances (`jctc1-pass`, `jctc9-pass`, solved by the baseline in 0.1 s and 1.3 s) still time out
  with the new solver at 120 s in every row of the smoke test (known since T05); the benchmark stage will meet it.
- Certificate semantics under `-dl` could not be shown to be a problem (above), and a targeted test is not written.

## Coordinator decisions after M1 round 1 (coordinator, 2026-11-22)

Every open point of T01-T10 is settled here: as a worker task (T11, T12 below), as a decision, or as a deferral.
Decisions are binding for the verifier and the reviewer. Measurements of this entry: release binary 59b1a69, search
seeds 151-300 (150 instances, `/home/ec2-user/miniqu-work/stress-t08/inst`), 20 s, 16 parallel on cores 16-47 while a
regress run of another agent was using the machine (so times are upper bounds); script, per-configuration summary and
the conflict table in `bench/results/m1-triage/` (`m.sh`, `sum.py`, `stress-options.txt`, `fid.csv`), raw CSVs in
`/home/ec2-user/miniqu-work/triage/`.

### D1. Stress rows and their timeout limits (T07.1, T08, T09.1, T09.2, T10.1, T10.3)

What the stress rows protect: every scheduled event (reduction, collection with relocation, restart, dependency
reset) fires many times per instance, with verdicts cross-checked and proofs Lean-checked on the instances that
finish, and a timeout rate that would expose a new hang. Measured (timeouts of 150; longest finished run; medians per
finished instance):

| row / candidate | timeouts | max s | median events | decision |
|---|---|---|---|---|
| `gc` `--reduceint=2` (mode 0) | 0 (0/1000 in T10) | 6.2 | 68 reductions = collections | **unchanged**, limit 2% |
| `gc-dl`, reduceint 2 / 10 / 30 | 0 / 0 / 0 | 20.0 / 12.3 / 4.3 | 62 / 27 / 12 | **`--reduceint=30`**, limit 2% |
| `gc-mode1`, reduceint 2 (T08) / 10 / 30 / 100 / 300 | 44 / 9 / 1 / 0 / 0 | - / 19.8 / 13.8 / 8.7 / 4.3 | - / 41 / 25 / 14 / 8 (default options: 6, on 60% of the instances) | **`--reduceint=100`**, limit 5% |
| `gc-mode2`, reduceint 2 / 10 / 30 | 0 / 0 / 0 | 18.0 / 4.7 / 1.6 | 61 / 23 / 12 | **`--reduceint=10`**, limit 2% |
| `restart` (mode 0) | 0 (0/1000 in T10) | | | **unchanged**, limit 2% |
| `restart-dl` as is | 6 (36/1000 in T10) | | 100% restarts | **options unchanged, limit 8%** |
| `restart-dl`, constant interval 2 / 4 / 16 / 50, Luby 1 / 4 / 10 | 5 / 6 / 5 / 3, 2 / 1 / 0 | | | not taken |
| `restart-mode1-dl` as is | 63 (357/1000 in T10) | | | replaced |
| same, constant interval 2 / 4 / 8 / 16 / 50 (depreset 1, 1, 2, 4, 1) | 58 / 49 / 34 / 20 / 18 | | | not taken |
| same, Luby with rfirst/depreset 1/1, 4/1, 10/2, 10/5, 20/2, 20/5, 30/3 | 23 / 21 / 21 / 22 / 22 / 21 / 21 | 13.2 (1/1) | 1/1: 2620 restarts, 976 dependency resets | **`--rfirst=1 --depreset=1 -mode=1 -dl`** (Luby on), limit 25% |
| `-mode=1 -dl` default (Luby 100, depreset 20) | 1 | 11.3 | 44 restarts, 2 resets | (the normal row) |

Reasons:
- **gc rows.** `--reduceint=2 --tier1glue=0` deletes nearly everything that is learnt; mode 0 survives that (0 timeouts
  in 1000 release instances), `-dl`, mode 1 and mode 2 need 10 to 100 times the conflicts (T07, T08, T09 measured it),
  which the asan binary (7-13 times slower) cannot do in 90 s. The new values keep 12 to 23 reductions and collections
  per instance at the median (default options: about 6, and only on 60% of the instances), with `reductions`,
  `collections` and `relocated` nonzero on 91-98% of the instances, so the coverage assertion keeps a wide margin. The
  extreme interval 2 remains in the mode-0 row, and with `-dl`, `-mode=1`, `-mode=2` in `tests/fuzz_qdimacs.sh`
  (T09 ran it for mode 2: 0 failures, 0 timeouts in release), which T12 makes part of the gate.
- **restart-dl.** The baseline with the same schedule (`-no-luby -rfirst=1 -rinc=1.000001 -dl`) times out on the same
  six seeds (T08). The options stay; the limit is twice the measured rate (3.6% of 1000 release, 4% of 150 asan).
- **restart-mode1-dl.** 18 seeds (155 174 180 184 185 189 199 209 214 215 230 234 239 244 270 280 290 299, all
  UNSAT) time out under *every* restart schedule tried that is more frequent than the default, constant or Luby, with
  any `depreset`, and the baseline times out on the same 18 with restart-every-conflict (28 of 150 in total, T08).
  With default options they are solved in 1-4 s after 20-51 restarts. So no choice of options reaches 2%; the Luby
  schedule with base 1 is taken because it has the fewest timeouts (23, against 63) and at the same time the most
  restarts and resets on the instances that finish. Limit 25% = the baseline's rate under its closest schedule (19%)
  plus a margin. Observation for M2.4 (EMA restarts) and M2.6: `-mode=1 -dl` is fragile against frequent restarts on
  this family in the baseline as well; any new restart schedule is to be checked on these seeds.
- **Limits above 2%** are a property of the row in `tests/matrix.txt` (optional sixth field), not a global change. ROADMAP
  0.1 is amended with the rule: only with a measurement against the baseline.
- **asan timeout.** The gate command for the asan binary is `tests/regress.sh -t 90 ...` (as T07-T10 ran it); 20 s
  stays the default and the limit of release runs. ROADMAP 0.1 amended.
- If a row exceeds its new limit in T12's validation or after T11, the worker reports the numbers and changes nothing.

### D2. The two `jctc` smoke instances and the order of equal scores (T05.3, T07.2, T10.4, T10 fidelity note)

Re-measured, 30 s, eight seeds: `jctc1-pass` baseline solves seeds 6 and 8 (and seed 0 in 0.09 s), new solves seeds 4
and 8; `jctc9-pass` baseline solves seed 2 (and seed 0 in 1.2 s), new none; conflict rates are the same (2000-2900 /s
in both). So with random initial scores the two binaries are alike, and the difference is in the unseeded run, where
all initial scores are equal. `src/heap.hpp` breaks ties by the smaller variable index (ARCH 7.3 said so); the baseline's
MiniSat heap compares scores strictly, so its order of equal scores follows from the heap operations. Experiment (a
scratch copy, `/home/ec2-user/miniqu-work/triage/src-tb`, one line: `before` returns `sa > sb`):

- `jctc1-pass` is solved in 1.7 s (6685 conflicts; baseline 623); `jctc9-pass` still times out at 30 s.
- `search-1014`: 13 conflicts against the baseline's 13 (before: 15); with `-no-earlytseitin` 11 against 11 (before:
  timeout, the instance of T10's fidelity note); `-dl` 1196 against 1210.
- Search seeds 151-230, conflicts new/baseline (`fid.csv`: seed, baseline, current, experiment, then the same with
  `-dl`): default geometric mean 0.88 with 14 of 80 identical counts and largest factor 7.8 (current: 0.98, 4
  identical, largest factor 56); `-dl` 1.11 with 7 identical, largest factor 21 (current: 1.17, 2 identical, 34). Many
  counts are now within a few percent of the baseline's (5193/5298, 7345/7696, 101/101).

**Decision:** the heap orders equal scores as the baseline does (ARCH 7.3 amended). It costs nothing, the run stays
deterministic, and it removes most of the heuristic drift from the M1 comparison, which is a comparison of a port.
Task T11 implements it and looks for the cause of the remaining divergence. `jctc9-pass` unsolved at seed 0 is
**accepted** if it remains after T11: the baseline solves it on 1 of 8 seeds, the benchmark protocol compares seeded
run sets, and a seed-0 loss on an instance that both binaries lose on most seeds is not a parity gap.

### D3. Machine and benchmark protocol (T05.2, T06.8)

The machine has 96 cores. Timed runs: upper half of the cores, `--jobs nproc/2`, `--mem-gb 8`; everything else on the
lower half, at most 16 jobs (ROADMAP 0.3 amended). `bench/run.py`, `tests/regress.sh`, `tests/regress.py` and the
other scripts still hard-code `64-127`, `0-63` and 48 jobs: T12 derives them from `nproc`. Old results measured on
the 128-core machine serve verdict checks only.

### D4. Accepted as built (no task)

- **T01.** The 15.5 s `-dl` instance is the *baseline's* time in the corpus histogram; `regress.py` takes its reference
  verdict from the baseline's default run first, and the new solver's longest `-dl` run on the corpus is 2.2 s. The
  `noearly` row is a normal row: its timeouts (11%) only warn, T10 showed the baseline has them at the same rate with
  seeds, and its coverage counters hold; D2/T11 is expected to lower the seed-0 gap. The synthetic counters of the stat
  wrapper are obsolete: every counter of the matrix has since been asserted on the real binary (T07-T10). Rate-checking
  only the default proofs in the histogram is enough, because every row's proofs are Lean-checked by `regress.sh`.
- **T02.** All listed deviations (sanitizer runtime symlinks, `miniqu-old-lib` since removed, `const Arena &` in
  `Watches`, process-wide verbosity, first-guess profile levels, tmpdir) are accepted.
- **T03.** Gate order inside a group for files with forward references: accepted without scanning the 376 files.
  QCIR requires definition before use, the constraints are identical, and a numbering that disagreed with
  `doc/proof-format.md` would be rejected by the Lean checker in the benchmark proof runs, which is a blocking failure
  by rule. `tests/encoding_diff.sh` needing the baseline binary is a documented prerequisite (`bench/README.md`).
- **T04.** `Solver::set` aborting on an unknown name, and the assertion for "unit of the other kind", are accepted.
- **T05.5.** The four differences of the binary (QCIR by file name, result file always written, `V` line when the input
  decides the formula, stdin notice as a comment) are accepted.
- **T05.4 / arena.** A failing arena `realloc` ends through `fatal` (exit 1). Accepted for M1: the harness limits memory
  by watching RSS and never by an address-space limit, so no benchmark result depends on it. Deferred to **M2.1** (the
  first package that touches `arena.cpp`): report it like `std::bad_alloc` (`INDETERMINATE`).
- **T06.1 `--trace`.** The new content is confirmed: originals as lines without premises, reductions of originals as
  derived lines, no deletions, QCIR literals as proof numbers, no `u` lines. The old premises were QDIMACS positions
  that no longer exist as ids, and the old QCIR trace never worked, so there is no consumer to stay compatible with.
- **T06.2-T06.7.** Default `Checker` when no tracer is connected (a debug run with only `--trace` is unchecked unless
  `--check`), the `Proof` API as built, user numbers as proof numbers for QDIMACS, the two error messages through
  `fatal`, and initial cubes staying live in the `Checker` (debug and `--check` only) are accepted. T06.6 is closed by
  T09: minimisation is off while any tracer is connected.
- **T07.4.** (a) decide right after `reduce`, (b) `lim.reduce = conflicts + reduceint * reductions`, (d) the old
  schedule's constants as `constexpr` are accepted. (c) "half of the candidates" and the size tie-break instead of the
  dropped constraint activity are accepted as known sources of drift against the baseline; T11 reports whether they
  are the first divergence. The whole policy is replaced in M2.2.
- **T07.5.** The header measurement stands as a ratio measurement; the 12-byte header is confirmed.
- **T09.3.** `--trace` rejected in mode 2 (the old trace there held no learnt constraint, so it was not usable);
  minimisation off for all `ccminmode` values under a tracer (the old proofs with modes 1 and 2 missed the removed
  literals, i.e. were not checkable; M2.3 makes minimisation proof-producing); the definition of `minimized`; the
  duplicate watch entry not ported. All accepted. Consequence to keep in mind when reading results: the proof runs of
  the `ccmin3` rows check the search without minimisation; minimisation itself is covered by verdicts only until M2.3.
- **T09.4, T10.2.** The partial reruns are accepted as evidence for the commits they covered, because the code changes
  in between are stated and narrow. They are superseded anyway: T12 reruns the gate on the final binary after T11.
- **T10.5 `V` line.** The new solver keeps printing a `V` line when the input decides the formula (ARCH 10.4): every
  such certificate was valid or well-formed, and a caller of `--cert` gets a line in every solved case. The baseline's
  missing line counts as the baseline's behaviour in `check_cert.py`, not as a discrepancy.
- **Commit trailers (T08, T09).** The commits carry the attribution lines of the session that made them. Accepted;
  history is not rewritten.
- **Release link note** `lto-wrapper: using serial compilation`: not a warning of the code; T12 silences it with
  `-flto=auto`.

### D5. Deferred

- **Certificates under `-dl`** (T10.6): no invalid certificate in 24000 checked runs, so ARCH 10.4 stays as it is
  (inherited behaviour). A targeted generator for blocks left partially assigned is deferred to **M3.1**, where the
  extension stack changes how certificates are built and the check has to be redone in any case.
- **Peak RSS on long, small runs** (T07.3, `amba2f9n` 23 MB against 19 MB): the M1 memory rule is amended (ROADMAP,
  acceptance of M1): below 64 MB of baseline RSS the limit is an absolute excess of 16 MB. The cause (trajectory of the
  learnt database or watch-list growth) is looked at once in T11's re-measurement and otherwise left to **M2.2**, which
  replaces the reduction policy.
- **Propagation rate 0.70 on `1.3.qcir`, `1.4.qcir`** (T07.3): total CPU time there is 5.5 s against 9.5 s, so it is
  not a loss for the user; whether the rate is a real slowdown of early propagation or an artefact of where the two
  binaries stop the "parse" clock is settled by T11's re-measurement (with the baseline's tie order the conflict
  counts should be close enough to compare directly). If it is real it becomes a task of the next round, not of M2.
- **Full benchmark runs** (T10.7): the benchmark stage, after T11 and T12.

### Worker tasks of round 2 (in this order)

- **M1-T11** (solver): baseline order of equal scores in the heap; first-divergence diagnosis against the baseline;
  re-measurement of fidelity, header table, smoke.
- **M1-T12** (tooling): `tests/matrix.txt` per D1 with the per-row limit; `nproc`-derived cores and jobs; QDIMACS
  fuzz with the gc options in the gate; `--profile` rows that are still 0.00 (T07.4e); members that nothing uses
  (T04); `-flto=auto`; then the full gate on the final binary.

## M1-T11: baseline order of equal scores; first-divergence diagnosis; fidelity (worker, 2026-11-22)

Commits 3a414a5 (heap), 0db1458 (rescale), a3afba8 (learnt literal order), aacdc59 (comment) and this STATUS commit.
Release binary of all measurements below: sha256 `fa6fbf22…` (sources a3afba8; aacdc59 changes a comment only and
gives the same release binary), copy in `/home/ec2-user/miniqu-work/t11/miniQU-final`. "Before" is the release
binary of 59b1a69 (`t11/miniQU-before`).

### Part A: the heap (3a414a5)

`Heap::before` is the strict score comparison. Read against `minisat/mtl/Heap.h` and every call site of
`minisat/core/Solver.cc`, five operations or call sites differed in a way that changes the order of equal scores;
each now follows the old code, with a one-line comment:
1. `remove` sifted up and then down; MiniSat's `remove` only sifts down (so the heap property may then be broken, as
   in the baseline; only `--dl` removes).
2. `update` (bumping) sifted up and down; MiniSat's `varBumpActivity` calls `decrease`, which only sifts up.
3. `learn_dependency` backtracked and then recorded the dependency, so the backtrack pushed x and the record removed
   it again; the old `search` records first (the backtrack then leaves x out), backtracks, then removes x if it is in
   the heap.
4. `reset_dependencies` pushed only unassigned variables; the old `resetDependencies` inserts every decision variable
   (root-assigned ones too).
5. `decide` under `--dl` returned as soon as no block had an unassigned variable; the old `pickBranchLit` runs the
   dependency watches and pops the heap until it is empty, so the heap is empty before the initial-cube analysis.
Equivalent already: push/pop (`insert`, `removeMin`), the child choice of `sift_down`, variable creation (pushed in
index order into the heap of the block, one heap under `--dl`; the old `initOrderHeaps` inserts in the same order),
re-insertion in `backtrack` (trail from the top down, same eligibility test), `update_dependency_watches`. The old
`rebuildOrderHeap` is only called from `simplify`, which the old search never calls: `Heap::build` and `clear` had no
caller in `src/` and are removed. `test/unit/heap.cpp` now compares 50000 random push/pop/update/remove operations
with a transcription of the MiniSat heap and pins the tie order (push 0..4, pops 0 4 3 2 1) and the sift-down-only
`remove`; `test/unit/depend.cpp` tests items 3-5.

### Part B: first divergence

Tools (work dir, not committed): instrumented baseline `/home/ec2-user/miniqu-work/t11/baseline-instr` (copy of
`baseline-src`, build `t11/baseline-instr-build`), instrumented copy of the new tree made by `t11/instr-new.sh`
(build `t11/new-instr-build`), `t11/evdiff.py INSTANCE [OPTS]` (first differing event with context). Both print to
stderr, when `EVENTS` is set: decisions (proof number, level), conflicts (literals@level), each antecedent of the
analysis, learnt constraints and dependencies, restarts, reductions (with the counts deleted), dependency resets, and
with `EVTRAIL` every propagated literal with the literal that propagated it. Literals are proof numbers in both
(the old `variable_names` of gates are the encoder's own numbers). The baseline copy has two switches that undo the
two deliberate deviations described below: `-proof=/dev/null` and `STOPFIRST=1` (`t11/baseline-aligned.sh` uses both).

Two unintended porting differences were found and fixed (class i):
- **Learnt literal order** (a3afba8): `Prefix::qreduce` sorted the learnt literals; the old `finishLearnt` reduces
  in place. The order decides which literal of the backjump level becomes position 1 (the first one of that level),
  i.e. the second watch, and from there the watch lists and the propagation order. First seen on search-1014 `-dl`
  at conflict 3 (two clauses in the watch list of literal -3354 in the other order). `qreduce` now keeps the order;
  `test/unit/original.cpp` pins it.
- **Rescale** (0db1458, found by reading `varBumpActivity`): the port divided by 1e100, the old code multiplies by
  1e-100; the products differ in the last bit in about a quarter of the cases (measured on random doubles), which
  changes ties after a rescale.

After these, the first difference on the instances examined is always one of three **deliberate, documented**
deviations (class ii; not changed):
1. **Originals are not simplified** under the root assignment (ROADMAP porting note 1). The baseline without a proof
   removes root-false literals from originals (MiniSat `addClause`), the port keeps them. With `-proof` the baseline
   takes the same path as the port. Example: search-1014 default, conflict 1 learns `-19635 1319 1726 2131` (baseline)
   against `-19635 505 912 1319 1726 2131` (new; 505 and 912 are false at level 0 and part of the reason of 19634).
   In mode 2 the baseline has no proofs, so this one cannot be aligned there (search-179/180/185/245/285 `-mode=2`
   differ at conflict 1 or 2 for this reason).
2. **Propagation stops at the first conflict** (T04, "Behaviour of the old propagate" item 2). After a clause conflict
   the old `propagate` still runs the cube loop of the same literal and keeps propagating whatever that assigns; this
   moves cube watches and so changes later propagation orders. Example: search-1014 `-dl`, conflict 105 (baseline
   `E -2 100 t` after the clause conflict; new: completion `100@32`); the decisions first differ at conflict 497.
   Default-mode examples (with `-proof`): search-245 conflict 3, search-285 conflict 2, search-190 conflict 5,
   search-244 conflict 2, search-243 conflict 1.
3. **Reduction policy** (D4 / T07.4c, porting note 7, ARCH 4.3): the port deletes half of the *candidates* (the
   baseline: half of *all* learnt constraints of the kind, counted with the protected and the glue-2 ones, as long
   as candidates remain), breaks ties by size instead of activity, and stores learnt units irredundant, so they are
   neither counted in the trigger `#learnt - #assigned >= max_learnts` nor in the halves. Example: search-243 default
   (aligned baseline), reduction at conflict 730 deletes 63 clauses (baseline) against 60 (new); the first difference
   is at conflict 737 (a clause the baseline deleted propagates in the new solver).

With the aligned baseline (both switches) the event streams of these instances are **identical to the end**
(including every antecedent of every analysis): default search-245, -285, -190, -244 (755-1010 conflicts); `-dl`
search-195, -221, -196, -269, -249 (185-1230 conflicts); `-mode=1` search-220 (1002); `-mode=2` search-282, -291,
-156. Of 66 non-identical runs examined with the aligned baseline (`bench/results/m1-t11-fidelity/firstdiff.csv`:
36 `-dl` runs and the 10 with the fewest conflicts of default, `-mode=1`, `-mode=2`), 60 first differ after at least
one reduction; the other 6 are the mode-2 runs of deviation 1 above and search-158 default, where the baseline
reduces at conflict 726 and the new solver does not (the learnt units of the trigger, deviation 3).

For the coordinator (alignment not done, per the task): deviation 3 is cheap to align while the old policy lives:
count the learnt units in the trigger of `reducing ()` (one term) and take the halves over all learnt constraints
of the kind, as the baseline does (a few lines in `reduce.cpp`); the size tie-break cannot follow the baseline
without constraint activities, and M2.2 replaces the whole policy anyway. Deviation 2 is a few lines in
`propagate_trail` (run the cube loop of the conflicting literal and go on propagating what it assigns, keeping the
first conflict), but T04 documented the literal old behaviour as able to overwrite the conflict and to assign the
literal of a pending completion, and ARCH 7.2 defines `propagated` by the first-conflict rule. Deviation 1 would need
a second, simplifying path for originals without a proof, against porting note 1. Not examined: ccminmode 3 sorts
its keys with `std::sort` where the old code uses MiniSat's `sort` (both unstable, so equal keys may come out in
another order); the ccmin3 rows were not part of the diagnosis.

### Part C: measurements

**Fidelity**, search seeds 151-300, seed 0, 60 s, conflicts new / baseline over the instances both solved (all 150
in every row; no timeouts), `bench/results/m1-t11-fidelity/` (`run.sh`, `summary.py`, CSVs; lower half, 16 jobs,
counts only):

| binary | config | geo. mean | min | max | identical |
|---|---|---|---|---|---|
| before (59b1a69) | default | 0.997 | 0.018 | 9.06 | 9 |
| before | -dl | 1.006 | 0.040 | 34.3 | 3 |
| before | -mode=1 | 0.899 | 0.001 | 4.62 | 1 |
| before | -mode=2 | 1.114 | 0.086 | 31.7 | 11 |
| after | default | 0.955 | 0.193 | 2.49 | 47 |
| after | -dl | 1.004 | 0.122 | 6.07 | 55 |
| after | -mode=1 | 0.957 | 0.128 | 4.87 | 22 |
| after | -mode=2 | 0.982 | 0.112 | 4.53 | 44 |
| after, vs aligned baseline | default / -dl / -mode=1 / -mode=2 | 0.953 / 0.995 / 0.985 / 1.006 | | | 63 / 93 / 62 / 51 |

(An intermediate binary with Part A and the rescale fix only had 26 / 31 / 1 / 44 identical counts.)

**Smoke** (`python3 bench/run.py --solver .../build/release/miniQU --tag m1-t11-smoke --timeout 120 --jobs 33 --cores
48-95 --mem-gb 8 --instances bench/smoke.txt --proof-check --proof-cores 0-47`; `--proof-cores` added so that the
checker stays on the lower half): **33/33 solved**, every verdict equal to `bench/smoke-expected.csv`, **33/33 proofs
accepted** by the Lean checker, longest run 3.4 s. **`jctc1-pass` solved at seed 0 in 0.08 s with 623 conflicts and
`jctc9-pass` in 1.06 s with 3858 conflicts, both exactly the baseline's counts** (baseline 623 in 0.07 s, 3858 in 1.2
s); D2's accepted gap is gone.

**noearly** (T10's note; `bench/results/m1-t11-fidelity/noearly.sh`, search seeds 1001-1200, 20 s, seed 0, both
binaries on cores 48-95, 24 seeds at a time): timeouts **new 27, baseline 26** (1 only new, 0 only baseline; no verdict
differs). T10 measured 30 against 22 on the old machine. search-1014 `-no-earlytseitin`: 11 conflicts, as the baseline.

**Header table** (`bench/header_measure.py --new t11/miniQU-final --tag t11`, results `bench/results/header-t11/`):
`1.3.qcir` props/s ratio **1.07** and `1.4.qcir` **1.08**, with **identical conflict counts** (313 / 313 and 300 /
300); so the 0.72 of h12 was a different search, not slower propagation, and no profile was needed. `amba2f9n.sat`:
RSS 22 MB against 18 MB (ratio 1.20, 4 MB above the baseline, inside D5's 16 MB rule), conflicts new 1586498,
baseline 1480707. All 10 instances of the "largest" group now have identical conflict counts (props/s ratios
1.02-1.24). Geometric means new/baseline: largest props/s 1.109, RSS 0.792, CPU 0.855; propagations group 1.319,
1.023, 0.640; all 1.209, 0.900, 0.739. **The instance set is not the same as h12's**: the script skips instances
that either binary does not solve in 180 s, and the new binary now solves `jctc17-vals-0,2-pass` and
`jctc18-vals-0,2-pass` (larger than `10.2` and `8.1`, which h12 took in their place) and needs 194 s for
`bt-2x5_17.ig` (replaced by `klieber2017q-088-22-eq`). The three h12 instances measured separately with the same
function and a 600 s limit (`logs/t11/header-missing.txt`): `10.2` props/s ratio 1.03 (204 / 204 conflicts, RSS 314 /
413 MB), `8.1` 0.99 (723 / 723, RSS 169 / 165 MB), `bt-2x5_17.ig` 1.16 (4117304 / 2097002 conflicts, RSS 42.5 / 29.5 MB,
194 s / 114 s).

### Acceptance (final binary; logs `/home/ec2-user/miniqu-work/logs/t11/`)

- Clean rebuilds (`cmake --build --preset P --clean-first`) of release, debug, asan, release-clang: no compiler
  warning (only the known `lto-wrapper` note in release); `ctest --preset P`: 36/36 pass in each.
- `tests/regress.sh -S -s 1:300 -M all R`: **0 wrong verdicts, 0 rejected proofs**, coverage assertions hold in every
  row. Stress rows over the old 2% limit, as expected (matrix unchanged, D1/T12): gc-mode1 45/150, restart-dl 6/150,
  restart-mode1-dl 63/150 timeouts. Normal-row timeouts (warnings): mode1-dl 5, mode2-dl 3, dl-ccmin3 1, noearly 31,
  gc-mode2 1; checker timeouts: mode1 1, mode1-dl 15, noearly 1, gc-mode1 12.
- `tests/regress.sh -S -s 1:100 -M all -t 90 A`: **0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports**,
  coverage assertions hold. Stress rows over the old 2% limit (expected, matrix unchanged): gc-mode1 19/50,
  restart-mode1-dl 20/50, restart-dl 3/50, gc-mode2 2/50; gc-dl 1/50 (at the limit, not over it). Normal-row timeouts
  (warnings): mode1-dl 9, mode2-dl 1, noearly 10. No checker timeouts; every finished instance of a proof row had
  its proof accepted.
- `tests/fuzz_qdimacs.sh R 1 300 OPT` for OPT '', `-dl`, `-mode=1`, `-mode=2`: 0 failures, 0 timeouts, 600 instances
  agreed in each. `tests/run_regressions.sh R`: 7 instances, 0 failures.

### Notes and open points

- Kept in the work dir: the instrumented baseline `/home/ec2-user/miniqu-work/t11/baseline-instr` (build
  `baseline-instr-build`), `instr-new.sh` (regenerates the instrumented copy of the new tree from the working tree;
  the copy itself was deleted), `evdiff.py`, `firstdiff.py`, `baseline-aligned.sh`, and the raw fidelity CSVs
  (`fid-A.csv` = intermediate binary). Event output and proof files were deleted.
- `bench/header_measure.py` still pins its runs to cores 0-7 (T12 derives cores from `nproc`); it ran with nothing
  else on the machine. The fidelity runs and the instrumented runs used the lower half (counts only); smoke and noearly
  ran on cores 48-95.
- The heap's `remove` reproduces MiniSat's sift-down-only removal, so with `--dl` the heap property can be broken
  after a dependency is learnt, exactly as in the baseline: decisions stay correct (any popped variable is
  checked), only which variable comes first is affected. ARCH 7.3 already says "exactly as the baseline's MiniSat
  heap"; no ARCH statement became false.
- D2's accepted gap (`jctc9-pass` at seed 0) no longer exists; D5's question about `1.3`/`1.4` is answered (same
  search, ratio 1.07/1.08).
- The noearly row still has 31 of 150 timeouts in the release regress run (warnings only); the baseline has the same
  rate on seeds 1001-1200 (26 of 200 against 27).

## Owner decision: stress-row timeouts on the sanitizer build (2026-11-22)

- A stress row that stays within its timeout limit on the release build and only exceeds it on the
  sanitizer (asan) build is NOT a failure, provided the asan run shows no wrong verdict, no rejected
  proof and no sanitizer report. This applies now to `gc-mode1` (9 of 150 at `-t 90`, limit 5%) and to
  any other row in the same situation.
- To make the gate green, increase the time limit of the asan gate run (the per-instance timeout, and the
  proof-check timeout if needed) or allow a higher share of timeouts for the asan run, whichever is
  simpler; both are acceptable. Prefer a longer time limit where the run time allows it, because it keeps
  more instances checked. Record the values chosen in `tests/matrix.txt` / `bench/README.md`.
- Verifier and reviewer: do not report or block on asan-only timeout-limit misses of stress rows; report
  the numbers. Wrong verdicts, rejected proofs and sanitizer reports remain blocking as before.

## M1-T12: tooling after the coordinator decisions; full gate (worker, 2026-11-22)

Commits (one per item): `fcfc915` (1: per-row stress limits, rows of D1, self-test `tests/test_regress_limits.sh`
with `tests/fake/hang-30.sh`), `29f751d` (2: cores/jobs from `nproc`, run.py checks), item 3 is the block in
`bench/README.md` (committed in `29f751d`, `tests/fuzz_qdimacs.sh` unchanged: it passes the options), `614353f` (4:
`PROFILE_SCOPE` in `Internal::search`, `Internal::analyze`, `Internal::propagate`; the stats unit test checks nonzero
`search`/`analyze`/`propagate` at level 3, zero at level 0), `2975741` (5), `716b199` (6). Logs:
`/home/ec2-user/miniqu-work/logs/t12/` (not committed; proof files deleted by the scripts).

### Item 4: overhead of the profile scopes

Release, `bench/run.py --tag smoke --instances bench/smoke.txt --cores 48-95 --jobs 33 --mem-gb 8 --timeout 120`
(`miniqu-work/t12/smoke-ab.sh`), binary before (HEAD without `614353f`) and after, alternating, 3 rounds. Same 33
verdicts in all six runs, 33/33 solved. Total wall time of the 33 instances (s): before 30.17 / 30.19 / 30.05
(mean 30.14), after 29.98 / 30.08 / 29.94 (mean 30.00): ratio 0.995, within the 3% bound.

### Item 5: dead members

Removed: `Limit::conflicts`, `Limit::decisions`, `Inc::restart`, `Inc::reduce`. `Solver::Impl::user_of` is read
(`solver.cpp:157`), kept. `Last` (`last.restart`, `last.reduce`) is read nowhere, but ARCHITECTURE 5 and 9.4 name
`struct Last` in `limit.hpp` for the later milestones, so it stays (listed here as required by the spec).

### Item 6

`-flto=auto` for GCC (`CMAKE_CXX_COMPILE_OPTIONS_IPO`): the release link prints no `lto-wrapper` warning any more;
release-clang keeps CMake's flags and builds without warnings.

### Item 7: gate on the final binary (HEAD `716b199`, `taskset -c 0-47`, 16 jobs)

- Clean builds (`--clean-first`) of release, debug, asan, release-clang: 0 lines with warning/error; `ctest`: 37/37
  in each (`gate-a.sh`).
- `tests/regress.sh -j 16 -s 1:2000 -M all R` (2 h 15 min): rc 0, **0 wrong verdicts, 0 rejected proofs**, every
  coverage assertion holds, all stress rows within their limit.
- `tests/regress.sh -j 16 -s 1:300 -M all -t 90 A`: **0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports**,
  coverage assertions hold, **one stress row over its limit (blocking for the coordinator's decision, nothing changed):
  `gc-mode1` 9 of 150 search instances timed out (6.0%, limit 5%)**. The timed-out instances are the search seeds
  179, 184, 199, 204, 209, 214, 234, 280, 290 (re-run with the asan binary, 90 s,
  `--reduceint=100 --tier1glue=0 --gcfrac=0 -mode=1`: exactly these nine time out,
  `python3 tests/corpus.py --tier search --seed S --out F.qcir`). The release row has 0 of 1000.
- Table per row: instances = tiny + search seeds; "proofs" = proofs accepted; "chk to" = proof checks timed out;
  "solver to" = solver timeouts on the search tier (1000 in R, 150 in A); proof runs unfinished (timeouts of the
  proof run): R mode1-dl 1, noearly 2, restart-dl 1; A none. Rows without limit: warnings only.

| row | R inst | R proofs | R chk to | R solver to | A inst | A proofs | A chk to | A solver to | limit |
|---|---|---|---|---|---|---|---|---|---|
| default | 2000 | 2000 | 0 | 0 | 300 | 300 | 0 | 0 | - |
| dl | 2000 | 2000 | 0 | 0 | 300 | 299 | 0 | 1 | - |
| mode1 | 2000 | 1995 | 5 | 0 | 300 | 299 | 0 | 1 | - |
| mode1-dl | 2000 | 1895 | 84 | 20 | 300 | 276 | 0 | 24 | - |
| mode2 | 2000 | 0 (no proofs) | 0 | 0 | 300 | 0 | 0 | 0 | - |
| mode2-dl | 2000 | 0 (no proofs) | 0 | 13 | 300 | 0 | 0 | 3 | - |
| ccmin3 | 2000 | 2000 | 0 | 0 | 300 | 300 | 0 | 0 | - |
| dl-ccmin3 | 2000 | 2000 | 0 | 0 | 300 | 299 | 0 | 1 | - |
| noearly | 2000 | 1793 | 15 | 190 | 300 | 268 | 0 | 32 | - |
| legacy | 2000 | 2000 | 0 | 0 | 300 | 300 | 0 | 0 | - |
| gc | 2000 | 2000 | 0 | 0 | 300 | 299 | 0 | 1 | 2% |
| gc-dl | 2000 | 2000 | 0 | 0 | 300 | 300 | 0 | 0 | 2% |
| gc-mode1 | 2000 | 1960 | 40 | 0 | 300 | 291 | 0 | **9** | 5% |
| gc-mode2 | 2000 | 0 (no proofs) | 0 | 0 | 300 | 0 | 0 | 0 | 2% |
| restart | 2000 | 2000 | 0 | 0 | 300 | 300 | 0 | 0 | 2% |
| restart-dl | 2000 | 1967 | 0 | 32 | 300 | 293 | 0 | 7 | 8% |
| restart-mode1-dl | 2000 | 1900 | 0 | 100 | 300 | 277 | 0 | 23 | 25% |

  Smoke part of both runs: 0 failures (timeouts only in the short-timeout smoke of slow rows, as before).
- `tests/fuzz_qdimacs.sh R 1 1000 OPT` for OPT '', `-dl`, `-mode=1`, `-mode=2`: 0 failures, 0 timeouts, 2000
  instances agreed each. gc options `--reduceint=2 --tier1glue=0 --gcfrac=0` + OPT: release 1 300: 0 failures, 0
  timeouts, 600 instances agreed in each of the four; asan 1 100: 0 failures, 0 sanitizer reports; timeouts (only
  counted): '' 0, `-dl` 1, `-mode=1` 3, `-mode=2` 0 (200 / 199 / 197 / 200 instances agreed).
- `tests/run_regressions.sh R`: 7 instances, 0 failures. `tests/fuzz_cert.sh R 1 500` and with `-dl`: 1261 VALID, 739
  WELLFORMED, 0 INVALID/MALFORMED/ERROR in both.
- `tests/corpus_stats.py --check --first 1 --last 400` (default and `-dl`): 0 timeouts; 400 proofs, 100% accepted
  (max check 4.4 s); fraction in [100, 10000) conflicts 87% (default), 82% (`-dl`); max solve time 0.3 s / 13.2 s.

## Owner decision: testing and benchmarking budget per milestone (2026-11-22)

The owner wants less extensive testing: roughly 2 hours of benchmarking per milestone. This overrides the
tiers, seed counts and seed ranges of ROADMAP 0.1/0.3 and of the milestone acceptance texts wherever they
cost more; the definitions of "better" / "not worse" and the report contents stay.

- **Benchmark stage of a milestone round: at most about 2 hours of wall time on the benchmark cores**, all
  runs included. The standard plan that fits: timeout 60 s, seeds 1, 2, 3, configurations default and
  `-dl`, new default against the previous accepted state (M1: the frozen baseline, run on this machine);
  results of the previous state are reused when they were measured on this machine with the same
  settings. With what is left of the 2 hours, in this order: one proof-coverage run (seed 0, default,
  proofs attempted for instances solved within 20 s, checker limit 600 s), one on/off ablation per new
  technique (default configuration, same seeds), modes 1 and 2 once each (seed 1). Drop items from the end
  of this list when the budget is used up, and say in the report what was dropped.
- **No 600 s "full tier" at milestone gates.** Long runs (900 s) happen once, in the final stage.
- **Fuzz gates: seeds 1:300 on the release build and 1:100 on the asan build** over the matrix (QCIR with
  Lean checking) and 1:300 for the QDIMACS fuzz, for task acceptance, the milestone gate and independent
  verification alike. The 1:2000 / 1:3000 ranges of the acceptance texts are not required. A
  verification pass should take about an hour, not several.
- Reviewer: judge the evidence against this budget. Do not block because the full tier, more seeds or
  larger fuzz ranges are missing; do say what the reduced evidence can and cannot show. Discrepancies,
  rejected proofs and sanitizer reports remain blocking.

## M1 round 2: diagnosis of B1 and plan (coordinator, 2026-11-23)

Review `doc/rewrite/reviews/M1-r1.md`: not approved, one blocking item (B1: the new engine needs more CPU time
than the baseline on identical searches when the neighbouring cores run copies of it). Accepted without
rebuttal: the report's "search-order variance" explanation was wrong.

### Cause: the 12-byte constraint header (measured)

Machine: EPYC 9R14, 96 cores, 1 MB L2 per core, **twelve L3 caches of 32 MB, each shared by 8 cores**
(`cpu0/cache/index3/shared_cpu_list` = 0-7). A benchmark run puts one solver on every core of the upper half,
so a process has about 4 MB of L3. The effect needs no 48 processes: 8 copies on cores 0-7 reproduce it in
seconds (`DW-sat-08-22-1`, seed 1, user time, median of 8: baseline 3.1 s, new 3.7 s; alone on the machine
both need 1.70 s with identical conflict and propagation counts).

Prototypes (scratch copies of `src/` at `edd1f12`, only `constraint.hpp` changed, built with `-O3 -DNDEBUG
-flto`; `/home/ec2-user/miniqu-work/coord/`: `build.sh`, `load48.sh`, `v0` unchanged, `v1` 4-byte header (no
id, no glue), `v2` 8-byte header (no id; head word and glue word), raw output `l48.txt`). Load as in the
review: its 12 instances x 4 copies = 48 processes of one binary at a time on cores 0-47, seed 1, arms in the
order baseline, v0, v1, v2, two rounds; per instance the median user time of the 4 copies, mean of the two
rounds; conflict counts identical in all four arms on every instance (none of them reduces in these runs,
which is why the prototypes without glue run the same search):

| instance | baseline s | 12-byte (r1) | 4-byte | 8-byte |
|---|---|---|---|---|
| DW-sat-08-22-1 | 1.99 | 2.58 (1.29) | 2.34 (1.18) | 2.58 (1.29) |
| DW-unsat-09-22-1 | 9.38 | 11.59 (1.24) | 9.86 (1.05) | 10.00 (1.07) |
| jctc10-fail | 7.21 | 9.26 (1.28) | 8.13 (1.13) | 8.71 (1.21) |
| DW-sat-09-26-1 | 3.79 | 3.87 (1.02) | 3.25 (0.86) | 3.48 (0.92) |
| chess_solving_mate_in_3_2003_UKR-CH_04 | 9.88 | 10.84 (1.10) | 9.57 (0.97) | 9.79 (0.99) |
| 9.2 | 13.75 | 14.08 (1.02) | 12.61 (0.92) | 12.94 (0.94) |
| chess_solving_mate_in_3_2012_GRE-CH-11_02 | 12.32 | 13.00 (1.06) | 11.50 (0.93) | 12.22 (0.99) |
| chess_solving_mate_in_3_1991_WCSC-15_05 | 8.06 | 8.71 (1.08) | 7.81 (0.97) | 8.04 (1.00) |
| 4.1 | 8.43 | 8.22 (0.98) | 7.24 (0.86) | 7.55 (0.90) |
| 5.2-1 | 31.68 | 31.86 (1.01) | 28.19 (0.89) | 29.10 (0.92) |
| hadw11-12 | 6.20 | 6.21 (1.00) | 5.43 (0.88) | 5.50 (0.89) |
| ltl2dba_beta6.tlsf | 11.79 | 11.48 (0.97) | 10.97 (0.93) | 10.73 (0.91) |
| **geometric mean of the ratio** | | **1.082** | **0.958** | **0.995** |

A second pair of rounds (baseline, 4-byte, and the same 4-byte binary again under another name) gave 0.918 and
0.920 for the two copies of the 4-byte binary, and shows the noise of single instances: the two identical
binaries differed by up to 15% on the two shortest runs (`DW-sat-08-22-1` 0.80 / 0.93, `jctc10-fail` 1.20 /
1.04) and by at most 2% on the instances above 8 s. So: the geometric mean over the twelve is reliable to
about 0.01-0.04 between sessions (the 12-byte arm was 1.08 here and 1.23 in the reviewer's session, the
direction and the ranking are the same), a single short instance is not. The idle-machine measurement of
T07 could not see any of this; its conclusion ("no slower and smaller") was wrong for the protocol all
milestones are measured with.

Not the cause, as far as these numbers go: `std::vector<Watch>`, `VarData`, `stats.ticks`, the initial arena
order (the old solver does not collect or simplify at start-up either: its `simplify ()` call is commented
out). With the 4-byte header the new engine is 4-8% faster than the baseline under load without touching
them. They stay as they are unless the measurement of R2-T2 on the real implementation says otherwise.

### Decisions

1. **Constraint layout** (ARCH 5.2 rewritten in this commit): 4-byte header, literals, then one glue word
   only for redundant constraints, then two id words only when a tracer is connected (`has_id` flag in the
   header, size field 26 bits as in the old solver). This is the old solver's memory per original and 4
   bytes less per learnt constraint; with a proof the footprint is what round 1 had. The 8-byte uniform
   header (parity, simpler) was the alternative; the 4-byte one is chosen because it is measurably faster and
   it is MiniSat's own scheme ("as in MiniSat/miniQU"). The T07 header decision is withdrawn.
2. **Rule**: layout decisions are measured under benchmark load with `bench/load_measure.py` (R2-T1), not on
   an idle machine.
3. **Reduce tie-break**: creation order (position in the `redundant` list, `std::stable_sort`) instead of
   the id, so that the search is the same with and without stored ids. Same order as before, since ids grow
   with creation; R2-T2 verifies identical conflict counts against the round-1 binary.
4. **Coverage of the id-less layout**: debug/asan builds connect the default `Checker` (ids present) unless
   `ccminmode > 0` or mode 2. The id-less paths of reduce/collect in an asan build are covered by the unit
   tests (which build `Internal` without a tracer), by the `gc-mode2` row and by a new stress row `gc-ccmin3`.
5. **Mode 1 "worse" by the sign test** (14 W / 31 L): same cause expected (mode 1 had the largest
   identical-search ratio, 1.14); it is re-run in the benchmark stage, with seeds 2 and 3 of both arms if
   the 2 hours allow.

### Suggestions of the review

- `struct Last` removed (R2-T1); ARCH 3.1 and 9.4 now say that the first package that reads it adds it.
- Constants of `reduce.cpp` / `bump.cpp`: ARCH 9.1 relaxed (a constant ported unchanged is a named
  `constexpr` until the package that changes it makes it an option; M2.2 for the reduce schedule).
- `Solver::freeze`: comment in `miniqu.hpp` (R2-T1).
- Benchmark reports state the arm order (R2-T1: the paired report prints the start time of every run).
- Proof-coverage run on the benchmark set and modes 1/2 with three seeds: in the benchmark stage of round
  2, in that order, as far as the 2 hours allow (9 new runs against the reused baseline runs take about one
  hour).

### Worker tasks of M1 round 2 (in this order; specs in the workflow, summary in ROADMAP "M1 round 2")

- **R2-T1** tooling and clean-ups. - **R2-T2** constraint layout, measurements, gate.

## M1-R2-T1 Bench tooling for B1 and clean-ups (worker, 2026-11-23)

What exists now:
- `bench/load_measure.py` + `bench/load-instances.txt` (the reviewer's twelve instances) + `bench/test_load_measure.py`
  (ctest `bench-load-measure`, fake solvers; second case checks `different search`). Arms run in separate
  rounds (A, B, A, B, ...), copy k of instance j on core `k*12+j` of `--cores` in both arms, user CPU time from
  `os.wait4`, conflict counts via the new `run.parse_stats_text` (run.py's regexes, refactored out of `parse_stats`).
  Refuses to start if more processes than cores or if `pgrep -af` finds `/miniQU`, `bench/run.py` or
  `load_measure.py` processes other than its own ancestors (`--force` overrides). Gotcha: when launching it
  detached from an agent shell, the shell wrapper's command line contains these words; start it through a small
  launcher script that sleeps 5 s first (what I did: `/home/ec2-user/miniqu-work/logs/launch-load.sh`).
  `--a-args`/`--b-args` accept values starting with `--` (`glue_arguments`).
- `bench/paired.py`: section `## Identical searches` after `## Result` (class `IdenticalSearches`, constants
  `MIN_CPU`, `FAMILY_MIN_N`, `FAMILY_LIMIT`) and the list "Order in which the runs started" in `## Parameters`;
  tests in `bench/test_compare.py` (`IdenticalSearchTest`: geometric mean 1.5 / counts, exclusions, family mark,
  run order, no stats.csv); `bench/README.md` documents both.
- Part C: `struct Last` and `Internal::last` removed (no other use in src/ or test/), `freeze` comment corrected.

Identical-search numbers regenerated from the committed CSVs (`bench/results/M1-r1-reports/*-paired-v2.md`; the
round-1 reports are unchanged). Acceptance check against the review: all equal.

| config | seed 1 | seed 2 | seed 3 | pooled per instance |
|---|---|---|---|---|
| default | 1.133 (n=39) | 1.125 (39) | 1.058 (37) | 1.119 (51) |
| dl | 1.104 (40) | 1.074 (42) | 1.111 (30) | 1.095 (50) |
| mode1 | 1.140 (35) | | | |
| mode2 | 1.026 (33) | | | |
| ccmin3 | 0.910 (4) | | | |

Families marked `> 1.10` in default: DW (6 instances, 1.279), chess (16, 1.138), hadw (3, 1.166), jctc (4, 1.293);
`numeric` (15) is at 1.013.

Reproducing commands (options of compare.py go before the `--`):

    B=baseline-c96; M=M1-r1
    python3 bench/compare.py --paired --out bench/results/M1-r1-reports/default-paired-v2.md \
        $B-default-t60-s{1,2,3} -- $M-default-s{1,2,3}      # likewise dl (3 seeds), mode1, mode2, ccmin3 (seed 1)

Load measurement `M1-r2-load-before` (round-1 binary sha256 a48a1a946f47... against the baseline, nothing else
running, 48 processes, 3 rounds per arm, about 33 s per round; log in the work dir):

    taskset -c 0-47 python3 bench/load_measure.py --a /home/ec2-user/miniqu-work/baseline/miniQU \
        --a-args "-rnd-init -rnd-seed=1" --a-name baseline --b /home/ec2-user/miniqu-work/build/bench-M1-r1/miniQU \
        --b-args "--seed=1" --b-name new-r1 --rounds 3 --cores 0-47 --tag M1-r2-load-before

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.99 | 3.86 | 1.941 | 1.91-3.36 | 2.31-4.57 | yes |
| DW-unsat-09-22-1.qcir | 9.48 | 13.22 | 1.394 | 8.07-11.08 | 11.79-14.27 | yes |
| jctc10-fail.qcir | 6.78 | 9.92 | 1.462 | 6.32-8.18 | 9.67-11.72 | yes |
| DW-sat-09-26-1.qcir | 3.85 | 4.39 | 1.142 | 3.47-4.15 | 4.09-4.65 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.99 | 12.22 | 1.222 | 9.21-11.81 | 10.59-13.27 | yes |
| 9.2.qcir | 13.79 | 16.06 | 1.165 | 12.67-15.01 | 15.14-16.80 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.52 | 14.49 | 1.157 | 10.93-13.50 | 13.23-16.63 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.41 | 9.53 | 1.133 | 7.30-9.57 | 8.47-10.30 | yes |
| 4.1.qcir | 8.28 | 9.22 | 1.114 | 7.90-8.55 | 8.92-9.42 | yes |
| 5.2-1.qcir | 31.66 | 35.70 | 1.128 | 30.80-32.91 | 34.55-36.95 | yes |
| hadw11-12.qcir | 6.23 | 6.64 | 1.065 | 5.98-6.73 | 6.17-7.20 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.31 | 12.53 | 1.018 | 11.50-13.50 | 11.43-13.10 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.226** |  |  |  |

Geometric mean 1.226 over 12 identical searches (conflict counts equal in all 288 runs): the reviewer's 1.23
reproduces with the new tool. The ranges of A and B do not overlap for 5 of 12 instances.

Checks: all four presets (release, debug, asan, release-clang) build without warnings and pass ctest (38 tests);
`tests/regress.sh -S -j 16 -s 1:40 -M default,dl` on the release build passed (0 warnings). No proofs involved in
this package. Nothing failed; the only deviation from the spec is that the `-verb=1` goes after the user's
arguments and before the instance, and `-rnd-init` etc. are passed through unchanged.

## M1-R2-T2 Constraint layout: 4-byte header, trailing glue and id words; watch records; load gate (worker, 2026-11-23)

Commits: `b9ba11e` (layout, A-E of the spec), `84a94d6` (matrix row `gc-ccmin3`), `c6753ff` (watch records, F3
candidate 2), `32a9714` (watch-list growth 3/2, F3 candidate 3), `60dce84` (watch records allocated once, for F6), and
this one (STATUS, results). Logs and throwaway scripts: `/home/ec2-user/miniqu-work/logs/r2-t2/`,
`/home/ec2-user/miniqu-work/r2t2/` (`f1.py`, `launch-*.sh`, `f5.sh`); proof files deleted.

### What changed

- `src/constraint.hpp`: the layout of ARCH 5.2 exactly (word 0: kind, redundant, garbage, moved, reason, has_id, 26-bit
  size; literals; glue word iff redundant; two id words iff `has_id`). `words (size, redundant, has_id)`, `glue ()` is 0
  for irredundant constraints, `set_glue` asserts redundant, `id ()`/`set_id` assert `has_id`, `shrink` moves the
  trailing words, `set_size` (model buffer) keeps the id words and asserts irredundant, `copy_constraint` copies verbatim,
  `alloc_constraint` takes `std::optional<uint64_t>`. `set_redundant`, `id_max`, `header_words` and the 44-bit packing
  are gone (`set_redundant` had no production use). `message_id (c)` (id or 0) for fatal messages.
- `Internal::stored_id (id)` (internal.hpp): the id a new constraint stores, none without a tracer; used by
  `new_constraint` (which asserts `has_id () == (proof != nullptr)` and sets the glue only for learnt constraints) and
  `alloc_model_cube`. `check_invariants` checks the same for every listed constraint.
- Id reads reviewed: analyze.cpp / analyze_qu.cpp / proof.cpp already under `if (proof)`; `add_original` builds the
  premises of the empty constraint only under `if (proof)`; model.cpp keeps the buffer's id across a collection only if
  it has one, `initial_cube` stores the id only if `has_id` (`next_id++` stays unconditional) and now calls `set_size`
  BEFORE copying the literals (the id words move with the size and the new literals may cover the old id position);
  logging.cpp prints `[id]` only if stored; check.cpp and model.cpp messages use `message_id`.
- `reduce.cpp`: `std::stable_sort` on (glue desc, size desc) over the candidates in list (= creation) order.
- `collect.cpp`: the Relocator uses `copy_constraint`.
- Watches (`src/watch.hpp`, F3, see below): one `alignas (64)` record per literal holding the clause list, the cube list
  and both dirty flags; `push_watch` grows a list by about 3/2; the records are allocated once for all variables at the
  first original (`Internal::size_watches`, also at the start of `search`), not per `add_var`; `check_invariants` walks
  the allocated lists (`watches.size ()`). ARCH 6.1 updated accordingly.
- Tests: `test/unit/constraint.cpp` rewritten (words of the four combinations, redundant+id glue/id independence and
  `shrink`, irredundant without id, `set_size` 3/0/1/5/4 keeping the id, `copy_constraint` into a second arena,
  forward/forwarded). `test/unit/database.hpp`: `Database (bool traced)` connects a recorder before the first constraint.
  `collect.cpp`: contents in list order with optional id (no id map), both layouts collected (`traced` false/true),
  watch-order check via `words ()` and the model buffer position. `reduce.cpp`: `test_reduce` and
  `test_collection_after_reduce` for both layouts; the deletion order is checked through the recorder when traced
  (the old test connected the recorder after the constraints, which is no longer allowed). `original.cpp`:
  `test_normalisation` now runs with a recorder (it checks stored ids), `test_units` checks that no id is stored without
  one. watch.cpp, propagate.cpp, analyze_ldq.cpp, search.cpp compiled unchanged.
- `tests/matrix.txt`: row `gc-ccmin3` as specified (`--reduceint=2` kept: release 0 of 150 search-tier timeouts,
  coverage of every required counter 91-100%); ROADMAP "Matrix names" lists it.
- `src/constraint.cpp` comment: ids counted always, stored only with a tracer; `proof.hpp` comment likewise.

### F1 same search (round-1 binary `bench-M1-r1/miniQU` against the new release binary, 16 jobs, 60 s)

12 load instances x seeds 1 and 0, 33 smoke instances seed 0, corpus search seeds 151-300; options '', `-dl`, `-mode=1`,
`-mode=2`, `-ccminmode=3`, `--reduceint=2 --tier1glue=0 --gcfrac=0`: 1242 pairs. Counters conflicts, decisions,
propagations, reductions, reduced.clause, reduced.cube and the `s` line:
- layout commit (`b9ba11e`): **1216 compared, 1216 identical**, 26 skipped (a timeout of either binary), 674 of them with
  reductions > 0.
- final binary (`60dce84`, sha256 dfbd0f64976b...): **1215 compared, 1215 identical**, 27 skipped.
- with/without `-proof=F -proof-binary` (final binary, corpus seeds 151-170, default and the gc options): **40 of 40
  identical**, 31 with reductions.

### F2

Clean builds (`--clean-first -j16`) of release, debug, asan, release-clang on the final code: 0 warnings; ctest 38/38 in
each.

### F3 load gate

`bench/load_measure.py`, baseline `-rnd-init -rnd-seed=1 [OPT]` against new `--seed=1 [OPT]`, cores 0-47, 3 rounds,
nothing else running. **Final binary: geometric means 0.827 (default, n=12), 0.773 (`-dl`, n=5), 0.818 (`-mode=1`,
n=9); no instance above 1.10 (largest: chess GRE-CH-11_02 in mode 1, 1.082). Gate met.**

How it got there (B/A per instance; `before` = round-1 binary, M1-r2-load-before of T1; `layout` = commit `b9ba11e`
alone; `watches` = + candidate 2; `growth` = + candidate 3; `after` = final binary with the allocation change; `-r4`
= repetition with 4 rounds; all directories under `bench/results/`):

default (diff = different search, unf = unfinished in 300 s; both excluded):

| instance | before | layout | layout-r4 | watches | growth | after |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1 | 1.941 | 0.965 | 1.137 | 0.764 | 0.704 | 0.808 |
| DW-unsat-09-22-1 | 1.394 | 0.970 | 0.986 | 0.737 | 0.687 | 0.675 |
| jctc10-fail | 1.462 | 1.120 | 1.085 | 0.881 | 0.875 | 0.879 |
| DW-sat-09-26-1 | 1.142 | 0.816 | 0.861 | 0.552 | 0.590 | 0.586 |
| chess_solving_mate_in_3_2003_UKR-CH_04 | 1.222 | 0.975 | 0.960 | 0.937 | 0.926 | 0.968 |
| 9.2 | 1.165 | 0.912 | 0.912 | 0.775 | 0.759 | 0.757 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02 | 1.157 | 0.948 | 0.942 | 0.912 | 0.928 | 0.932 |
| chess_solving_mate_in_3_1991_WCSC-15_05 | 1.133 | 0.997 | 0.930 | 0.936 | 0.891 | 0.949 |
| 4.1 | 1.114 | 0.891 | 0.875 | 0.794 | 0.804 | 0.803 |
| 5.2-1 | 1.128 | 0.900 | 0.888 | 0.881 | 0.885 | 0.885 |
| hadw11-12 | 1.065 | 0.864 | 0.866 | 0.871 | 0.895 | 0.895 |
| ltl2dba_beta6.tlsf | 1.018 | 0.882 | 0.871 | 0.863 | 0.869 | 0.881 |
| **geometric mean** | **1.226** | **0.934** | **0.939** | **0.818** | **0.810** | **0.827** |

-dl (diff = different search, unf = unfinished in 300 s; both excluded):

| instance | layout | watches | growth | after |
|---|---:|---:|---:|---:|
| DW-sat-08-22-1 | 0.847 | 0.705 | 0.676 | 0.679 |
| DW-unsat-09-22-1 | diff | diff | diff | diff |
| jctc10-fail | unf | unf | unf | unf |
| DW-sat-09-26-1 | diff | diff | diff | diff |
| chess_solving_mate_in_3_2003_UKR-CH_04 | unf | unf | unf | unf |
| 9.2 | 0.826 | 0.687 | 0.691 | 0.687 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02 | unf | unf | unf | unf |
| chess_solving_mate_in_3_1991_WCSC-15_05 | unf | unf | unf | unf |
| 4.1 | 0.837 | 0.766 | 0.768 | 0.767 |
| 5.2-1 | 0.888 | 0.904 | 0.914 | 0.909 |
| hadw11-12 | unf | unf | unf | unf |
| ltl2dba_beta6.tlsf | 0.851 | 0.883 | 0.880 | 0.850 |
| **geometric mean** | **0.849** | **0.784** | **0.780** | **0.773** |

-mode=1 (diff = different search, unf = unfinished in 300 s; both excluded):

| instance | layout | layout-r4 | watches | watches-r4 | growth | after |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1 | 1.221 | 1.259 | 0.868 | 0.871 | 0.834 | 0.775 |
| DW-unsat-09-22-1 | 1.163 | 1.173 | 0.775 | 0.819 | 0.694 | 0.759 |
| jctc10-fail | unf | unf | unf | unf | unf | unf |
| DW-sat-09-26-1 | 1.016 | 0.995 | 0.649 | 0.622 | 0.622 | 0.634 |
| chess_solving_mate_in_3_2003_UKR-CH_04 | diff | diff | diff | diff | diff | diff |
| 9.2 | 0.955 | 0.942 | 0.798 | 0.788 | 0.752 | 0.742 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02 | 1.047 | 1.028 | 1.114 | 1.120 | 1.085 | 1.082 |
| chess_solving_mate_in_3_1991_WCSC-15_05 | diff | diff | diff | diff | diff | diff |
| 4.1 | 0.921 | 0.935 | 0.847 | 0.854 | 0.804 | 0.798 |
| 5.2-1 | 0.970 | 0.964 | 0.942 | 0.951 | 0.884 | 0.880 |
| hadw11-12 | 0.919 | 0.927 | 0.919 | 0.937 | 0.858 | 0.847 |
| ltl2dba_beta6.tlsf | 0.947 | 0.912 | 0.957 | 0.956 | 0.922 | 0.920 |
| **geometric mean** | **1.013** | **1.009** | **0.865** | **0.870** | **0.819** | **0.818** |

The layout alone met the default and `-dl` parts (0.934 / 0.939 in two sessions, 0.849) and the mode-1 geometric mean
(1.013 / 1.009), but in mode 1 `DW-sat-08-22-1` (1.221 / 1.259) and `DW-unsat-09-22-1` (1.163 / 1.173) stayed above
1.10 in the repetition with 4 rounds (in default, `jctc10-fail` 1.120 and `DW-sat-08-22-1` 1.137 did not repeat). At
idle the same mode-1 searches were faster than the baseline (`DW-unsat-09-22-1`: 5.7 s against 6.5 s), so the cost was
again cache pressure. The candidates of the spec, in order, each against the previous state on the same day
(`load_measure.py --timeout 60`, 3 rounds, A = previous binary, B = candidate; `bench/results/M1-r2-load-candidates/`):

| candidate | mode 1 geo. mean (n=11) | default geo. mean (n=12) | decision |
|---|---:|---:|---|
| (1) `stats.ticks` counted in a local and added once per call | 0.976 | 0.987 | not kept: every instance above 3 s within 0.99-1.02, the means move with the 2-s `DW-sat-08-22-1` (0.71 / 0.83, its A median itself varied 1.6-2.4 s) |
| (2) one 64-byte record per literal: both list headers and both dirty flags | 0.890 | 0.884 | kept (DW 0.62-0.77, 9.2 0.83, nothing else worse beyond noise except chess GRE 1.098 in mode 1) |
| (3) list growth about 3/2 instead of 2 | 0.948, repeated 0.945 | 1.012, repeated 1.007 | kept: every mode-1 instance below 1 in both runs (0.92-0.97); default within noise. The uniform mode-1-only shift may partly be code placement rather than memory; I kept it under the rule "helps by more than the noise" |
| (4) for F6: 48-byte record of the two lists, dirty flags in a separate array (not in the spec) | 1.076 | 1.081 | rejected: DW 1.3-1.5 slower than (2)+(3); the flags must share the line |

After (2) the gate run had chess GRE-CH-11_02 (a 2.5-s mode-1 search) at 1.114 and 1.120 (4 rounds); after (3) it is
1.085 and, on the final binary, 1.082. The load tables of the final binary (`M1-r2-load-after`, `-dl`, `-mode1`; user
CPU seconds, median over all copies and rounds, B / A):

Default (`M1-r2-load-after`):

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.96 | 1.58 | 0.808 | 1.88-3.75 | 1.50-1.65 | yes |
| DW-unsat-09-22-1.qcir | 9.92 | 6.69 | 0.675 | 8.75-10.64 | 6.35-6.95 | yes |
| jctc10-fail.qcir | 7.33 | 6.44 | 0.879 | 5.90-8.24 | 4.85-7.10 | yes |
| DW-sat-09-26-1.qcir | 3.79 | 2.22 | 0.586 | 3.38-4.10 | 1.97-2.39 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.62 | 9.31 | 0.968 | 8.70-11.24 | 8.93-10.01 | yes |
| 9.2.qcir | 13.85 | 10.49 | 0.757 | 12.68-15.27 | 10.08-11.39 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.31 | 11.47 | 0.932 | 11.38-14.72 | 10.86-12.11 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.19 | 7.78 | 0.949 | 7.38-9.13 | 7.59-8.16 | yes |
| 4.1.qcir | 8.23 | 6.61 | 0.803 | 7.99-8.52 | 6.39-6.71 | yes |
| 5.2-1.qcir | 31.75 | 28.10 | 0.885 | 30.79-32.59 | 27.30-29.04 | yes |
| hadw11-12.qcir | 6.29 | 5.63 | 0.895 | 6.00-6.65 | 5.49-5.83 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.28 | 10.83 | 0.881 | 11.55-13.58 | 10.15-11.42 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.827** |  |  |  |

`-dl` (`M1-r2-load-after-dl`; unfinished: jctc10-fail and the three chess and hadw11-12, as in every `-dl` run here):

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 9.73 | 6.61 | 0.679 | 8.66-11.27 | 6.41-6.86 | yes |
| DW-unsat-09-22-1.qcir | 6.72 | 2.46 | 0.367 | 4.63-8.68 | 2.26-2.71 | different search |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 22.04 | 14.09 | 0.639 | 20.69-24.01 | 13.49-14.59 | different search |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| 9.2.qcir | 17.90 | 12.30 | 0.687 | 17.42-18.40 | 11.87-12.60 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | - | - | - | - | - | unfinished |
| 4.1.qcir | 6.62 | 5.07 | 0.767 | 6.45-6.82 | 4.79-5.33 | yes |
| 5.2-1.qcir | 15.55 | 14.14 | 0.909 | 15.39-15.90 | 14.00-14.33 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| ltl2dba_beta6.tlsf.qcir | 16.66 | 14.16 | 0.850 | 15.34-18.07 | 13.07-14.60 | yes |
| **geometric mean** (n=5 identical searches) |  |  | **0.773** |  |  |  |

`-mode=1` (`M1-r2-load-after-mode1`; jctc10-fail unfinished):

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.77 | 1.37 | 0.775 | 1.55-2.25 | 1.28-1.45 | yes |
| DW-unsat-09-22-1.qcir | 8.91 | 6.76 | 0.759 | 7.50-10.78 | 6.34-7.13 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 6.73 | 4.26 | 0.634 | 5.39-8.42 | 3.67-4.65 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.83 | 25.88 | 0.930 | 26.88-28.89 | 25.55-26.47 | different search |
| 9.2.qcir | 16.17 | 12.00 | 0.742 | 15.48-16.90 | 11.67-12.19 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.48 | 2.68 | 1.082 | 2.19-2.77 | 2.56-2.81 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.22 | 11.02 | 0.982 | 10.03-12.06 | 10.75-11.55 | different search |
| 4.1.qcir | 6.99 | 5.58 | 0.798 | 6.85-7.47 | 5.36-5.75 | yes |
| 5.2-1.qcir | 20.43 | 17.98 | 0.880 | 19.60-21.39 | 17.45-18.38 | yes |
| hadw11-12.qcir | 9.01 | 7.64 | 0.847 | 8.70-9.38 | 7.52-7.79 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.13 | 10.24 | 0.920 | 10.67-12.78 | 9.66-10.36 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **0.818** |  |  |  |

The round-1 `before` exists for the default configuration only (T1); for `-dl` and `-mode=1` the round-1 paired reports
gave 1.095 and 1.140 on identical searches of the benchmark set.

### F4 proof footprint (informational)

Final binary against itself, B with `-proof=/dev/null -proof-binary` (`M1-r2-load-proof`): geometric mean **1.096**
(n=12, per instance 1.056-1.165); the same before the allocation change (`M1-r2-load-proof-growth`): 1.099. This is the
cost of the two id words per constraint plus writing the binary proof.

### F5 fuzz gate (final binaries, `taskset -c 0-47`, 16 jobs; logs `logs/r2-t2/f5/`)

| run | result |
|---|---|
| `tests/regress.sh -S -j 16 -s 1:300 -M all R` | rc 0, **0 wrong verdicts, 0 rejected proofs**, coverage holds in every row incl. `gc-ccmin3`, every stress row within its limit (gc, gc-dl, gc-mode1, gc-ccmin3, gc-mode2, restart: 0 of 150; restart-dl 6, restart-mode1-dl 20). Warnings: solver timeouts mode1-dl 5, mode2-dl 3, dl-ccmin3 1, noearly 31; proof checks timed out mode1 1, mode1-dl 15, gc-mode1 6; noearly 1 proof run unfinished |
| `tests/regress.sh -S -j 16 -s 1:100 -M all -t 90 A` | rc 1: **0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports**, coverage holds in every row incl. `gc-ccmin3` (0 of 50 timeouts). The one failure is `gc-mode1` 3 of 50 search instances timed out (6%, limit 5%): corpus search seeds 64, 70, 89 (`python3 tests/corpus.py --tier search --seed S --out F.qcir`; asan > 90 s with `--reduceint=100 --tier1glue=0 --gcfrac=0 -mode=1`, release 2.7 / 3.1 / 3.9 s; release row 0 of 150). Under the owner decision "stress-row timeouts on the sanitizer build" this is not a failure. Other asan timeouts (warnings): mode1-dl 9, mode2-dl 1, noearly 10, restart-dl 3 (limit 8%), restart-mode1-dl 5 (limit 25%) |
| `tests/fuzz_qdimacs.sh R 1 300 OPT`, OPT '', `-dl`, `-mode=1`, `-mode=2`, `--reduceint=2 --tier1glue=0 --gcfrac=0` | 0 failures, 0 timeouts, 600 instances agreed in each of the five |
| `tests/run_regressions.sh R` | 7 instances, 0 failures |
| `bench/run.py --solver R --tag m1-r2-smoke --timeout 120 --jobs 33 --instances bench/smoke.txt --proof-check` | 33/33 solved, verdicts equal `bench/smoke-expected.csv` (33/33), **33/33 proofs accepted** by the Lean checker |

### F6 peak memory (`/usr/bin/time -v`, seed 0, 180 s, one process at a time)

| instance | baseline MB | round 1 MB (measured today) | final MB | final with per-variable growth of the records (`c6753ff`/`32a9714`) |
|---|---:|---:|---:|---:|
| 1.3 | 1681 | 1319 | **1358** | 1471 |
| 5.2-1 | 462 | 379 | 374 | 401 |
| DW-sat-08-22-1 | 37 | 32 | 32 | 32 |
| amba2f9n.sat | 18 | 22 | 21 | 21 |

(MB = KB / 1024 of `%M`.) **Deviation: on 1.3 the final RSS is 3.0% above round 1's** (1390456 KB against 1350244 KB;
STATUS T11 had 1316 MB for round 1), still 19% below the baseline; the other three are at or below round 1. Cause: the
watch record is 64 bytes per literal instead of 50 (two vectors and two flag bytes), and 1.3 has 2.2 million variables
(4.4 million literals, +60 MB). The record grown variable by variable cost another 8% (transient of two arrays at each
reallocation), which the allocation at the first constraint removed. The compact alternative (candidate 4) loses the
speed. Options for the coordinator: accept (the gate of F3 depends on the record), or replace `std::vector<Watch>` by a
MiniSat-style 16-byte list (pointer, size, capacity) so that two lists and the flags fit in 40 bytes; not done here
(larger change to every user of the lists).

### Deviations from the spec

- F3 investigation changed the code beyond the layout (candidates 2 and 3, kept by measurement as the spec allows when
  the gate is not met), plus the allocation of the watch records at the first constraint (for F6) and candidate 4
  (tried, rejected). Intermediate measurements are kept under the tags `M1-r2-load-layout*`, `-watches*`, `-growth*`,
  `M1-r2-load-proof-growth` and `M1-r2-load-candidates/`; `M1-r2-load-after*` and `M1-r2-load-proof` are the final
  binary.
- F6 on 1.3 above round 1 (see above).
- `check_invariants` walks the allocated watch lists only (before the first constraint there are none).
- The tie-break of `reduce` and the layout do not change the search (F1), as required.
- Commit trailers: the commits carry the attribution lines of this session's harness (`Claude Opus 5.5`, session
  `019m3aqfDNcA6iu8f1kSkxbh`) instead of the `Claude Fable 5.2` lines given in the task text.

### Reproducing

    # F1 (throwaway script): python3 /home/ec2-user/miniqu-work/r2t2/f1.py OLD NEW OUT.jsonl main|proof
    # F3, e.g. mode 1 (the others: drop -mode=1 / use -dl; repetition: --rounds 4):
    taskset -c 0-47 python3 bench/load_measure.py --a /home/ec2-user/miniqu-work/baseline/miniQU \
        --a-args "-rnd-init -rnd-seed=1 -mode=1" --a-name baseline --b <release miniQU> --b-args "--seed=1 -mode=1" \
        --b-name new-r2 --rounds 3 --cores 0-47 --tag M1-r2-load-after-mode1
    # F6: /usr/bin/time -v <binary> /home/ec2-user/benchmarks/qcir/1.3.qcir

## Coordinator decisions after M1 round 2 (coordinator, 2026-11-23)

Every open point of R2-T1 and R2-T2 is settled here. One worker task follows (R2-T3, tooling and documentation
only; no solver code changes). Measurements of this section: `/home/ec2-user/miniqu-work/coord/r2triage/` (`run.sh`,
`*.time`).

### E1. Peak memory on 1.3 (R2-T2 point 1, "F6"): accepted, no task

- Re-measured (`/usr/bin/time -v`, one process, cores 0-47 otherwise idle): final binary (`build/release`, `60dce84`)
  1390732 KB, round-1 binary (`build/bench-M1-r1`) 1350028 KB: +3.0%, as the worker reported. Baseline: 1681 MB.
- F6 ("not above round 1") was an acceptance line of the R2-T2 task spec, written before the watch record was known
  to be needed. The milestone gate is ROADMAP M1: peak memory not more than 10% above the **baseline** (16 MB
  absolute below 64 MB). That gate is met on all four instances (1.3: 19% below the baseline; 5.2-1: 19% below;
  DW-sat-08-22-1: 5 MB below; amba2f9n.sat: +3 MB, absolute rule). **F6 is withdrawn as a criterion; the M1 memory
  gate is the ROADMAP one and it is green.**
- Why the 3% is the right trade: the 64-byte record is what brought the mode-1 identical searches under load from
  1.01 to 0.87 and the default ones from 0.93 to 0.82 (R2-T2, F3); the compact 48-byte variant lost that (1.08). 60 MB
  on a 1.3-GB instance against 10-30% CPU time on the DW family is not a close call.
- **Deferred to M2 (as a measured candidate, not a gate):** a 16-byte list type (pointer, 32-bit size and capacity,
  MiniSat's `vec`) so that both lists and the two dirty flags of a literal fit in 32 bytes and the two literals of a
  variable share one cache line. M2 touches propagation and the watch lists anyway (tiers, binary handling); the
  candidate is taken only if `bench/load_measure.py` shows a gain beyond the noise (rule of round 2, decision 2) and
  the code does not get harder to read than `std::vector<Watch>` with `push_watch`. It is not done now because round 2
  has met its gate and the change touches every user of the lists.

### E2. Code changes beyond the layout (R2-T2 point 2): accepted, no task

The spec allowed the candidates when the layout alone missed the load gate, each kept only by measurement; that is
what happened (candidate 1 not kept, 2 and 3 kept, 4 rejected, all with numbers in STATUS and results committed).
ARCH 6.1 describes the record, the one-time allocation and the 3/2 growth. The owner's requirements (arena, watch
lists as in MiniSat/miniQU: one list of 8-byte watches with blockers per literal and kind, collection in access
order) are unchanged by it. The same-search check F1 (1215 of 1215 identical to round 1) covers these commits too,
since it was repeated on the final binary.

### E3. `gc-mode1` on the asan build, 3 of 50 timeouts at `-t 90` (R2-T2 point 3): asan gate limit raised to 240 s

- Binding owner decision ("stress-row timeouts on the sanitizer build"): not a failure; make the gate green by a
  longer time limit for the asan run where the run time allows it.
- Measured now (asan binary of `60dce84`, `--reduceint=100 --tier1glue=0 --gcfrac=0 -mode=1`, 12 processes side by
  side on cores 0-11, limit 900 s): all twelve seeds that ever timed out in this row finish with the right verdict.
  Seeds of the 1:100 gate: 64: 105 s, 70: 101 s, 89: 124 s. Seeds of T12's 1:300 run: 179: 92 s, 184: 139 s, 199: 334 s,
  204: 156 s, 209: 101 s, 214: 103 s, 234: 106 s, 280: 152 s, 290: 108 s. So these are slow runs of the asan build with its
  internal checker (release: 2.7-3.9 s), not hangs.
- **Decision: the gate command of the asan binary is `tests/regress.sh -S -j 16 -s 1:100 -M all -t 240 A`** (was
  `-t 90`); 240 s is about twice the slowest of the gate's seeds. The row, its options and its 5% limit stay as they
  are, so what the row protects (reductions and collections in mode 1 under the sanitizers, verdict and proof
  checked) is kept and more instances are checked than before. Release stays at 20 s. ROADMAP 0.1 amended in this
  commit; R2-T3 updates `bench/README.md` and the comment in `tests/matrix.txt` and confirms the row.
- For the verifier: with `-t 240` the row is expected green on 1:100. Should an asan-only timeout-limit miss of a
  stress row still appear (machine load), the owner decision applies: report the numbers, not a failure. Wrong
  verdicts, rejected proofs and sanitizer reports stay blocking.

### E4. Commit trailers (R2-T2 point 4): accepted, history is not rewritten

The trailer lines are supplied to each session by its harness and differ between sessions (model name, session id);
a worker that follows its harness is right. Commits `b9ba11e`..`f2679c5` keep their lines. Rewriting local history
to change attribution is not worth the risk for the other agents' work.

### E5. `check_invariants` walks only the allocated watch lists (R2-T2 point 5): accepted, no task

Follows from the one-time allocation: before the first constraint there are no records and no watches to check.
`check.cpp` asserts `watches.size () <= vars`, and `size_watches ()` is called by `add_original` and at the start of
`search`, the only two places after which a list can be read; `Solver::add_var` rejects variables after the first
original (`REQUIRE` in solver.cpp), so the records are never too short.

### E6. Bench tooling of R2-T1 (points 1, 2, 4): accepted as built

`parse_stats_text` split out of `parse_stats`; `-verb=1` after the user's arguments (the solver's option parser does
not depend on the order; a later user `-verb=0` cannot occur because the script appends last); `--a-args=--seed=1`
handled by `glue_arguments`. No effect on results.

### E7. Busy-process check of `load_measure.py` matches the launching shell (R2-T1 point 3): task R2-T3

The check must look at what a process *is*, not at words in its command line: a shell whose `-c` string mentions
`miniQU` is not a solver. R2-T3 replaces the `pgrep -af` pattern by an inspection of `argv[0]` / the script argument
from `/proc/PID/cmdline`, with a test, so that no launcher script with a sleep is needed and the benchmark stage
cannot trip over it. Until then the workaround of R2-T1 stands.

### Gates of M1 round 2 after these decisions

| gate | state |
|---|---|
| same search as round 1 (F1) | green: 1215 of 1215 |
| builds without warnings, ctest (F2) | green |
| load gate (F3): default 0.827, `-dl` 0.773, mode 1 0.818, no instance above 1.10 | green |
| fuzz, release 1:300 (F5) | green |
| fuzz, asan 1:100 | green by E3 after R2-T3 (0 wrong verdicts, 0 rejected proofs, 0 sanitizer reports at `-t 90` already) |
| QDIMACS fuzz, regressions, smoke with 33/33 proofs accepted | green |
| peak memory against the baseline (ROADMAP M1) | green (E1) |
| benchmark-set gate of ROADMAP "M1 round 2" (identical-search ratio, mode-1 sign test) | open: measured in the benchmark stage |

### Worker task

- **R2-T3** (tooling, docs): busy check by `argv` in `load_measure.py` with a test; `-t 240` for the asan gate in
  `bench/README.md` and `tests/matrix.txt`; confirmation run of the `gc-mode1` row on the asan binary.

## M1-R2-T3 Tooling after the round-2 triage (worker, 2026-11-23)

Changes (no solver source touched):
- `bench/load_measure.py` (decision E7): `busy_processes()` no longer runs `pgrep -af` with a pattern on whole
  command lines. It reads `/proc/PID/cmdline` of every process (vanished or unreadable ones skipped, this process
  and its ancestors skipped) and asks the pure function `is_busy(argv)`: busy iff `basename(argv[0])` is `miniQU`
  (any build, also the baseline), or `load_measure.py`, or argv[0] ends with `bench/run.py`, or a `python*`
  interpreter whose first non-option argument is `bench/run.py` or `load_measure.py`. `BUSY_PATTERN` is removed;
  `--force` and its note in the report are unchanged. The launcher-script-with-sleep workaround mentioned in the
  R2-T1 section is no longer needed. Tests: `IsBusyTest` in `bench/test_load_measure.py` (all cases of the spec,
  4 tests in the file pass; ctest `bench-load-measure`).
- Decision E3 (asan gate `-t 240`): comment lines added to `tests/matrix.txt` (no row, option or limit changed),
  usage comment of `-t` in `tests/regress.sh` (no behaviour change), and `bench/README.md` now lists both gate lines
  (release `-s 1:300 -M all`, asan `-s 1:100 -M all -t 240`) after the QDIMACS fuzz commands; the refusal sentence
  of the load_measure.py section now speaks of argv.

Part A manual check (96 cores): from `bash -c 'echo miniQU load_measure.py; nohup setsid taskset -c 0-47 python3
bench/load_measure.py ... --rounds 1 --cores 0-47 --timeout 20 --tag r2-t3-busycheck > LOG &'`, without `--force`
and without a sleeping launcher, the measurement started ("round 1, arm A ...") and ran to completion (5.2-1.qcir
unfinished at the 20 s timeout, as expected for this short test). While its baseline solvers were running, a second
invocation refused with rc 1 and listed the first load_measure.py and its miniQU processes. The result directories
were deleted, not committed.

Part C (asan binary, lower cores):
- incremental builds of release and asan: up to date; `ctest` in the release tree: 38 of 38 passed.
- `tests/regress.sh -S -j 16 -s 1:100 -M gc-mode1,gc-ccmin3,gc -t 240 <asan>` (log
  `/home/ec2-user/miniqu-work/logs/r2-t3/asan.log`): "REGRESSION TESTS PASSED (0 warnings)" (launched detached, so
  the rc was not captured; the script prints that line only on rc 0).
  - gc-mode1: 0 timeouts of 50 search instances, 98 proofs checked, 2 proof checks timed out (checker, warning
    only), 0 proof runs unfinished.
  - gc-ccmin3: 0 timeouts, 100 proofs checked, 0 checker timeouts, 0 unfinished.
  - gc: 0 timeouts, 100 proofs checked, 0 checker timeouts, 0 unfinished.
  - no wrong verdict, rejected proof or sanitizer report.

Deviations: none. The rc of the regress run is inferred from its final line, not measured directly.

## M1-r2 benchmark stage (benchmark worker, 2026-11-23)

Release build of 25216c2 (`build/bench-M1-r2`), 376 instances, 60 s, 48 jobs on cores 48-95; default and `-dl` seeds 1-3,
mode1, mode2, ccmin3 seed 1; compared with the reused same-machine `baseline-c96-*` runs and with `M1-r1-*`. No discrepancy,
no error. Differences to the baseline are within seed noise in every configuration (PAR2 new-base: default +0.24 s, dl +0.05 s,
mode1 +0.41 s, mode2 -1.10 s, ccmin3 -1.32 s, all CIs contain 0); against round 1 PAR2 -0.34 s (default, dl) and
identical-search CPU ratio 0.95. No proof run, no ablations (budget). Report: `bench/results/M1-r2-report.md`, commit 5b56822.

## M1 round 3: diagnosis of B1 and plan (coordinator, 2026-11-23)

Review `doc/rewrite/reviews/M1-r2.md`: not approved, one blocking item (B1): on identical searches of the DW family
the new binary is 12-27% slower than the baseline under the benchmark protocol; the round-2 family gate was not
evaluated; cause unknown. No rebuttal: the reviewer's measurements reproduce, and the round-2 gate table above was
wrong to call the load gate evidence. The coordinator's own measurements follow (prototype and scripts in
`/home/ec2-user/miniqu-work/coord/r3/`, nothing of it committed).

### Cause: 64 bytes of watch-list headers per literal

- DW-unsat-09-22-1 (default, seed 1): 6785 conflicts, 208 million propagations, no reduction, no collection. The time
  is propagation, and every propagated literal reads its list headers. Run alone on an idle machine the new binary
  is faster than the baseline (6.61 s against 6.95 s) and smaller (36 MB against 43 MB peak RSS), so the deficit is
  not instructions and not total memory; it is what is hot.
- The instance has 74039 solver variables, 148078 literals. New binary: one `alignas (64)` record per literal (two
  `std::vector<Watch>` of 24 bytes and two flags): 9.5 MB. Old solver: two `OccLists`, 16 bytes of `vec` header per
  literal and kind: 4.7 MB, four literals per cache line. Eight processes share a 32-MB L3 cache (4 MB each, 1 MB of
  L2 per core): the header array alone is more than twice a process's share. Without `alignas` the record is 56
  bytes, which is why the reviewer's experiment 3 left the table at 1.20.
- Round 2 introduced the record because `load_measure.py` reported a gain (decision E1/E2). That instrument mixes
  instances within an L3 group and lets cores go idle, so it did not show the cost. **E1's sentence "not a close
  call" is withdrawn**; its deferred M2 candidate (16-byte list type, 32 bytes per literal) is the fix and is done now.
- Prototype `v32` (`coord/r3/v32/watch.hpp.diff` against `src/watch.hpp` at `5ea3adf`; everything else unchanged):
  a 16-byte list (pointer, 32-bit size and capacity, `realloc`, growth 3/2), `alignas (32)` record with the two lists,
  dirty flags in a separate array of two bytes per literal. Same search (DW-unsat-09-22-1: 6785 conflicts, 208403301
  propagations, 624908363 ticks as before), 33 MB peak RSS.
- Reviewer's reproducer with a third arm (`coord/r3/l3x.sh OUT 0 "" base=... new=... v32=...`: the eight instances of
  the DW group on cores 0-7, one binary at a time, two rounds, 40 s; user seconds, mean of the two rounds; `new` is
  `build/bench-M1-r2/miniQU`, sha256 `30bd8fe6b956`):

  | instance | baseline | new | ratio | v32 | ratio |
  |---|---:|---:|---:|---:|---:|
  | DW-sat-08-22-1 | 2.04 | 2.98 | 1.46 | 2.19 | 1.07 |
  | DW-sat-08-23-1 | 1.81 | 2.54 | 1.40 | 2.15 | 1.18 |
  | DW-sat-09-26-1 | 3.34 | 3.46 | 1.03 | 3.15 | 0.94 |
  | DW-unsat-09-22-1 | 8.89 | 11.80 | 1.33 | 8.39 | 0.94 |
  | DW-unsat-09-23-1 | 17.98 | 19.55 | 1.09 | 18.55 | 1.03 |
  | DW-unsat-10-25-1 | 24.48 | 29.19 | 1.19 | 23.18 | 0.95 |
  | geometric mean | | | 1.239 | | 1.016 |

  Mode 1 (`-mode=1`, same script; DW-unsat-10-25-1 not solved in 40 s by any arm):

  | instance | baseline | new | ratio | v32 | ratio |
  |---|---:|---:|---:|---:|---:|
  | DW-sat-08-22-1 | 1.94 | 2.56 | 1.32 | 1.89 | 0.97 |
  | DW-sat-08-23-1 | 1.73 | 2.57 | 1.49 | 1.71 | 0.99 |
  | DW-sat-09-26-1 | 6.46 | 7.08 | 1.10 | 6.81 | 1.05 |
  | DW-unsat-09-22-1 | 8.88 | 12.47 | 1.40 | 8.73 | 0.98 |
  | DW-unsat-09-23-1 | 9.59 | 13.31 | 1.39 | 12.18 | 1.27 |
  | geometric mean | | | 1.333 | | 1.048 |

- Not measured by the coordinator: the chess family in mode 1 (1.12 in the benchmark run), `cross.sh` and `nb.sh`
  with the prototype, the whole benchmark set. One instance stays high in mode 1 (DW-unsat-09-23-1, 1.27, two
  rounds). R3-T3 measures these; they are not claimed here.

### Decisions

- **D1. Watch lists**: `WatchList` of 16 bytes and a 32-byte record per literal (ARCH 6.1, rewritten in this commit).
  This is MiniSat's `vec<Watcher>` in size and growth, so the owner's constraint (watch lists as in MiniSat/miniQU,
  collection in access order) is kept, more literally than with `std::vector`. Task R3-T3.
- **D2. Load instrument**: `bench/load_measure.py` results up to now (`M1-r2-load-*`, gate F3 of round 2) are not
  evidence about benchmark runs. R3-T1 changes the placement to the one of `run.py` (one window of the name-sorted
  instance list per L3 group, every core kept busy). ARCH 5.2's rule "layout decisions are measured under benchmark
  load" stands with the corrected instrument and `bench/l3.sh`.
- **D3. Benchmark reports** evaluate the gate of the round line by line with `bench/gate.py` (R3-T2) and paste its
  output; a report may not state "blocking items: none" while a line of that output says FAIL without a recorded
  decision. Instances that hit the memory limit are listed (2.1 and 5.2-3 hit 8 GB in every run of both binaries;
  the round-2 report's "no MEMOUT problems" was wrong in wording, the verdict counts were right).
- **D4. Unused functions** (review suggestion): `Watches::init` is removed in R3-T3 (`resize` is what the solver
  calls). `Internal::shrink_constraint` and `Proof::strengthen` stay: vivification and strengthening (M3) are their
  callers, both are unit-tested, and the layout work of round 2 (trailing words moved on shrink) is exactly what
  they exercise.
- **D5. `redundant` cannot be cleared in place** (review suggestion): added to ARCH 5.2 in this commit.
- **D6. Mode 1 pooled ratio** (1.06 in round 2): re-evaluated after R3-T3 by the benchmark stage; if it is still
  above about 1.03 it is recorded here as a known deficit with its per-family table.
- **D7. Proof coverage on the benchmark set**: one `--proof-check` run of the default configuration in the benchmark
  stage of round 3 if the two hours allow it (budget decision); otherwise stated as not measured.

### Round-3 gates

| gate | measured by |
|---|---|
| `bench/l3.sh` DW group, default: geometric mean new / baseline at most about 1.05 | R3-T3 |
| same search as round 2 (conflicts, propagations, ticks equal on the smoke set and the load instances) | R3-T3 |
| fuzz: release 1:300 matrix, asan 1:100 `-t 240`, QDIMACS 1:300; ctest; smoke with proofs | R3-T3 |
| peak memory not above round 2 on 1.3, 5.2-1, DW-sat-08-22-1, amba2f9n.sat (the record shrinks) | R3-T3 |
| benchmark stage, `bench/gate.py`: pooled at most about 1.03, no family (n >= 3) above 1.10, default and `-dl`; mode 1 reported, explained if above | benchmark stage |

### Worker tasks

- **R3-T1** (tooling): `bench/l3.sh` and its table, `cross.sh`, `nb.sh`; `load_measure.py` with L3-group placement.
- **R3-T2** (tooling): `bench/gate.py`, report rules in `bench/README.md`.
- **R3-T3** (solver): `WatchList`, 32-byte record, measurements, fuzz gate.

## M1-R3-T1 (worker, 2026-11-23): bench tooling with the placement of run.py

Built (commits f9d9c4f, f70f7da, results commit after them; no solver source touched):
- `bench/l3.sh` (+ `bench/l3lib.sh`, sourced by the three scripts: L3 check, seed arguments, neighbour loops), `bench/l3_table.py`, `bench/cross.sh`, `bench/nb.sh`. The neighbour loops of cross.sh and nb.sh run in their own process group (setsid, `timeout --foreground` so the solver stays in it) and only that group is killed; the reviewer's `pkill -f` is gone. Smoke-tested: no `miniQU` process left after a run, refusal exits 2 (cores across two L3 groups, existing OUT).
- `bench/load_measure.py` replaced: groups file, group g on L3 group g, instance j on core j of it, every core loops until every core has completed a run, unfinished runs discarded, per-group table, header "L3 groups, cores kept busy". `--copies` removed; `copy` is the repetition index; default `--timeout` 60. Extra checks: group windows must be consecutive in the sorted bench dir; a group larger than its L3 group is refused. A hidden `--sysfs-root` serves the fake-sysfs test.
- Tests: `bench/test_load_measure.py` (group parsing, placement, refusals, per-group means, loop bookkeeping with a fast fake instance running 3+ times next to a slow one) and `bench/test_l3_table.py` (ctest `bench-l3-table`, new). ctest in the release tree: 39/39 passed (bench tests included).

Chosen groups (windows of 8 consecutive sorted names; "qualifying" = identical search in M1-r2-default-s1 vs baseline-c96-default-t60-s1, baseline CPU 1-60 s):
1. DW (mandatory) CM-unsat-07-01-06-2 .. DW-unsat-11-26-1: 6 qualifying.
2. numeric 10.1 .. 4.1: 6 qualifying.
3. numeric 5.2-1 .. CM-sat-04-01-06-3: 4 qualifying.
4. chess mate_in_2 1982_WCSC-6_02 .. 2002_MAC-CH-6_03: 3 qualifying.
5. chess mate_in_3 2001_UKR-CH_06 .. 2014_FRA-CH_03: 6 qualifying (contains FRA-CH_03).
6. ex92_7S700 .. hadw11-12 (finan, finding_nemo, genbuf, hadw10-11): 3 qualifying.
Deviation: only numeric, CM/DW, chess and the hadw window have a window with three qualifying instances, so no "two other families" exist; I used a second numeric window and the chess mate_in_2 window (a different name family, same results family "chess").

Measurements (idle machine, lower half 0-47; baseline vs `build/bench-M1-r2/miniQU`, sha 30bd8fe6):
- `bench/l3.sh` default (results in `bench/results/M1-r3-l3-before/default.md`, raw `default.raw.txt`): geometric mean r2/base **1.243**, n=6 (DW-sat-08-22-1 1.503, 08-23-1 1.348, 09-26-1 1.069, DW-unsat-09-22-1 1.220, 09-23-1 1.095, 10-25-1 1.273). CM-unsat-07-01-06-2 and DW-unsat-11-26-1 time out at 40 s and are left out. Matches reviewer 1.25 and coordinator 1.24.
- `load_measure.py`, 2 rounds, tag `M1-r3-load-before` (default): overall geomean 1.032 (n=33); group geomeans DW **1.243** (n=6), numeric-1 0.909, numeric-2 0.928, chess_in_2 1.017 (n=8), chess_in_3 1.069, hadw 1.024. DW instances: 1.594, 1.771, 1.004, 1.072, 1.156, 1.053.
- Tag `M1-r3-load-before-mode1` (`-mode=1` on both): overall 1.067 (n=32); DW group **1.326** (n=5; DW-unsat-10-25-1 timed out and is unfinished); numeric-1 0.932, chess_in_2 1.055, hadw 1.042 (n=2).
- Acceptance 3 (DW group clearly above 1.10): met in both runs. Old `M1-r2-load-*` results used the mixed placement and are not evidence.

Notes for the next tasks: a round lasts about 61 s because the slowest instance of some group (the two CM/DW unsat ones, finan, genbuf) times out at 60 s; a run of 2 rounds x 2 arms takes ~4 min. The groups' unfinished instances are listed in each load.md. Rounds are only 2, so single-instance ratios (min-max columns) are noisy; the group geomeans are the evidence.
