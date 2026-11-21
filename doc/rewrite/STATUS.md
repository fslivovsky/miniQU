
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
