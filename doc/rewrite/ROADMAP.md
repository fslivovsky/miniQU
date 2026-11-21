# miniQU rewrite: roadmap

Companion to `ARCHITECTURE.md` (referred to as ARCH). Milestones are done in
order; inside a milestone the numbered work packages are sized for one worker
task each and are done in order unless marked independent. `STATUS.md` records
what is finished.

Classes (D), (R), (N) of a technique are defined in ARCH 11.2; the invariants
INV-* in ARCH 4.3.

---------------------------------------------------------------------------

## 0. Rules that apply to every work package

### 0.1 Definition of done

A package is done when all of the following hold, and its `STATUS.md` entry
says so with the commands that were run:

1. `release`, `debug` and `asan` presets build without warnings (GCC), and
   `release` also builds with Clang.
2. Unit tests pass (`ctest`), including new tests for the new code.
3. `tests/regress.sh` passes for the **configuration matrix** below with at
   least seeds 1:300 on the `release` binary and seeds 1:100 on the `asan`
   binary (the `asan`/`debug` binaries run the internal `Checker`).
   Zero wrong answers, zero rejected proofs, zero crashes, zero sanitizer
   reports. A failure is reported with its reproducing command, never
   worked around.
4. If the package can affect performance: a benchmark comparison against the
   previous accepted state (0.3).
5. The header comment of each new technique file states class, QBF side
   conditions and proof steps; new options, statistics and profiles are in
   their tables; `ARCHITECTURE.md` is still true.

Configuration matrix (grows with the milestones; every new on/off option adds
"default with the option flipped"):

```
(default)      -dl      -mode=1      -mode=1 -dl      -mode=2      -mode=2 -dl
-ccminmode=3   -dl -ccminmode=3      -no-earlytseitin -legacyanalyze
```

Mode 2 configurations run without proof checking (`regress.sh -n`).
QDIMACS is covered by its own fuzz script (M1.8).

### 0.2 Correctness beats everything

Any disagreement (with the baseline, with `tests/qcir_eval.py`, between two
configurations, between QDIMACS and its QCIR conversion) and any proof the
Lean checker rejects is a blocking bug: stop feature work, minimise the
instance (`qbfdd.py` or by hand), fix, add the instance to
`tests/regressions/`. Never weaken a test, the `Checker`, or the Lean checker.

### 0.3 Benchmark protocol

Harness: `bench/run.py`, `bench/compare.py` (see `bench/README.md`). All 376
instances, one core per job on cores 64-127, `--mem-gb 16`, same limits for
every run that is compared.

- **Noise floor** (once, at the start of M1, and again whenever the machine
  setup changes): run the baseline binary twice at each tier; the set of
  instances whose result differs and the spread of PAR2 between the two runs
  are the noise band. Differences inside the band are not evidence.
- **Quick tier**: timeout 60 s. For iterating and for ablations.
- **Full tier**: timeout 600 s. Required for milestone acceptance and for any
  change of a default.
- **Configurations**: default and `-dl` are both first-class (the README
  deliberately recommends neither); every acceptance run covers both. Modes 1
  and 2 are benchmarked at the quick tier once per milestone.
- **Proofs**: acceptance runs use `--proof-check` (proofs of instances solved
  within 20 s are checked by the Lean checker and deleted).
- **Report** (markdown from `compare.py`, committed under
  `bench/results/<tag>/` together with the CSV): discrepancies first; solved
  SAT/UNSAT/total; PAR2; instances gained and lost, by name; per-family table;
  largest speedups and slowdowns; peak memory; proof-check statistics. A
  claim "X helps" needs: more solved or lower PAR2 outside the noise band at
  the full tier, in at least one of the two main configurations, without a
  loss outside the band in the other, and no family that collapses without an
  explanation. Report losses as prominently as gains.
- **Ablations**: a technique is judged by the same binary with its option on
  and off, not by comparing different commits.
- Tags: `<milestone>-<what>-<config>-t<timeout>`, e.g. `m2-tiers-dl-t600`.

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
  `assign`, `propagate`, `decide`, `backtrack`, `analyze`, `learn`,
  `bump`, `restart` (Luby), `reduce` (old policy, see notes), `collect`
  (arena GC only), `model`, `external`, `solver`, `app`. First
  end-to-end fuzzing against the baseline.
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
- **M1.9 Parity gate.** Full configuration matrix, seeds 1:2000 (`release`)
  and 1:300 (`asan`); noise floor; full-tier benchmark of default and `-dl`
  against the baseline with proof checking.

Acceptance of M1: no discrepancies; all proofs accepted; solved counts at the
full tier not below the baseline's by more than the noise band in either main
configuration, PAR2 not worse outside the band; peak memory not higher than
the baseline's on any instance by more than 10% (expected to be much lower on
large files); reviewer accepts structure and readability.

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

`collect.cpp`: after new root units, delete constraints with a root-disabling
literal (class R with trivial obligations: the variable is fixed) and remove
root-vanished literals (class D).

- QBF side condition: a vanished literal is removed only if the reason of its
  root assignment has the **same kind** as the constraint (ARCH INV-DERIVED);
  otherwise it stays in the constraint forever, which is harmless. A
  *disabled* constraint is deleted whatever the reason's kind: substituting a
  root-fixed variable preserves the truth value, and deletion is always legal
  in a proof.
- After strengthening: `qreduce`; unit and empty results are handled.
- Proof: `strengthen` with chain = constraint id, unit ids; deletions.
- QDIMACS: initial cubes range over the remaining irredundant clauses; the
  fixed literals are not part of new cubes (they are substituted away).

### M2.2 Tiers, `used` counters, glue-based reduction (adopt; owner requirement)

- Glue is stored in the header; `used` (2 bits) is set when a redundant
  constraint is a reason or conflict in analysis: `used = 1`, or `2` if its
  glue is within tier 2. At that moment the glue is recomputed from the
  current levels and lowered if smaller (promotion).
- Tiers per kind (clauses and cubes have very different glue distributions;
  cubes from satisfying assignments are long): tier 1 `glue <= tier1glue`
  (default 2), tier 2 `glue <= tier2glue` (default 6), tier 3 the rest.
- `reduce ()` every `reduceint * (reductions + 1)` conflicts: protect
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
literals whose reason has the same kind (unit ids appended to the chain).
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

`--arenasort=1` (ARCH 5.3): relocation walks variables by descending score
and saved phase first. Measured by propagations per second on the quick tier.

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

Acceptance of M2: every adopted item has a full-tier ablation in both main
configurations; the combined default beats M1 outside the noise band (solved
or PAR2) in at least one main configuration and loses in neither; proofs with
minimisation enabled are accepted across the matrix (seeds 1:2000).

---------------------------------------------------------------------------

## M3. Inprocessing framework and bounded variable elimination

### M3.1 Framework

`inprocess.cpp`, `flags.hpp`, `occs`, occurrence mode, budgets, `preprocess`
(ARCH 10.1-10.3); `check_invariants ()` after every pass; backward
subsumption and strengthening for use by elimination (`subsume.cpp`, class D:
a subsumed constraint is deleted; if `D ∨ l` and `C ∨ ¬l` with `D ⊆ C` then
`C ∨ ¬l` is replaced by `C`, one resolution step; pivot of either quantifier,
which is QU-resolution and accepted by the checker in every mode; `qreduce`
afterwards). An irredundant constraint may only be subsumed away by an
irredundant one (or the subsuming one is made irredundant).

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
`Eliminated` (heaps, block counter, dependencies; ARCH 10.3); push to the
extension stack if `x` is in the certificate block (ARCH 10.4); schedule the
variables of the resolvents; backward-subsume with the resolvents.

Why E3 is needed and sufficient (clause case; the cube case is dual). Write
the matrix as `F_x ∧ G`, `F_x` the clauses containing `x`. By E3 all
variables of `F_x` are quantified no later than `x`'s block. If the formula
with `∃x` moved to the innermost position is true, then for every assignment
`α` of the variables up to `x`'s block that a play can reach, `F_x|α` is
satisfied by some value of `x`; choosing that value as a function of `α`
alone gives a strategy for `x` at its original position, and `G` does not
mention `x`. Moving `∃x` inward never makes a true formula false. So `∃x`
can be moved innermost, where `∃x. F_x` is propositionally equivalent to the
set of non-tautological resolvents on `x`. Without E3 this fails: for
`∃e ∀u ∃f` with clauses `(e ∨ f ∨ u) (e ∨ ¬f ∨ u) (¬e ∨ f ∨ ¬u) (¬e ∨ ¬f ∨ ¬u)`
the formula is false, but all resolvents on `e` are tautological. This also
shows that dropping resolvents that are tautological on a *universal*
variable is correct here, although Q-resolution would forbid deriving them.

Why E2. A cube containing `x` would refer to a variable that no longer
exists in the clause database: it is never assigned, so such a cube could
never fire, and removing the literal from the cube is not a cube derivation.
Strict E2 keeps every stored cube meaningful. Stored cubes without `x` stay
sound: a cube `t` with `t ⇒ F` and `x ∉ t` satisfies `t ⇒ ∃x.F`.

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
  weaker; the ablation must cover both placements. (Relaxing E3 with a
  dependency argument is M5 item 3 and needs the owner's approval.)
- **INV-COMPLETE (QCIR).** Elimination preserves it: a unit-propagation
  refutation under a total input assignment that propagates `x` from
  `C ∨ x` and uses it in `¬x ∨ D` is simulated by the resolvent `C ∨ D`
  (if the resolvent is tautological, `D` contained a true literal and was not
  usable), `qreduce` and subsumption only strengthen, and E4 guarantees all
  resolvents are present. So after elimination, as before, a full assignment
  of the inputs produces a conflict in one of the two databases.
- **Learnt constraints.** Learnt `K`-constraints with `x` are deleted (they
  need not satisfy E3). Learnt `K`-constraints without `x` remain valid: they
  are consequences of the old formula, and the elimination argument applies to
  the old formula conjoined with them. Learnt `K'`-constraints: E2.
- **Initial cubes / model generation (QDIMACS).** After elimination the
  solver works on the formula with matrix `∃x.F` over the remaining
  variables. `model.cpp` hits the current irredundant clauses, which are the
  resolvents: the cube is an implicant of the new matrix. Old cubes are
  implicants of it as well (above). Universal elimination has nothing to do
  for QDIMACS input (no original cubes).
- **Certificates.** Extension stack, ARCH 10.4; until validated, certificate
  block frozen when `--cert` is given.
- **Dependency learning.** Reset dependencies when a decision variable is
  eliminated.
- **Mode 2.** Only irredundant constraints are resolved, and they contain no
  complementary literals. Allowed.
- **Trail and reasons.** Root level only; reasons of root assignments are
  unit constraints and never contain an unassigned `x`.

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
  QDIMACS elimination, namely E2 against learnt cubes, model generation on
  resolvents, and the extension stack, is validated only by fuzzing against
  the baseline, the brute-force evaluator, and the QCIR conversion of the
  same instance. M5 item 6 would close this gap.
- The proof shows that the verdict is right; it does not show that E2/E3
  were respected. For QCIR input a violated side condition cannot produce a
  wrong verdict, because both databases still contain only derivable
  constraints (resolvents are sound whatever the position of the pivot); at
  worst it breaks INV-COMPLETE and shows up as a **stuck state**
  (`stats.modelcubes > 0`; fatal when a proof is written). For QDIMACS input
  a violated side condition can produce a wrong TRUE, because cubes are then
  taken from models of a matrix that is too weak. Hence: debug builds
  re-verify E2/E3 for every eliminated variable in `check_invariants ()`,
  and QDIMACS fuzzing is mandatory for this milestone.
- Mode 2 has no proofs.

### M3.5 Work packages

1. Framework and subsumption (M3.1), with elimination switched off.
2. Clause distribution for QCIR gate variables, preprocessing only, proofs
   on. Matrix + Lean.
3. Cube distribution (the same code through the kind template; verify that
   no clause-specific assumption crept in).
4. QDIMACS: E2 bookkeeping against learnt cubes, extension stack, certificate
   tests, then lifting the `--cert` freeze.
5. Inprocessing rounds (after search has started: learnt constraints exist,
   bounds increase), dependency reset.
6. Gate-aware elimination (optional): the encoder marks definition
   constraints (`gate` bit); when the complete definition of `x` (both
   implication directions) is present, only definition x non-definition
   resolvents are added. Same proof steps. Plaisted-Greenbaum gates of one
   polarity have no complete definition and take the plain path.

Acceptance of M3: matrix extended by `--elim` on/off, `--no-earlytseitin`
with elimination, `-cert`; seeds 1:3000 QCIR with Lean checking, 1:3000
QDIMACS; `stats.modelcubes == 0` on every QCIR benchmark run; full-tier
ablation in both main configurations with per-family analysis of where
elimination applies (number of eliminated variables, blocked by E2/E3/E4
each).

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
  resolved away (INV-DERIVED): if any such literal is not already in `C`,
  the candidate is skipped.
- **V5** `qreduce (D)`; if `D` is a proper subset of `C`, replace `C` by `D`
  (irredundant stays irredundant; a learnt `C` gets its glue recomputed and
  may be promoted); empty `D` decides the formula; unit `D` is a root unit.
- **V6** mode 2 is excluded at first (its watch invariant differs); modes 0
  and 1 only.

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

Acceptance: matrix with `--vivify` on/off; Lean-checked seeds 1:3000;
QDIMACS fuzz; full-tier ablation in both main configurations, with counts of
candidates, strengthened constraints and removed literals per kind and tier.

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
| 5 | **Blocked constraint elimination (QBCE)** and the cube dual | R | blocking literal primary, every resolvent on it tautological on a variable not to the right of it; E2 for the blocking variable. QCIR: does **not** preserve INV-COMPLETE in general (propagation gets weaker), so it is only admissible there together with a fallback for the stuck state, which does not exist when proofs are on. QDIMACS: admissible; learnt cubes must be checked as in E2; extension stack entry | deletion only | medium for QDIMACS input, doubtful for PG-encoded QCIR (elimination already removes what QBCE would) |
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
