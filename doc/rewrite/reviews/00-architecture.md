# Review 00: architecture and roadmap

Reviewer, 2026-11-21. Reviewed: `ARCHITECTURE.md` and `ROADMAP.md` at commit
aa308d1, against the old solver (`minisat/core`, c39005a),
`doc/proof-format.md`, CaDiCaL (`~/cadical/src`), the test and bench tooling,
and the owner's requirements.

**Verdict: not approved yet. Five blocking items, all of them changes to the
two documents (no design reversal).** B1 and B5 affect what M1 code is
written; B2 and B3 define what counts as evidence; B4 corrects a soundness
argument that M2.1, M3 and M4 rely on. Once they are fixed, M1.1 can start.

The design itself is sound in outline, and I found no technique that is
unsound for QBF as specified. The old-code claims I spot-checked are correct
(heap per block, ids in a `CRef` map rebuilt at GC, `ccmin-mode=3` disabled
when ids are recorded, dependency reset every 20th restart, `relocAll` in
watch order, `simplify()` not called during search).

---------------------------------------------------------------------------

## 1. Owner's hard constraints

| constraint | honoured? | remark |
|---|---|---|
| Start from miniQU and port it | yes | M1 is a port with a parity list and porting notes; three analyses ported as they are |
| CaDiCaL style, modern C++ | yes, with one deviation | `Internal` + one file per technique, X-macro tables, limits. Formatting deliberately departs from CaDiCaL (S9) |
| Arena retained | yes | ARCH 5: region allocator, 32-bit refs, copying GC |
| Watchers "stored in memory based on accesses" | yes, under one reading | ARCH 5.3 reads it as MiniSat's `relocAll`: GC lays constraints out in watch-list order. I agree this is the natural reading, but the phrase is ambiguous; record the interpretation in STATUS.md as a decision the owner can veto |
| Tiered databases, LBD cleaning | yes | M2.2, per kind |
| BVE: eliminated variable rightmost | yes | E3, by depth, same block allowed. Checked on irredundant constraints; learnt ones with `x` are deleted |
| BVE: existential (universal) only if not in cubes (clauses) | yes, stricter | E2 also counts learnt constraints of the other kind |
| Proof logging for every technique, Lean-checked | partly | QCIR: yes for M1-M4, no checker extension needed, and I agree with that analysis (a BVE resolvent is one derived step with two premises; `strengthen` is derive + delete). QDIMACS: no proofs at all, so QDIMACS-specific elimination is unverified (S2). Proof-check *coverage* is too weak as specified (B1, B3) |

---------------------------------------------------------------------------

## 2. Blocking

### B1. The fuzz corpus does not exercise the search machinery

ROADMAP 0.1 item 3 makes `tests/regress.sh` over the configuration matrix
the correctness gate. I ran the baseline on the instances `tests/fuzz.sh`
generates:

| generator | conflicts (baseline, default options) |
|---|---|
| `qcir_fuzz.py` seeds 1-12 | 0, 1 or 2 |
| `qcir_fuzz.py --vars 16 --gates 60 --blocks 8`, seeds 1-3 | 0, 1, 1 |
| `qcir_gen.py qcnf 1 7 7` | 5 |
| `reach 1 8 16`, `game 1 5`, `synth 1 8` | 1 each |
| `reach 1 15 16`, `game 1 30`, `game 2 30`, `synth 1 25` | 1 each; `synth 2 25`: 3; `reach 1 19 12`: 126 |
| `qcnf 1 40 5` | 2 475 634 (4158 restarts) |
| `qcnf 1 60 5.5`, `qcnf 2 60 5.5` | no result within 30 s |

So nearly every proof-checked fuzz instance ends after a handful of
conflicts, and the few that do not are too long to proof-check (STATUS.md
already reports 400 MB proofs and checker timeouts). With this corpus, 300 or
3000 seeds never reach database reduction, arena GC and relocation (an owner
constraint), restarts, tiers, root simplification, inprocessing rounds, or
elimination after learning. "Zero rejected proofs" would then say almost
nothing about M2-M4, and the 33 smoke instances are too few to fill the gap.

Required changes to ROADMAP 0.1 before M1.3:

1. **Stress configurations** in the matrix from M1 on, using options that
   make every scheduled event fire on tiny instances: reduce every few
   conflicts, GC at every safe point (`gcfrac=0`), restart every conflict,
   dependency reset every restart; from M2 tier limits 0/1 and root
   simplification every conflict; from M3/M4 inprocessing every few conflicts
   with unbounded effort. These options must exist with ranges that allow
   it (the old `minlearnts` is only a lower bound, so it is not enough).
2. **Generator parameters** that give 10^2 to 10^4 conflicts with proofs the
   Lean checker finishes; the worker reports the conflict histogram of the
   corpus in STATUS.md.
3. **A coverage assertion**: `regress.sh` sums the solver's counters over a
   configuration (reductions, collections, restarts, strengthened,
   eliminated, vivified, ...) and fails if a counter belonging to a technique
   under test is zero. Without this, nobody notices when a test stops
   testing.

### B2. The benchmark protocol cannot separate an effect from heuristic luck

ROADMAP 0.3 defines the noise band as the difference between two runs of the
same binary. The solver is deterministic, so that measures machine timing
noise only. A code change perturbs the search itself (ARCH says M1 is not
trace-identical to the baseline), and that variance is not in the band.

The partial `baseline-t180` run in the tree (358 of 376 instances so far)
shows 166 solved, 189 timeouts, 3 memouts. More than half the set is
unsolved, and each claim will be decided by a few instances near the timeout.
M2 has six "experiment" items times two configurations, each accepted on "a
gain outside the band in at least one configuration". With a band that
ignores search variance, some of them will be accepted by chance.

Required changes:

1. Define what `seed` perturbs (ARCH 9.1 lists the option but random
   decisions are dropped): for example a small random perturbation of the
   initial scores, off for `seed=0`. The baseline has `-rnd-init` and
   `-rnd-seed`, so its variance can be measured the same way.
2. Noise band = spread of solved count and PAR2 over k seeds of the *same*
   binary, k >= 3 at the full tier and k >= 5 at the quick tier. Compared
   arms use the same seeds.
3. A claim needs a paired per-instance comparison over all seeds (bootstrap
   confidence interval of the PAR2 difference, or a sign test on instances
   solved by both), reported with per-seed solved/PAR2, not one pair of
   numbers.
4. Compared runs use the same `--jobs` and memory limit, recorded in the
   report (run.py already stores them). The partial baseline run used 8 GB
   and 64 jobs while 0.3 says 16 GB; settle the limit before any baseline
   number is used.

Cost is acceptable: a full-tier run is at most about an hour on 64 cores.

### B3. Proof-check coverage is unspecified and currently low

Acceptance runs check proofs only for instances solved within 20 s, and
checker timeouts count as warnings. In the partial baseline run 115 of 166
solved instances are within 20 s; the other 31% are never checked, and those
are the runs in which reduction, GC and several inprocessing rounds happen.
Together with B1 this leaves the owner's requirement "use the Lean proof
checker to verify the proofs" unmet for exactly the new techniques.

Required changes to ROADMAP 0.3 and the milestone gates:

1. Every acceptance report states coverage: solved, proofs attempted,
   accepted, rejected, checker timeout/memout by instance name.
2. At milestone gates, proofs are attempted for every instance solved at the
   quick tier (60 s), with `qlrup-trim` first if that makes the difference and
   a generous checker limit. Coverage may not drop between milestones without
   an explanation.
3. Proof-logging overhead (time and proof size, on versus off) is measured
   once per milestone.

### B4. The soundness criterion for QDIMACS (ARCH 11.1, 4.5) is wrong as stated

11.1(b) requires every stored cube to remain an implicant of the new
irredundant clause set `F'`, and says subsumption, strengthening and
vivification "satisfy this trivially" because they are equivalence
preserving. They are not propositionally equivalence preserving once a
*learnt* clause takes part: a learnt clause is a Q-resolution consequence
(with universal reduction), not a propositional consequence of `F`. Example:
prefix `... ∃y ∀w ∃z`, clauses `(¬y ∨ w ∨ z)`, `(¬y ∨ w ∨ ¬z)` give the
learnt clause `(¬y)`; strengthening an irredundant `(x ∨ y ∨ a)` with it to
`(x ∨ a)` makes a stored cube containing `y ∧ w` no longer an implicant of
the matrix. The same applies to M2.1 (removing root-vanished literals) and
M4 (vivifying irredundant clauses with learnt clauses as reasons). So (b)
is violated by techniques the roadmap calls trivially fine, and the
follow-up argument for elimination ("old cubes are implicants of `∃x.F`")
no longer applies after such a step.

I believe the techniques are nevertheless sound, under a different
invariant, which the documents should state and argue instead:

> With `G` the current irredundant clauses, `T` the stored cubes and `Π` the
> current prefix: `Π.(G ∨ ⋁T)`, `Π.G` and the input formula have the same
> truth value.

- A new model cube `t ⊨ G` leaves `G ∨ ⋁T` unchanged; cube resolution and
  existential reduction preserve the truth value of `Π.(ψ ∨ ⋁T)` for any `ψ`.
- Strengthening `G` to `G'` with `G' ⊨ G` and `Π.G' ≡ Π.G`:
  `Π.G' ≤ Π.(G' ∨ ⋁T) ≤ Π.(G ∨ ⋁T) = Π.G = Π.G'`.
- Elimination of `x` (E2: `x` in no cube; E3 on `G`): `∃x` can be moved
  innermost in `G ∨ ⋁T`, not just in `G`. Where some cube is true the value
  of `x` is irrelevant; elsewhere the matrix is `G` and the E3 argument
  applies. This step is missing from ROADMAP M3.2 and is what makes E2 + E3
  sufficient in the presence of old cubes.

Required: replace 11.1(a)-(c) and the "rules" paragraph of 4.5 by this
invariant (or a corrected equivalent), redo the per-technique arguments in
M2.1, M3.2/M3.3 and M4 against it, and state whether irredundant constraints
may be strengthened using redundant ones (if yes, the argument above is
needed; if no, say so and the old criterion survives). QCIR input is not
affected: INV-DERIVED carries it.

### B5. The layering claim in ARCH 3 does not hold for the extension stack

ARCH 3 says each layer depends only on the layers below and that `Internal`
never sees user variables. ARCH 10.4 puts the extension stack in `External`
and has `elim.cpp` (Internal) push to it, as CaDiCaL does through its
`external` back-pointer. That is an upward dependency, and `External` is
written in M1.3. Decide now: keep the stack in `Internal`, in internal
literals (`extend.cpp` moves to the internal layer; `External` only
translates the result), or document the back-pointer as the single
exception. I recommend the first; `External` is meant to be thin.

In the same paragraph, say who owns the per-variable proof numbers that
`Proof` needs (they arrive through `add_var`), and which layer
`certificate.cpp` versus `External::val` belongs to.

---------------------------------------------------------------------------

## 3. Non-blocking findings and suggestions

**S1. Measure BVE yield before building M3.** For QCIR, E2 leaves only gate
variables, and E3 leaves only gates all of whose consumers sit in the same
block. With `--earlytseitin` (the default) that may be few. This is a static
property of the circuit: a short script over the 376 benchmarks, for both
placements, gives the number of initially eligible gate variables per family.
Run it at the start of M3, put the table in STATUS.md, and use it to decide
whether to ask the owner about M5 item 3 before M3 rather than after. Note
that the INV-COMPLETE argument in M3.3 does not use E3 at all, so for QCIR
E3 is a restriction imposed by the requirement, not by soundness; the owner
should see that together with the numbers.

**S2. QDIMACS elimination is unverified surface with no benchmark behind
it.** All 376 benchmarks are QCIR; QDIMACS has no proofs. M3.5 item 4 (E2
bookkeeping against learnt cubes, model cubes over resolvents, extension
stack) is the only part of M1-M4 where a mistake gives a wrong TRUE that no
checker sees. Suggestions: keep elimination off for QDIMACS input by default
until M5 item 6 or strong fuzz evidence exists; let the internal `Checker`
validate every model cube against the live irredundant clauses (cheap, and
it catches the wrong-TRUE scenario of M3.4 directly). Also, the cube half
of the extension stack can never fire in M3: a universal input occurs in
clauses in both input formats, so it is never eliminated. Implement clause
entries only and assert on the other case.

**S3. Constraint header size.** 16 bytes for every constraint, versus 4 in
the old solver (12 for learnt). Tseitin originals are mostly binary and
ternary, so a binary constraint grows from 12 to 24 bytes, which works
against the locality argument for keeping the arena. Measure propagations
per second and RSS against the baseline on the largest instances in M1.3
before the layout is taken as final; a 12-byte header (size and flags packed,
or a narrower id) is the fallback. The accessor-only rule in 5.2 makes that
change local; keep it that way.

**S4. Name the propagation variants and share the loop.** By M4 there are:
watch propagation for mode 0 and mode 1, both kinds; `propagate_ldq`;
`propagate_kind` for vivification (mode 0 without conflict completion, mode
1); `propagate_occs`. ARCH 7.2 should say that the watch loop exists once,
parameterised at compile time by kind and by the rule for a remaining
secondary literal (conflict / propagate / ignore), with mode dispatch outside
the loop. Otherwise workers will copy the MiniSat loop four times.

**S5. Be explicit about what "pluggable" means.** With a CaDiCaL-style
`Internal`, adding a technique touches `internal.hpp`, the option, stats and
profile tables, `inprocess.cpp`, possibly a header bit and the test matrix.
That is acceptable and is what the owner asked for, but the ownership rule in
ARCH 3 is enforced by nothing. Two cheap aids: group each technique's state in
a small struct member (`Depend`, `Eliminator`, `Vivifier`) instead of loose
fields, and state the rule reviewers will apply: a technique that needs an
edit in `propagate.cpp`, `analyze*.cpp` or `assign.cpp` is a design change
and needs a note in STATUS.md.

**S6. Port-fidelity diagnostics for M1.** Since search is not identical,
"within the noise band" mixes engine speed with heuristic drift. Add to the
M1.9 report: propagations per second and conflicts per second per instance
against the baseline, and the conflict-count ratio on instances both solve.
A faithful port shows ratios near 1; a systematic shift points at a lost
behaviour from the porting notes.

**S7. Signals.** "Flushed on termination signals" (ARCH 8.2) must not mean
writing a 1 MiB buffer from a handler. The handler sets the flag
`terminate ()` sets; the search loop returns; the app flushes.

**S8. Scope of the internal `Checker`.** It is "on by default in debug/asan
builds", but model cubes (QDIMACS) and mode 2 steps are not replayable. State
what it does there (off, or premise-free steps validated as in S2).

**S9. Formatting.** CaDiCaL ships a `.clang-format` (76 columns,
`SpaceBeforeParens: Always`). ARCH 12 chooses LLVM style at 100 columns while
the documents themselves write `f ()`. This is cosmetic, but it is the most
visible part of "in the style of CaDiCaL"; record it in STATUS.md as a
decision the owner may reverse, before thousands of lines exist. Also,
`--arenasort` means something different from CaDiCaL's `arenasort` (the
analogue is `arenatype`); rename to avoid confusion.

**S10. Things specified before they are needed.** `Flags` statuses
`Substituted` and `Pure`, the `gate`/`subsume`/`vivify`/`vivified` header
bits, and the remark about a future `compact` pass belong to M3+/M5. Reserve
the bits in the layout comment but add enumerators and accessors with the
technique that uses them (the "no dead options" rule applies). `Solver` /
`External` / `Internal` is three layers for a single-shot solver whose
variable mapping is nearly the identity; either say what `External` does
beyond translation or let `Solver` hold it directly.

**S11. Extension stack wording (ARCH 10.4).** "The rightmost condition
guarantees that every other variable in a pushed constraint belongs to the
same block" is not what E3 says (earlier blocks are allowed). It holds only
because the certificate block is the outermost one; say that, and say what
happens when a variable of that block is unassigned at the end (the `-dl`
wrinkle), since reconstruction needs their values.

**S12. Gate on quick-tier modes.** Modes 1 and 2 are benchmarked "once per
milestone" without an acceptance criterion. Add one (no discrepancy; no
collapse relative to the previous milestone) so that regressions there are
not discovered late.

---------------------------------------------------------------------------

## 4. What is good and should not change

- INV-DERIVED as a design rule: one code path for originals, removal of
  root-vanished literals only for same-kind reasons. It removes the old
  proof / non-proof split and makes verdict soundness for QCIR independent
  of every later technique.
- INV-COMPLETE with a counter (`stats.modelcubes`) that turns a completeness
  bug into a visible event, and the honest list in M3.4 of what proofs do not
  cover.
- The (D)/(R)/(N) classification, and the conclusion that M1-M4 need no
  checker extension. I checked BVE resolvents, `strengthen`, vivification
  chains and extended minimisation chains against `doc/proof-format.md` and
  agree.
- Kind-generic code through `kval`; `qreduce` versus `reduce` naming; ids
  inline instead of the hash map; `mark_garbage` as the only source of
  deletion steps; the internal `Checker` in debug and asan builds.
- Ablations on one binary with the option on and off; default and `-dl` both
  first-class; losses reported as prominently as gains.
- The "decided against" list for M2 with reasons, and the explicit request
  for owner approval before relaxing E3.
