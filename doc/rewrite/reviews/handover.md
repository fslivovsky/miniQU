# Hand-over review: bounded variable elimination (M3) and vivification (M4)

Reviewer verdict: **not approved as it stands: one blocking defect (B1, invalid
`-cert` output).** B1 is not in the two new units. It is in root
simplification (M2-T4, on by default) and shows with default options;
elimination makes it reachable on more instances, and the two new units have
the same pattern in their own "empty result" paths. Apart from B1 I found no
wrong verdict, no crash, no rejected proof and no changed default in
elimination and vivification, by reading and by the runs of section 5.

Reviewed: branch `rewrite/cadical-style` at `36ffcfa`, range `3bbf085..HEAD`.
Read in full: `src/elim.cpp`, `src/elim.hpp`, `src/vivify.cpp`,
`src/vivify.hpp`, `src/flags.hpp`, the diff of `check.cpp`, `constraint.hpp`,
`internal.cpp/.hpp`, `learn.cpp`, `propagate.cpp`, `simplify.cpp`,
`options.hpp`, `limit.hpp`; and, for the interactions, `propagate.hpp`,
`simplify.cpp`, `backtrack.cpp`, `assign.cpp`, `depend.cpp`, `prefix.cpp`,
`certificate.cpp`, `encode.cpp`, `mark_garbage`. Unit tests were not read line
by line. Release build of HEAD: 0 warnings (binary sha256 `64b5e259b960`).
Time-box 75 minutes, started 02:11 UTC on 2026-11-25.

## 1. Blocking

### B1. `-cert` prints an invalid certificate when the formula is decided at level 0 by a reduction

`record_certificate ()` reads the values of the outermost block from the trail
and prints an unassigned variable as true. When root simplification
strengthens a constraint and `qreduce` then drops its remaining literals of the
outermost block (they are unassigned at the root), the empty constraint
decides the formula with those variables unassigned, and the V line is the
all-true default. The literals that were reduced away are exactly the move the
certificate has to contain.

Measured (`tests/fuzz_cert.sh`, seeds 100:400, release build, 1204 instances):

| options | VALID | WELLFORMED | INVALID |
|---|---|---|---|
| `--elim --elimint=1 --vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce` | 753 | 440 | **11** |
| the same with `--no-rootsimp` | 764 | 440 | 0 |

Of the 11 invalid ones, **10 are invalid with no option at all** (default
configuration), also with the binary from before M3
(`/home/ec2-user/miniqu-work/m3/miniQU.before`); the frozen baseline is valid
on the ones checked (tiny-140, tiny-261, search-130). The eleventh is made
invalid by `--elim` (elimination derives a unit, root simplification then
decides the formula). Earlier runs missed it because they used seeds 1:30
(60 QCIR instances at a rate of about 1.7%).

Reproduce (from the repo root, `B=/home/ec2-user/miniqu-work/build/release/miniQU`):

```
python3 tests/corpus.py --tier tiny --seed 140 --out f.qcir
python3 tests/check_cert.py $B f.qcir                 # INVALID (0 decisions, V m0_0 m0_1)
python3 tests/check_cert.py $B f.qcir --no-rootsimp   # VALID  (V -m0_0 -m0_1)
python3 tests/corpus.py --tier tiny --seed 245 --out g.qcir
python3 tests/check_cert.py $B g.qcir                 # VALID  (V -v1)
python3 tests/check_cert.py $B g.qcir --elim          # INVALID (V v1)
python3 tests/check_cert.py $B g.qcir --elim --no-rootsimp   # VALID
```

All eleven files are kept in
`/home/ec2-user/miniqu-work/handover-review/cert-keep/` (list in `bad.txt`).

The same pattern exists in the new units and nothing prevents it there; it was
not observed in the 1204 instances of the `--no-rootsimp` run:

- `vivify_apply`: `found_empty` is reached after `backtrack (0)`; the literals
  of D before `qreduce` are the vivification decisions that were just undone.
- `add_resolvents`: an empty resolvent (all literals reduced away) decides the
  formula at level 0.
- units of both (`add_root_units`) followed by root simplification: the
  observed case of seed 245.

What a fix has to do (one place serves all four): whenever an empty constraint
of the winning kind is obtained from a non-empty literal set at level 0, the
certificate takes the outermost-block literals of that set before reduction (a
cube's literals as they are, a clause's negated), and only the rest from the
trail. Until then `-cert` is not trustworthy with `rootsimp` (default),
`--elim` or `--vivify`; refusing `-cert` unless `--no-rootsimp` and both
techniques are off would be the minimal stopgap.

## 2. Soundness of the two units: what was checked

**Elimination, owner's side conditions.** As built they are the owner's,
slightly stricter:

- Rightmost (E3): checked for every live constraint of the variable's kind,
  learnt ones included, by block depth; the same block is allowed. That is
  sound: all variables of the constraints of x are in the block of x or left
  of it, variables of one block commute, and the rest of the formula does not
  contain x, so the quantifier of x can be moved in front of the constraints
  that contain it (`Q1 ∃x Q2. (F_x ∧ F') = Q1. (∃x F_x) ∧ Q2 F'`, dually for
  cubes). Note for cubes: a universal gate variable shares its block with the
  universal inputs of the next input block (`encode.cpp`), on which it does
  not depend; "same block" still holds by the argument above.
- Other kind (E2): both occurrence lists of the other kind (original and
  learnt) must be empty. On QCIR input this never fires (`elimblockedother`
  is 0 in every run I saw), since gate variables come in pairs, one per kind.
- Candidates are gate variables only, unassigned, not pending as a unit.
  `elim_candidate` is monotone inside a round (a variable never becomes a
  candidate again), so the occurrence lists of candidates, which are extended
  with every stored resolvent, are complete when E2/E3 are tested.
- Resolvents: one clash on the pivot, any second clash drops the resolvent
  (true clause / false cube), `qreduce` afterwards; learnt constraints are
  never parents and are deleted with the variable; parents contain the
  unassigned x and so are no root reasons. Subsumed resolvents are only
  dropped against a live irredundant non-parent or an earlier stored resolvent
  of the same candidate. I found no hole.
- Completeness of propagation after elimination (a full assignment of the
  inputs must end in a conflict of one kind): holds for the full set of
  non-tautological resolvents by induction over the unit-propagation
  derivation, also for the Plaisted-Greenbaum encoding; a violation would end
  in `report_missing_cube ()` ("unknown"), not in a wrong verdict. None seen.
- Verdicts rest on derived constraints only: clause resolvents are
  Q-resolution steps from clauses, cube resolvents from cubes, and deletions
  cannot make a verdict wrong on QCIR input. Every stored resolvent, unit and
  empty resolvent has its derived step before the `d` steps of its parents;
  the code path is the same with and without `--proof`.
- Dependency learning: E3 uses the prefix, not the learnt dependencies (the
  conservative choice); the reset on a dependency that mentions an eliminated
  variable is unreachable on QCIR input (dependencies are between decision
  variables), harmless.
- Later learnt constraints cannot mention an eliminated variable (no live
  constraint contains it, it is never assigned); asserted in `learn.cpp` and
  in `check_invariants`.
- Models/certificates: nothing is reconstructed, because only gate variables
  are eliminated and the certificate lists decision variables. The certificate
  problem is B1, not reconstruction.

**Vivification.** Propagation in modes 0 and 1 ignores the prefix (a
constraint acts only when all other literals vanished), so every reason on the
vivification trail has all other literals vanished and the chain is a plain
resolution chain with one clash per step; D is a subset of C (decisions, the
kept literal, root literals of C), reduced once at the end; mode 0 never
resolves on a secondary pivot (`Lone::Ignore`), mode 1 does (QU-resolution, as
in the search). A root literal without a unit of the candidate's kind is
either a literal of C or the candidate is given up. One-kind propagation keeps
the analysis inside one calculus. With `-dl` the decision order is irrelevant
for the derivation, and `backtrack (0)` leaves the dependency watches
consistent (`stays_eligible`, `depend.propagated`). Unit and empty results go
through the same code as root strengthening. I found no hole other than the
B1 pattern.

**Unsupported combinations.** Mode 2 and (for elimination) QDIMACS input
switch the technique off with a notice at `-verb=1`; proofs exist for QCIR in
modes 0 and 1 only, where every step of both techniques is logged. No
combination writes an underived step. Vivification on QDIMACS input has no
Lean-checkable proof (the format is QCIR only); it is covered by `--check` and
verdict comparison only.

## 3. Structure, readability, defaults

- Each feature is one unit (`elim.cpp/.hpp`, `vivify.cpp/.hpp`) with scratch
  state in its own struct, two branches in the search loop, one flag table
  (`flags.hpp`). Header comments state schedule, side conditions, soundness
  and what is left out; they match the code. Functions are short. Accepted.
- Both are off by default; with the options off only `init_elim`,
  `init_vivify` and two false predicates run. Spot check: 8 search-tier
  corpus instances x (`-verb=1`, `-dl`, `-mode=1`, `-mode=2`): verdict and
  conflicts/decisions/propagations/ticks equal to the pre-M3 binary, 32/32
  (the workers report 80/80 on other seeds).
- No default changed in `3bbf085..HEAD`.

## 4. Suggestions (not blocking)

1. Share the epilogue. `vivify_apply` repeats the tail of `strengthen_root`
   (empty / unit / in-place rewrite) and `eliminate`, `vivify` and
   `simplify_root` repeat the round end (units, PHASE, conflict, collection or
   invariant check). One `replace_constraint (ref, lits, chain)` and one
   `finish_root_round ()` would also be the single place for the fix of B1.
   `simplifier.units` is now used by three units and should be named for what
   it is (pending root units).
2. Elimination cost is unbounded relative to the search: every round rebuilds
   the occurrence lists of the whole database, allocates `4 * vars` vectors,
   and tries every variable in every pass; there are no dirty marks and no
   effort limit relative to search ticks. The hand-over failure of row
   `elim-inp-gc` is of this kind, not a hang: with a 300 s limit all 25
   search instances of seeds 26:50 finish, the slowest (seed 44) in 22 s with
   27126 conflicts and 231 rounds on a loaded machine. The owner decides
   whether the row keeps a 2% limit at 20 s.
3. Vivification budget counts propagation ticks only (analysis, selection,
   sorting and the occurrence count are free), and it adds its propagation to
   `stats.ticks`, so `c stat ticks` is not comparable between runs with and
   without `--vivify`.
4. In the real-file run of section 5, `jctc8-pass` (`--elim`, and
   `--vivify --vivifytier=3`) and `klieber2017q-108-27-t1` (`--vivify
   --vivifyint=100 --vivifytier=3`) did not finish in 120 s with proof
   logging, while the default solved them in 4-5 s in the 30 s hand-over run.
   Not attributed (heavy-tailed family, proof logging on, no paired run); it
   says that neither technique should be switched on without paired
   benchmarks.
5. `--elimsubsume=1` and `--elimboundmax=16` are active under `--elim`
   without any measurement; the conservative sub-defaults (0, `elimbound`)
   would make `--elim` the plain technique.
6. The dependency-reset path of elimination is dead code on QCIR input; an
   assertion would say the same in one line.
7. `--elim` on QDIMACS input or in mode 2, and `--vivify` in mode 2, do
   nothing and say so only at `-verb=1`; a line at the default verbosity
   would avoid a silent no-op in benchmark scripts.

## 5. Runs of this review (all in `/home/ec2-user/miniqu-work/handover-review/`)

- `tests/fuzz_cert.sh`, seeds 100:400, two option sets: table in B1.
- `tests/fuzz.sh` with Lean proof checks and the frozen baseline as
  reference, 7 processes per configuration for about 28 minutes, then killed
  (the script prints its totals only at the end, so there are no totals;
  sampled progress was 10 to 26 seeds per process, 17 instances per seed):
  no `FAIL` line (no wrong verdict, no rejected proof, no assertion or
  invariant failure, no sanitizer report) in
  A debug `--elim --elimint=1 --vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce -dl`,
  B debug `--elim --elimint=1 --elimbound=16 --vivify --vivifyint=1 --vivifytier=3 -mode=1 --no-rootsimp`,
  C asan `--elim --elimint=1 --vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce --reduceint=2 --gcfrac=0`,
  D debug `-no-earlytseitin --elim --elimint=1 --vivify --vivifyint=3 --vivifytier=3 -dl -mode=1`,
  E release `--elim --elimint=1 --vivify --vivifyint=1 --vivifytier=3 --no-reusetrail --restartmode=1`.
- QDIMACS, debug build with `--check --vivify --vivifyint=1 --vivifytier=3
  --no-vivifyonce`, plain / `-dl` / `-mode=1`, qbfuzz seeds 5001:5200 (large
  parameters of `fuzz_cert.sh`): 600 runs, all verdicts equal to the baseline.
- 28 benchmark files (16 SAT, 12 UNSAT, default wall 0.3-6 s) x `--elim
  --elimint=200`, `--vivify --vivifyint=100 --vivifytier=3`, and both with
  `-dl`, with `--proof --proofbinary` and `qlrup-check`: 83 runs finished or
  timed out, 80 proofs `VERIFIED` with the expected verdict, 3 solver
  timeouts at 120 s (suggestion 4), 1 run killed at the end of the time-box.
  Proofs deleted.
- Row `elim-inp-gc`, seeds 26:50, limit 300 s: all finish (suggestion 2).

## 6. What the missing tests have to cover

1. Certificates: instances decided at level 0 (0 decisions) for both
   quantifiers of the outermost block and both verdicts; `fuzz_cert.sh` with
   several hundred seeds for the default, `--elim`, `--vivify` and their
   combination, with and without `-dl`; a unit test per path of B1 (root
   strengthening, empty resolvent, empty vivification result, unit followed by
   root simplification).
2. Elimination paths that the fuzz rows reach rarely or never: the empty
   resolvent, two contradicting unit resolvents in one round (root conflict
   out of `add_root_units`), `elimlearnt.cube` (0% in all rows), E2
   (`elimblockedother` is always 0 on QCIR), the dependency reset; they are
   covered by unit tests only.
3. Completeness after elimination on the whole benchmark set: no "missing
   cube" exit, `modelcubes == 0`, with `--elim` alone and with
   `--elimbound=16`, with and without `-no-earlytseitin`.
4. Long sanitizer and debug fuzz runs (asan, assertions, owner re-check) of
   elimination and vivification together with reduce, garbage collection,
   root simplification on and off, modes 0 and 1, `-dl`; my runs are about
   half an hour and have no totals.
5. Proofs on real UNSAT and SAT instances in which elimination and
   vivification steps are a large share of the proof, including proof size and
   checking time; the three proofs of row `vivify-mode1-dl` whose check timed
   out; mode 1 with QU pivots in vivification chains over many seeds.
6. QDIMACS with `--vivify`: only verdicts and `--check` exist; no Lean proof
   is possible in the current format.
7. Option-off equality on the benchmark set (`tests/m1_equiv.sh` with both
   options off) and a paired on/off benchmark per technique with the harness
   (same machine, same seeds), with attention to the heavy tails (`jctc`,
   `klieber`) and to the cost of rounds on large instances (`elimint`,
   `elimticks`, `vivifyint`, `vivifyticks`, `vivifytier`, `vivifyonce`).
