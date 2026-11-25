# Tests and benchmarks after the hand-over (2026-11-25)

Binary: release build of `bcc7ed2` (sha256 `3e47d7e820a7…`), copied to
`~/miniqu-work/build/bench-post/miniQU`. Machine: m7a.12xlarge, 48 cores. Tests on cores 0-23 (22 jobs),
benchmarks at the same time on cores 24-47 (24 jobs, 8 GB per job, 60 s, all 376 QCIR instances).
Drivers: `~/miniqu-work/post/tests.sh`, `~/miniqu-work/post/bench.sh` (copies in `post-reports/`).

## Summary

- No wrong verdict, crash, sanitizer report or rejected proof in any test or benchmark run.
- Elimination (`--elim`) is a clear gain in default mode and a smaller one with `-dl`.
- Vivification (`--vivify`) shows no measurable effect on its own; added to elimination it gives a small gain
  in default mode.
- Elimination makes the `jctc` family slower in default mode.
- The new features stay off by default; the data supports switching `--elim` on, which is the owner's decision.

## Tests (items of HANDOFF.md section 2)

| item | test | result |
|---|---|---|
| 1 | unit tests, release / debug / asan | passed |
| 8 | `tests/m1_equiv.sh` against the M1 binary | passed |
| 2 | full matrix, release, seeds 1:300, smoke set, Lean (67 rows) | passed, 8 warnings; 19056 proofs accepted |
| 4 | full matrix, asan + ubsan, seeds 1:100, 240 s | passed, 5 warnings |
| 3 | certificates, 7 option sets, seeds 1:300 (not 1:1000) | passed, no INVALID |
| 6 | QDIMACS fuzz, 4 modes: plain, stress, vivify + stress (release 1:300), vivify + stress (asan 1:100) | passed |
| 11 | completeness after elimination, 3 option sets, benchmark set | no `ERROR`, `modelcubes` 0 everywhere |
| 9 | Lean coverage with `--elim --vivify`, benchmark set | default 142 of 142, `-dl` 145 of 145 accepted |

Warnings are solver time-outs in rows where they were known (`noearly` and `elim-noearly` 34 each on release,
`restart-mode1-dl` 20, `restart-dl` 6, `ema-stress-dl` 4, `mode1-dl` 3, `mode2-dl` 2, `vivify-mode1-dl` 1); no
stress row exceeded its limit. In the release matrix 42 proof checks hit the checker's time limit and stay
unchecked (rows `mode1-dl`, `noearly`, `elim-noearly`, `elim-mode1-dl`, `vivify-mode1-dl`); item 10 of the
hand-over list (longer checker limit) is still open.

Not run: items 5 (debug build on the new rows), 10, 12 (mode 1 certificates, known defect), 13 (missing unit
tests), 14 (other seed ranges), the debug `--check` QDIMACS run of 2.1, and proof coverage per single technique.

## Benchmarks: solved of 376 at 60 s, seeds 1 / 2 / 3

| configuration | default mode | `-dl` |
|---|---|---|
| original miniQU (`c39005a`) | 141 / 146 / 144 | 150 / 153 / 146 |
| rewrite, defaults (tag `ref`) | 150 / 151 / 151 | 154 / 161 / 158 |
| `--vivify` | 153 / 151 / 150 | 155 / 157 / 158 |
| `--elim` | 161 / 166 / 159 | 158 / 160 / 162 |
| `--elim --vivify` (tag `both`) | 166 / 166 / 161 | 164 / 163 / 162 |

Paired comparison over the three seeds (`bench/compare.py --paired`, reports in `post-reports/`). PAR2
difference is B minus A in seconds per instance, mean over 376 instances, with the 95% bootstrap interval;
wins and losses are instances, sign test with a margin of max(1 s, 10%).

| A | B | PAR2 difference | wins / losses | verdict |
|---|---|---|---|---|
| ref | `--elim` | -4.44 [-6.12, -2.86] | 83 / 6 | better |
| ref | `--vivify` | +0.10 [-0.64, +0.84] | 29 / 33 | no measurable difference |
| ref | both | -5.16 [-6.96, -3.46] | 90 / 8 | better |
| `--elim` | both | -0.72 [-1.37, -0.13] | 28 / 26 | better (interval only; sign test p = 0.89) |
| ref `-dl` | `--elim -dl` | -1.78 [-2.75, -0.86] | 96 / 16 | better |
| ref `-dl` | `--vivify -dl` | +0.04 [-0.75, +0.87] | 42 / 34 | no measurable difference |
| ref `-dl` | both `-dl` | -2.37 [-3.42, -1.42] | 102 / 13 | better |
| `--elim -dl` | both `-dl` | -0.59 [-1.35, +0.10] | 47 / 24 | no measurable difference |
| original | ref | -2.34 [-4.09, -0.73] | 67 / 31 | better |
| original | both | -7.50 [-9.82, -5.36] | 99 / 10 | better |
| original `-dl` | ref `-dl` | -2.49 [-3.83, -1.27] | 76 / 21 | better |
| original `-dl` | both `-dl` | -4.86 [-6.44, -3.36] | 113 / 10 | better |

No comparison has a result discrepancy.

### Where elimination helps and where it hurts (ref against both, default mode)

- Gained in a majority of seeds (17): 7 `klieber` instances, 2 `CM`, 2 `test`, and one each of `DW`, `Lights`,
  `connect`, `reachqu`, `s`, `numeric` (`5.2-2`). Lost (1): `jctc9-pass`.
- Family mean score (s), ref to both: `klieber` 52.0 to 12.0 (26 of 26 instances faster), `Lights` 69.7 to 22.2,
  `CM` 120.0 to 98.3, `reachqu` 94.3 to 72.2, `DW` 38.3 to 25.9, `bt` 52.9 to 40.9, `test` 35.8 to 30.1.
- **`jctc` gets worse: 64.0 to 74.7 (1 win, 4 losses); with `--elim` alone 64.0 to 71.4.** With `-dl` the family
  is 35.7 to 33.5 with `--elim` and 35.7 to 40.3 with both. The family is heavy-tailed (STATUS M2-T11), so three
  seeds do not settle the size, but the direction in default mode is the same in both comparisons.
- With `-dl`, gained 3 (`bt`, `chess`, `connect`), lost 1 (`3.1`); `numeric` is slightly worse (35.8 to 38.6).
- On searches that elimination leaves identical (10 `numeric` instances) the run is 9% slower in CPU time: the
  cost of rounds that eliminate nothing useful.

### One switch at a time (seed 1 only, default mode)

One seed: differences of up to about 5 solved instances are within the spread seen between seeds.

| configuration | solved | PAR2 |
|---|---:|---:|
| ref | 150 | 76.4 |
| `--elim` | 161 | 72.2 |
| `--elim --no-elimcube` (clauses only) | 160 | 72.5 |
| `--elim --no-elimclause` (cubes only) | 156 | 74.6 |
| `--elim --no-eliminp` (before the search only) | 157 | 73.4 |
| `--elim --no-elimpre` (inprocessing only) | 162 | 71.5 |
| `--vivify` | 153 | 76.5 |
| `--vivify --no-vivifycube` (clauses only) | 156 | 75.4 |
| `--vivify --no-vivifyclause` (cubes only) | 148 | 76.9 |
| `--vivify --vivifytier=3` | 148 | 77.1 |
| `--elim --vivify` | 166 | 70.7 |
| `--no-tiers --no-glueupdate` | 152 | 76.4 |
| `--no-rootsimp` | 151 | 76.6 |
| `--no-reusetrail` | 157 | 75.1 |
| M1 binary | 141 | 79.6 |
| original miniQU | 141 | 79.3 |

With `-dl` (seed 1): ref 154 (PAR2 74.6), M1 binary 150 (76.2), original 150 (76.3).

Reading, with the one-seed caveat:
- Both kinds of elimination contribute; the clause side carries most of it. Inprocessing rounds alone do as
  well as the full setting; elimination before the search alone gives about half the gain.
- No vivification variant is distinguishable from the reference.
- The M2 features, switched off one at a time, do not lower the solved count; without trail reuse the run solves
  7 more. M2 as a whole is better than M1 (150 against 141, and the three-seed comparison with the original
  above), so the gain of M2 is not attributed to a single switch by these runs. Trail reuse needs seeds before
  its default is changed (see also the M2-T11 side observation on `jctc10-fail`).

## Limits

- 60 s time limit and three seeds; nothing at 900 s exists for the rewrite.
- The option defaults of both features (`elimint`, `elimticks`, bounds, `vivifyint`, `vivifyticks`,
  `vivifytier`) are the first values chosen; nothing is tuned.
- The ablations of single switches and the M2 ablations are one seed.
- Tests and benchmarks shared the machine (separate halves of the cores), as in the earlier milestones.
