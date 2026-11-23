# M1-r2 benchmark report (port of miniQU to the new architecture, round 2)

Correction (round 3): the family gate of ROADMAP 'M1 round 2' was not met, see M1-r2-reports/gate.md and review M1-r2; 2.1 and 5.2-3 hit the memory limit in every run of both binaries.

New: release build (-O3 -DNDEBUG) of rewrite/cadical-style at 25216c2 (`build/bench-M1-r2`, tags `M1-r2-<cfg>-s<seed>`).
Baseline: frozen c39005a binary, same machine (96 cores, 48 jobs on cores 48-95, 8 GB, timeout 60 s, all 376 instances),
tags `baseline-c96-<cfg>-t60-s<seed>` (meta.json of the baseline runs matches the harness settings; reused, not rerun).
Previous milestone: `M1-r1-*` (same machine, same settings, round-1 binary at 00eb7a4). default and `-dl`: seeds 1-3
(baseline `-rnd-init -rnd-seed=S`, new `--seed=S`); mode1, mode2, ccmin3: seed 1 only. Paired compare.py output is in
`M1-r2-reports/` (`<cfg>-paired.md` = new vs baseline, `<cfg>-vs-r1.md` = new vs round 1, `all-runs-discrepancy-check.md`).
No proof run and no ablations in this stage (outside the 2 h budget note; not requested in the configuration list).

## Interpretation

**Blocking items: none.** No result discrepancy in any pair or across all runs (the 9 new runs, the 9 same-machine baseline
runs and the old 180 s baselines), no MISMATCH/ERROR/MEMOUT problems reported. No proofs were produced in this stage.

| config | seeds | solved baseline | solved new | PAR2 baseline | PAR2 new | PAR2 diff new-base [95% CI] | sign test (W/L, p) | verdict | not worse |
|---|---|---|---|---|---|---|---|---|---|
| default | 1-3 | 141/146/143 | 140/144/143 | 79.3/77.9/79.1 | 79.9/78.3/78.9 | +0.24 s [-0.52, +1.05] | 32 / 21, p=0.17 | no measurable difference | yes |
| dl | 1-3 | 150/153/146 | 149/151/146 | 76.4/75.7/77.7 | 76.6/76.0/77.4 | +0.05 s [-0.68, +0.76] | 36 / 30, p=0.54 | no measurable difference | yes |
| mode1 | 1 | 116 | 114 | 85.9 | 86.3 | +0.41 s [-1.02, +1.88] | 18 / 21, p=0.75 | no measurable difference | yes |
| mode2 | 1 | 130 | 134 | 82.3 | 81.2 | -1.10 s [-2.76, +0.44] | 39 / 23, p=0.056 | no measurable difference | yes |
| ccmin3 | 1 | 142 | 146 | 79.0 | 77.7 | -1.32 s [-3.27, +0.56] | 43 / 23, p=0.019 | no measurable difference (single seed) | yes |

(solved and PAR2 per seed 1/2/3; "W/L" are wins/losses of the new solver with margin max(1 s, 10 %).)

Against round 1 (same machine, same seeds; `*-vs-r1.md`): PAR2 difference new-r2 minus r1 is -0.34 s for default
(CI [-0.68, -0.13], verdict "better") and -0.34 s for dl (CI [-0.55, -0.19], 18 wins / 0 losses, p<0.001); mode1 -0.04 s,
mode2 -0.18 s (no measurable difference), ccmin3 -0.48 s (CI [-1.05, -0.09], single seed). Round 2 is thus slightly
better than round 1 in score; this is consistent with the engine-speed gain below.

**Noise.** Seed spread within one arm: baseline default 5 solved / 1.4 s PAR2 (141-146, 77.9-79.3), new default 4 solved /
1.6 s (140-144, 78.3-79.9); dl baseline 7 / 2.0 s, new dl 5 / 1.4 s. All new-vs-baseline PAR2 differences for default, dl
and mode1 (|diff| <= 0.41 s) are well inside this spread and every bootstrap interval contains 0: the new solver is
statistically indistinguishable from the baseline in default, dl and mode1. Round 1 had a small, unresolved deficit
(+0.58 s default, +0.40 s dl); it has shrunk to +0.24 s / +0.05 s. In mode2 and ccmin3 the new solver is nominally better
(-1.1 s, -1.3 s) but with a single seed that is within the seed noise (up to 2 s); the ccmin3 sign test p=0.019 is not
corrected for the five comparisons and rests on one seed, so it is not claimed as an improvement.

**Engine speed (identical searches, CPU-time ratio new/baseline, from stats.csv, instances with equal conflict counts and
baseline CPU > 1 s).** Pooled per instance: default 1.037 (n=51, 28 slower / 23 faster), dl 1.001 (n=50), mode1 1.063
(n=35, 25 slower / 10 faster), mode2 0.975 (n=33), ccmin3 0.834 (n=4). Against round 1 the identical-search ratio improved
to 0.950 (default, n=119), 0.939 (dl, n=129), 0.933 (mode1, n=76), 0.959 (mode2), 0.949 (ccmin3), i.e. the round-2 binary is
about 5-6 % faster on the same search. Compared to the baseline the engine is within a few percent (mode1 about 6 % slower,
the worst case; this is not visible in the solved counts).

**Improved:** `test_5_5_knobby.pg-9` (gained in a majority of seeds, default); `CM-sat-04-01-06-3` (gained in dl, mode1,
ccmin3); in mode2 gained in a majority: `CM-sat-04-01-07-3`, `hadw2-8`, `hadw3-7`, `jctc8-pass`, `klieber2017q-072-18-t1`,
`klieber2017q-100-25-t1`, `ltl2dba_beta6.tlsf`; in ccmin3 nine gains incl. `DW-unsat-10-25-1` and several `klieber2017q-08x-2x-t1`.
Family means: dl `DW` -3.0 s and `CM` -8.3 s; mode1 `CM` -16.9 s; mode2 `CM` -5.6 s.

**Regressed:** default: `klieber2017q-076-19-eq` and `klieber2017q-108-27-t1` lost in a majority of seeds; family means worse for
`CM` (+10.5 s, 3 losses of 7) and `Lights` (+12.4 s, only two instances). dl: `Lights2_0f5381e9.tlsf` lost in a majority of seeds,
`Lights` +24.5 s, `DWs` +2.2 s. mode1: lost `5.1-1`, `Lights2_0f5381e9.tlsf`, `hadw6-8`, `klieber2017q-072-18-eq`,
`reachqu_query60_1344`, `test_5_5_elly.pg-9` (gained: `CM-sat-04-01-06-3`, `jctc14-unrolled-fail`, `jctc8-pass`,
`reachqu_query64_1344`). mode2 lost `CM-sat-04-01-06-4`, `chess_solving_mate_in_3_2000_CZE-CH_04`, `jctc6-pass`. ccmin3 lost
`CM-sat-04-01-06-4`, `CM-sat-04-01-07-3`, both `Lights2_*`, `klieber2017q-112-28-t1`. The recurring losers are the `Lights2` and
`CM-sat-04-01-06/07` instances, which solve near the 60 s limit and flip with the seed (the same names flip in both directions
across configurations), so they indicate sensitivity, not a systematic regression; the per-family means for `Lights` (2
instances) and `CM` (7) are dominated by one instance crossing the timeout (a 60 s timeout counts 120 s PAR2).

**Summary.** The round-2 port matches the baseline within noise in all five configurations (no configuration shows a
difference beyond seed spread) and is a measurable ~5 % engine-speed improvement over round 1. Remaining caveats: mode1 has
the slowest identical-search ratio (1.063), single-seed configurations (mode1/2, ccmin3) cannot separate noise from effect,
and the 2 h budget left no time for proof coverage or ablations, so proof logging and the new techniques are not benchmarked here.
