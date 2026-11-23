# M1-r1 benchmark report (port of miniQU to the new architecture)

New: release build (-O3 -DNDEBUG) of rewrite/cadical-style at 00eb7a4 (`build/bench-M1-r1`). Baseline: frozen
c39005a binary on the same machine (96 cores, jobs 48 on cores 48-95, 8 GB, timeout 60 s, all 376 instances),
tags `baseline-c96-<cfg>-t60-s<seed>` (new runs: `M1-r1-<cfg>-s<seed>`). default and `-dl`: seeds 1-3
(baseline seeds via `-rnd-init -rnd-seed=S`, new via `--seed=S`); mode1, mode2, ccmin3: seed 1 only.
No previous-milestone results exist on this machine. Sub-reports (paired compare.py output) are in
`M1-r1-reports/`: default-paired, dl-paired, mode1-paired, mode2-paired, ccmin3-paired,
all-runs-discrepancy-check (plain compare of all 18 runs + baseline-t180/-dl-t180).

## Interpretation

**Blocking items: none.** No result discrepancy in any pair or across all runs (including configurations
against each other and against the old 180 s baselines), no MISMATCH/ERROR. No proofs were produced in
this stage (proof coverage run dropped, see below).

| config | seeds | solved A (baseline) | solved B (new) | PAR2 A | PAR2 B | PAR2 diff B-A [95% CI] | sign test | verdict | not worse |
|---|---|---|---|---|---|---|---|---|---|
| default | 1-3 | 141/146/143 | 138/143/143 | 79.3/77.9/79.1 | 80.5/78.6/79.0 | +0.58 s [-0.20, +1.42] | 27 W / 28 L, p=1.0 | no measurable difference | yes |
| dl | 1-3 | 150/153/146 | 148/151/145 | 76.4/75.7/77.7 | 77.0/76.2/77.8 | +0.40 s [-0.34, +1.11] | 27 W / 44 L, p=0.057 | no measurable difference | yes |
| mode1 | 1 | 116 | 115 | 85.9 | 86.3 | +0.44 s [-0.92, +1.83] | 14 W / 31 L, p=0.016 | B worse (single seed) | no |
| mode2 | 1 | 130 | 134 | 82.3 | 81.3 | -0.92 s [-2.59, +0.63] | 29 W / 27 L, p=0.89 | no measurable difference | yes |
| ccmin3 | 1 | 142 | 144 | 79.0 | 78.2 | -0.84 s [-2.81, +1.07] | 36 W / 24 L, p=0.155 | no measurable difference | yes |

(A/B solved and PAR2 are listed per seed 1/2/3.) Noise: the spread over seeds within one arm is 5 solved
and about 1.4 s PAR2 for the baseline default (141-146, 77.9-79.3), 5 solved / 1.8 s for the new default
(138-143, 78.6-80.5); dl: 7 solved / 2.0 s (baseline), 6 solved / 1.6 s (new). The PAR2 differences between new
and baseline (0.4-0.6 s) are inside this spread, and the bootstrap intervals contain 0. In default and dl the new
solver solves on average 2 instances fewer (means baseline vs new: default 143.3 vs 141.3; dl 149.7 vs 148.0) and is marginally slower in PAR2 (+0.4 to +0.6 s, +0.5-0.8%); this is a
small, consistent-in-sign but statistically unresolved loss (dl sign test p=0.057 is borderline).

- **Improved (random-seed sensitive, no stable gains):** `test_5_5_knobby.pg-9` (gained in a majority of
  seeds, default), `CM-sat-04-01-06-3` (gained in dl, mode1, ccmin3), and most `klieber` t1 instances in
  ccmin3 and default (14 wins vs 6 losses in the klieber family, per-family mean +3.2 s worse nevertheless
  because of a few large losses); `sc`, `test` families slightly faster (-1.2 s, -2.7 s mean).
- **Regressed:** default: `DW-unsat-10-25-1`, `klieber2017q-076-19-eq`, `klieber2017q-108-27-t1` lost in a
  majority of seeds; family means worse for `CM` (+10.5 s), `DW` (+9.6 s), `Lights` (+11.9 s), `klieber`
  (+3.2 s), `eequery` (+4.7 s); `chess` shows 9 losses but a mean difference of only +0.7 s. Largest
  single losses: `klieber2017q-088-22-t1` (+62.8 s in score), `klieber2017q-108-27-t1`, `DW-unsat-10-25-1`,
  `klieber2017q-076-19-t1`, `CM-sat-04-01-06-4`. dl: `Lights2_0f5381e9.tlsf` lost in a majority of seeds.
  mode1 (one seed): lost `5.1-1`, `Lights2_0f5381e9.tlsf`, `klieber2017q-072-18-eq`, `reachqu_query60_1344`,
  `test_5_5_elly.pg-9`; gained 4. Peak memory: only 3 instances solved by both exceed +10% (`sc-ungrounded-*`,
  `bt-3x6_9.ig`, all below 60 MB).
- **Above noise?** Only mode1 passes the sign test (p=0.016), but with one seed the noise cannot be estimated
  from it; the solved count differs by 1 and PAR2 by 0.4 s, which is within the default-configuration seed
  spread, so it is at most a weak signal (many instances sit near the 60 s limit and flip between seeds).
  Nothing else exceeds noise. Instances flipping at the limit (CM-sat-*, klieber2017q-*, Lights2_*, DW-unsat-10-25-1)
  account for nearly all gains and losses, i.e. these are search-order variance (different RNG streams and
  data-structure layout), not systematic. Overall: the port is at parity with the baseline within noise in
  default, dl, mode2 and ccmin3, with a slight (unresolved) shortfall in default/dl/mode1 of about 0.5% PAR2.
- **Dropped for the 2 h budget (about 1 h 50 min used):** proof-coverage run, proof overhead, ablations (none
  existed for M1), modes 1/2 and ccmin3 with seeds 2-3 (seed 1 only), 600 s tier (not wanted).
- Caveat: only 3 seeds; one new-default seed is 138 solved vs 141-146 for baseline, so a loss of about
  1-3 solved instances cannot be excluded; a 5-seed or 600 s run would be needed to resolve it.


---

# Paired comparison: B (M1-r1-default-s1, M1-r1-default-s2, M1-r1-default-s3) against A (baseline-c96-default-t60-s1, baseline-c96-default-t60-s2, baseline-c96-default-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-23T01:16:03 |
| B | `` | 00eb7a4 | a48a1a946f47 | 2026-11-23T01:09:59 |

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.58 s**, 95% bootstrap interval [-0.20, +1.42] (10000 resamples).

Sign test: B wins on 27 instances, loses on 28, ties on 321; two-sided p = 1.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 81/57/138 | 80.5 |
| 2 | 86/60/146 | 77.9 | 85/58/143 | 78.6 |
| 3 | 85/58/143 | 79.1 | 83/60/143 | 79.0 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.9-79.3 |
| B | 138-143 | 78.6-80.5 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `test_5_5_knobby.pg-9.qcir`
- lost by B (3): `DW-unsat-10-25-1.qcir`, `klieber2017q-076-19-eq.qcir`, `klieber2017q-108-27-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.1 | 105.7 | +10.5 | 1 | 3 |
| DW | 7 | 31.8 | 41.5 | +9.6 | 0 | 3 |
| DWs | 13 | 117.3 | 117.4 | +0.1 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.8 | 91.6 | +11.9 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 100.8 | -0.4 | 0 | 0 |
| arbiter | 6 | 84.8 | 84.9 | +0.1 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.7 | 81.1 | -1.6 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.3 | 28.0 | +0.7 | 0 | 9 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 1 |
| collector | 1 | 4.4 | 4.6 | +0.2 | 0 | 0 |
| connect | 7 | 86.9 | 86.8 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 74.7 | 79.4 | +4.7 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.3 | 10.6 | +0.2 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.5 | 76.2 | -0.3 | 2 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.7 | 75.8 | +0.1 | 0 | 0 |
| klieber | 26 | 49.9 | 53.1 | +3.2 | 14 | 6 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.8 | +0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.6 | 99.1 | +0.5 | 0 | 1 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.3 | 112.0 | +0.8 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 33.3 | +1.5 | 0 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 88.9 | 88.1 | -0.8 | 0 | 0 |
| robot | 1 | 5.2 | 4.1 | -1.1 | 1 | 0 |
| round | 1 | 2.0 | 2.0 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 59.0 | 57.7 | -1.2 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 47.2 | 44.5 | -2.7 | 5 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_knobby.pg-9.qcir | 90.6 | 41.3 | -49.3 |
| CM-sat-04-01-06-3.qcir | 90.4 | 59.1 | -31.3 |
| klieber2017q-112-28-t1.qcir | 120.0 | 90.0 | -30.0 |
| klieber2017q-084-21-eq.qcir | 120.0 | 92.5 | -27.5 |
| klieber2017q-100-25-t1.qcir | 93.7 | 72.2 | -21.5 |
| bt2nd-3x6_10.ig.qcir | 120.0 | 100.0 | -20.0 |
| klieber2017q-068-17-t1.qcir | 40.2 | 27.0 | -13.2 |
| klieber2017q-078-19-t1.qcir | 61.8 | 50.5 | -11.2 |
| klieber2017q-074-18-t1.qcir | 36.1 | 25.8 | -10.4 |
| klieber2017q-080-20-t1.qcir | 31.8 | 23.1 | -8.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-088-22-t1.qcir | 10.2 | 72.9 | +62.8 |
| klieber2017q-108-27-t1.qcir | 35.4 | 84.6 | +49.2 |
| DW-unsat-10-25-1.qcir | 52.2 | 99.5 | +47.3 |
| klieber2017q-076-19-t1.qcir | 29.2 | 72.5 | +43.3 |
| klieber2017q-076-19-eq.qcir | 51.4 | 92.4 | +41.0 |
| CM-sat-04-01-06-4.qcir | 43.8 | 80.5 | +36.7 |
| CM-sat-04-01-07-3.qcir | 84.4 | 120.0 | +35.6 |
| CM-sat-07-01-06-3.qcir | 87.2 | 120.0 | +32.8 |
| 5.2-1.qcir | 31.7 | 57.4 | +25.6 |
| Lights2_b02056d6.tlsf.qcir | 97.9 | 120.0 | +22.1 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-1x3X3x2_1.qcir | 26 | 37 | 1.44x |
| bt-3x6_9.ig.qcir | 15 | 20 | 1.31x |
| sc-ungrounded-2x1X1x2_2.qcir | 47 | 55 | 1.16x |


---

# Paired comparison: B (M1-r1-dl-s1, M1-r1-dl-s2, M1-r1-dl-s3) against A (baseline-c96-dl-t60-s1, baseline-c96-dl-t60-s2, baseline-c96-dl-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-23T01:28:03 |
| B | `-dl` | 00eb7a4 | a48a1a946f47 | 2026-11-23T01:22:04 |

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.40 s**, 95% bootstrap interval [-0.34, +1.11] (10000 resamples).

Sign test: B wins on 27 instances, loses on 44, ties on 305; two-sided p = 0.0568 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.4 | 84/64/148 | 77.0 |
| 2 | 86/67/153 | 75.7 | 86/65/151 | 76.2 |
| 3 | 84/62/146 | 77.7 | 82/63/145 | 77.8 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.7-77.7 |
| B | 145-151 | 76.2-77.8 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `CM-sat-04-01-06-3.qcir`
- lost by B (1): `Lights2_0f5381e9.tlsf.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.2 | 89.1 | -8.1 | 2 | 2 |
| DW | 7 | 21.4 | 21.6 | +0.2 | 1 | 5 |
| DWs | 13 | 117.8 | 120.0 | +2.2 | 0 | 1 |
| JP | 6 | 109.9 | 113.0 | +3.1 | 0 | 1 |
| Lights | 2 | 50.2 | 75.5 | +25.4 | 0 | 2 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 105.1 | -2.5 | 1 | 1 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.2 | 91.3 | +4.1 | 1 | 1 |
| arbiter | 6 | 84.2 | 84.9 | +0.7 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.8 | 83.6 | +2.9 | 1 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.8 | 62.7 | +0.8 | 0 | 12 |
| ci | 30 | 88.6 | 88.6 | +0.0 | 1 | 1 |
| collector | 1 | 4.3 | 4.8 | +0.5 | 0 | 0 |
| connect | 7 | 88.4 | 87.7 | -0.8 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.5 | 70.2 | +0.7 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.8 | 9.4 | +1.6 | 0 | 1 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.7 | 78.5 | -0.2 | 1 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.4 | 39.9 | +2.5 | 1 | 2 |
| klieber | 26 | 17.3 | 16.3 | -1.0 | 11 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.1 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.2 | 99.1 | -0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.1 | 111.8 | +0.7 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | -0.0 | 0 | 0 |
| numeric | 26 | 36.8 | 37.8 | +1.0 | 0 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 80.2 | +7.4 | 0 | 1 |
| robot | 1 | 4.4 | 3.3 | -1.1 | 1 | 0 |
| round | 1 | 1.4 | 1.3 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.7 | 56.4 | -0.3 | 1 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 37.3 | -0.9 | 4 | 2 |
| voter | 2 | 102.1 | 102.0 | -0.1 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 90.4 | 25.1 | -65.3 |
| klieber2017q-084-21-eq.qcir | 68.4 | 27.3 | -41.1 |
| jctc10-fail.qcir | 120.0 | 89.5 | -30.5 |
| SR-sat-02-01-06-3.qcir | 120.0 | 90.4 | -29.6 |
| test_5_5_fatty.pg-9.qcir | 73.9 | 46.9 | -27.0 |
| CM-sat-07-01-07-3.qcir | 120.0 | 98.2 | -21.8 |
| DW-unsat-11-26-1.qcir | 72.9 | 59.6 | -13.2 |
| klieber2017q-086-21-t1.qcir | 18.6 | 9.7 | -8.9 |
| test_5_5_knobby.pg-9.qcir | 26.3 | 17.9 | -8.3 |
| test_5_5_skinny.pg-9.qcir | 68.3 | 61.2 | -7.1 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_0f5381e9.tlsf.qcir | 75.5 | 120.0 | +44.5 |
| jctc4-fail.qcir | 9.9 | 41.3 | +31.4 |
| bt2nd-3x6_10.ig.qcir | 90.8 | 120.0 | +29.2 |
| klieber2017q-088-22-eq.qcir | 62.7 | 91.2 | +28.5 |
| DWs-unsat-08-17-1.qcir | 91.7 | 120.0 | +28.3 |
| jctc14-unrolled-fail.qcir | 92.4 | 120.0 | +27.6 |
| 5.2-1.qcir | 35.5 | 59.1 | +23.6 |
| CM-sat-04-01-06-4.qcir | 96.5 | 120.0 | +23.5 |
| amba2f9n.sat.qcir | 53.5 | 76.1 | +22.7 |
| JP-unsat-02-06-3.qcir | 59.4 | 77.8 | +18.4 |

## Peak memory

5 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc6-pass.qcir | 64 | 122 | 1.90x |
| jctc13-fail.qcir | 17 | 25 | 1.50x |
| CM-sat-04-01-07-3.qcir | 480 | 581 | 1.21x |
| bt-3x6_9.ig.qcir | 14 | 17 | 1.20x |
| jctc8-pass.qcir | 49 | 58 | 1.19x |


---

# Paired comparison: B (M1-r1-mode1-s1) against A (baseline-c96-mode1-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | c39005a | 10ff614c6694 | 2026-11-23T02:27:56 |
| B | `-mode=1` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:21:44 |

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.44 s**, 95% bootstrap interval [-0.92, +1.83] (10000 resamples).

Sign test: B wins on 14 instances, loses on 31, ties on 331; two-sided p = 0.0161 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is worse than A.**

B is not worse than A: **no**.

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 72/44/116 | 85.9 | 70/45/115 | 86.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 116-116 | 85.9-85.9 |
| B | 115-115 | 86.3-86.3 |

## Instances gained and lost in a majority of seeds

- gained by B (4): `CM-sat-04-01-06-3.qcir`, `jctc14-unrolled-fail.qcir`, `jctc8-pass.qcir`, `reachqu_query64_1344.qcir`
- lost by B (5): `5.1-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `klieber2017q-072-18-eq.qcir`, `reachqu_query60_1344.qcir`, `test_5_5_elly.pg-9.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 103.1 | -16.9 | 1 | 0 |
| DW | 7 | 40.2 | 42.6 | +2.4 | 0 | 3 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 89.7 | 120.0 | +30.3 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.4 | 101.6 | +0.1 | 0 | 0 |
| arbiter | 6 | 85.0 | 85.2 | +0.2 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.5 | 93.8 | +1.3 | 0 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.3 | 30.2 | +0.9 | 0 | 8 |
| ci | 30 | 100.1 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.5 | 3.7 | +0.2 | 0 | 0 |
| connect | 7 | 89.1 | 89.2 | +0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 71.2 | 72.3 | +1.1 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 11.7 | 13.5 | +1.8 | 0 | 1 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.2 | 69.4 | +0.3 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.9 | 72.5 | -11.4 | 2 | 1 |
| klieber | 26 | 112.1 | 116.5 | +4.5 | 0 | 2 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.1 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.3 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.8 | 98.0 | +0.3 | 0 | 1 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.3 | 110.8 | +0.6 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 31.3 | 34.7 | +3.4 | 0 | 6 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 83.3 | 92.7 | +9.4 | 1 | 1 |
| robot | 1 | 4.5 | 4.0 | -0.5 | 0 | 0 |
| round | 1 | 1.5 | 1.5 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 57.3 | -0.9 | 2 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 68.6 | 70.8 | +2.2 | 6 | 3 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 120.0 | 1.9 | -118.1 |
| jctc8-pass.qcir | 120.0 | 31.5 | -88.5 |
| reachqu_query64_1344.qcir | 120.0 | 38.1 | -81.9 |
| jctc14-unrolled-fail.qcir | 120.0 | 59.7 | -60.3 |
| test_5_5_snaky.pg-7.qcir | 15.7 | 7.5 | -8.2 |
| test_5_5_Z.pg-7.qcir | 14.7 | 6.5 | -8.1 |
| test_5_5_domino.pg-11.qcir | 10.7 | 4.2 | -6.4 |
| sc-ungrounded-2x2X2x2_1.qcir | 26.4 | 20.1 | -6.3 |
| test_5_5_knobby.pg-7.qcir | 9.5 | 7.2 | -2.3 |
| test_5_5_tic.pg-9.qcir | 12.5 | 10.3 | -2.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query60_1344.qcir | 9.8 | 120.0 | +110.2 |
| klieber2017q-072-18-eq.qcir | 20.7 | 120.0 | +99.3 |
| test_5_5_elly.pg-9.qcir | 46.9 | 120.0 | +73.1 |
| 5.1-1.qcir | 50.0 | 120.0 | +70.0 |
| Lights2_0f5381e9.tlsf.qcir | 59.5 | 120.0 | +60.5 |
| klieber2017q-060-15-eq.qcir | 13.3 | 30.2 | +16.9 |
| bt2nd-2x5_10.ig.qcir | 28.0 | 43.2 | +15.3 |
| DW-unsat-09-22-1.qcir | 12.1 | 21.3 | +9.2 |
| test_5_5_elly.pg-7.qcir | 1.6 | 10.7 | +9.1 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 10.4 | 18.2 | +7.8 |

## Peak memory

2 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| hadw6-8.qcir | 108 | 126 | 1.17x |
| hadw5-7.qcir | 27 | 30 | 1.11x |


---

# Paired comparison: B (M1-r1-mode2-s1) against A (baseline-c96-mode2-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | c39005a | 10ff614c6694 | 2026-11-23T02:40:07 |
| B | `-mode=2` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:34:06 |

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.92 s**, 95% bootstrap interval [-2.59, +0.63] (10000 resamples).

Sign test: B wins on 29 instances, loses on 27, ties on 320; two-sided p = 0.8939 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 77/53/130 | 82.3 | 76/58/134 | 81.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 130-130 | 82.3-82.3 |
| B | 134-134 | 81.3-81.3 |

## Instances gained and lost in a majority of seeds

- gained by B (7): `CM-sat-04-01-07-3.qcir`, `JP-unsat-02-06-3.qcir`, `hadw2-8.qcir`, `hadw3-7.qcir`, `jctc8-pass.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-100-25-t1.qcir`
- lost by B (3): `CM-sat-04-01-06-4.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `jctc6-pass.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 108.8 | 103.2 | -5.6 | 1 | 1 |
| DW | 7 | 40.5 | 42.0 | +1.5 | 0 | 2 |
| DWs | 13 | 97.2 | 98.0 | +0.9 | 0 | 1 |
| JP | 6 | 120.0 | 108.7 | -11.3 | 1 | 0 |
| Lights | 2 | 73.4 | 75.8 | +2.4 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.6 | 97.5 | -0.1 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| arbiter | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.3 | 91.4 | -1.0 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 31.1 | 33.0 | +1.9 | 2 | 6 |
| ci | 30 | 88.4 | 88.8 | +0.4 | 2 | 1 |
| collector | 1 | 7.2 | 7.8 | +0.6 | 0 | 0 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.2 | 65.8 | +1.5 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 48.4 | 52.0 | +3.6 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 75.9 | 69.3 | -6.7 | 4 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.4 | 83.4 | -0.0 | 1 | 1 |
| klieber | 26 | 43.9 | 37.6 | -6.3 | 9 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.4 | 62.2 | -0.3 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | -0.0 | 0 | 0 |
| ltl | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.8 | 0.7 | -0.1 | 0 | 0 |
| numeric | 26 | 31.8 | 32.3 | +0.5 | 0 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 57.2 | 57.5 | +0.3 | 0 | 0 |
| robot | 1 | 51.1 | 24.2 | -26.9 | 1 | 0 |
| round | 1 | 3.0 | 2.6 | -0.4 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 77.2 | 75.2 | -2.0 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 79.6 | 79.0 | -0.5 | 4 | 1 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc8-pass.qcir | 120.0 | 0.2 | -119.8 |
| CM-sat-04-01-07-3.qcir | 120.0 | 2.6 | -117.4 |
| klieber2017q-072-18-t1.qcir | 120.0 | 6.7 | -113.3 |
| klieber2017q-100-25-t1.qcir | 120.0 | 19.2 | -100.8 |
| hadw3-7.qcir | 120.0 | 48.3 | -71.7 |
| JP-unsat-02-06-3.qcir | 120.0 | 52.1 | -67.9 |
| hadw2-8.qcir | 120.0 | 58.6 | -61.4 |
| klieber2017q-112-28-t1.qcir | 49.7 | 17.5 | -32.2 |
| robot_grid6_1.tlsf.qcir | 51.1 | 24.2 | -26.9 |
| klieber2017q-088-22-t1.qcir | 34.2 | 8.0 | -26.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc6-pass.qcir | 0.1 | 120.0 | +119.9 |
| CM-sat-04-01-06-4.qcir | 41.7 | 120.0 | +78.3 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 57.7 | 120.0 | +62.3 |
| klieber2017q-066-16-eq.qcir | 15.8 | 51.6 | +35.8 |
| klieber2017q-074-18-t1.qcir | 10.0 | 38.1 | +28.2 |
| klieber2017q-068-17-t1.qcir | 23.4 | 49.5 | +26.2 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 1.5 | 21.2 | +19.8 |
| klieber2017q-072-18-eq.qcir | 16.7 | 34.4 | +17.7 |
| klieber2017q-078-19-eq.qcir | 28.1 | 39.4 | +11.3 |
| DWs-unsat-08-17-1.qcir | 40.0 | 50.9 | +10.9 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 13 | 19 | 1.53x |
| sc-ungrounded-1x2X2x2_2.qcir | 56 | 78 | 1.39x |
| DWs-unsat-08-17-1.qcir | 182 | 222 | 1.22x |


---

# Paired comparison: B (M1-r1-ccmin3-s1) against A (baseline-c96-ccmin3-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-ccmin-mode=3` | c39005a | 10ff614c6694 | 2026-11-23T02:52:10 |
| B | `-ccmin-mode=3` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:46:10 |

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.84 s**, 95% bootstrap interval [-2.81, +1.07] (10000 resamples).

Sign test: B wins on 36 instances, loses on 24, ties on 316; two-sided p = 0.1550 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 87/55/142 | 79.0 | 85/59/144 | 78.2 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 142-142 | 79.0-79.0 |
| B | 144-144 | 78.2-78.2 |

## Instances gained and lost in a majority of seeds

- gained by B (8): `CM-sat-04-01-06-3.qcir`, `klieber2017q-080-20-t1.qcir`, `klieber2017q-082-20-t1.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `test_5_5_domino.pg-15.qcir`
- lost by B (6): `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `jctc10-fail.qcir`, `klieber2017q-112-28-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 89.4 | 104.8 | +15.4 | 1 | 2 |
| DW | 7 | 38.2 | 42.0 | +3.8 | 0 | 2 |
| DWs | 13 | 110.9 | 110.9 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 58.8 | 120.0 | +61.2 | 0 | 2 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 88.7 | 87.7 | -1.0 | 0 | 0 |
| arbiter | 6 | 84.8 | 83.6 | -1.2 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 84.5 | 84.3 | -0.2 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 28.8 | 29.1 | +0.3 | 4 | 5 |
| ci | 30 | 100.2 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.7 | 2.9 | -0.7 | 0 | 0 |
| connect | 7 | 87.0 | 86.9 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 75.4 | 73.5 | -1.9 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 8.3 | 8.7 | +0.4 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.1 | 76.0 | -0.1 | 2 | 2 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 69.5 | 76.5 | +7.0 | 1 | 2 |
| klieber | 26 | 60.9 | 39.1 | -21.8 | 13 | 5 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.7 | -0.2 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.4 | 97.5 | -0.9 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.1 | 110.0 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 33.6 | 35.1 | +1.5 | 3 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 80.5 | 81.2 | +0.6 | 0 | 1 |
| robot | 1 | 3.3 | 2.7 | -0.7 | 0 | 0 |
| round | 1 | 1.6 | 1.9 | +0.3 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 57.2 | -1.1 | 2 | 1 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 45.5 | 41.7 | -3.9 | 4 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-080-20-t1.qcir | 120.0 | 9.1 | -110.9 |
| klieber2017q-082-20-t1.qcir | 120.0 | 9.7 | -110.3 |
| klieber2017q-088-22-t1.qcir | 120.0 | 12.7 | -107.3 |
| klieber2017q-108-27-t1.qcir | 120.0 | 12.9 | -107.1 |
| CM-sat-04-01-06-3.qcir | 120.0 | 13.8 | -106.2 |
| klieber2017q-084-21-t1.qcir | 120.0 | 15.3 | -104.7 |
| test_5_5_domino.pg-15.qcir | 120.0 | 27.2 | -92.8 |
| klieber2017q-086-21-t1.qcir | 120.0 | 59.4 | -60.6 |
| klieber2017q-078-19-t1.qcir | 58.2 | 1.4 | -56.8 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 50.9 | 29.0 | -21.9 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-4.qcir | 8.2 | 120.0 | +111.8 |
| CM-sat-04-01-07-3.qcir | 17.9 | 120.0 | +102.1 |
| jctc10-fail.qcir | 24.6 | 120.0 | +95.4 |
| klieber2017q-112-28-t1.qcir | 32.6 | 120.0 | +87.4 |
| Lights2_b02056d6.tlsf.qcir | 58.4 | 120.0 | +61.6 |
| Lights2_0f5381e9.tlsf.qcir | 59.2 | 120.0 | +60.8 |
| 5.2-1.qcir | 12.8 | 47.3 | +34.5 |
| klieber2017q-076-19-t1.qcir | 3.7 | 29.9 | +26.2 |
| klieber2017q-100-25-t1.qcir | 32.9 | 58.8 | +25.9 |
| 3.1.qcir | 33.8 | 54.1 | +20.3 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-2x1X1x2_2.qcir | 26 | 31 | 1.20x |
| hadw5-7.qcir | 32 | 38 | 1.16x |
| reachqu_query64_1344.qcir | 21 | 24 | 1.14x |

