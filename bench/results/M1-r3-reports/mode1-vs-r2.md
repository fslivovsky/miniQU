# Paired comparison: B (M1-r3-mode1-s1) against A (M1-r2-mode1-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:16:26 |
| B | `-mode=1` | 46874d9 | 006221175f2f | 2026-11-23T20:48:28 |

Order in which the runs started:

- 2026-11-23T14:16:26 `M1-r2-mode1-s1`
- 2026-11-23T20:48:28 `M1-r3-mode1-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.20 s**, 95% bootstrap interval [-0.81, +0.42] (10000 resamples).

Sign test: B wins on 10 instances, loses on 3, ties on 363; two-sided p = 0.0923 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 75 | 0.962 | 37 | 38 |
| all (per instance) | 75 | 0.962 | 37 | 38 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.995 |  |
| DW | 5 | 0.727 |  |
| amba | 1 | 1.030 |  |
| arbiter | 2 | 0.970 |  |
| bt | 2 | 1.004 |  |
| chess | 16 | 0.925 |  |
| collector | 1 | 0.955 |  |
| connect | 2 | 1.011 |  |
| eequery | 1 | 1.030 |  |
| finding | 1 | 0.791 |  |
| hadw | 6 | 0.948 |  |
| jctc | 3 | 1.152 | > 1.10 |
| klieber | 1 | 1.016 |  |
| lift | 1 | 0.991 |  |
| load | 1 | 1.005 |  |
| ltl | 1 | 0.978 |  |
| mult | 1 | 0.996 |  |
| numeric | 12 | 0.991 |  |
| reachqu | 1 | 1.015 |  |
| robot | 1 | 0.949 |  |
| round | 1 | 0.937 |  |
| sc | 5 | 1.021 |  |
| test | 9 | 1.018 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 1.538 | 4.28 | 6.58 |
| sc-ungrounded-1x3X3x2_1.qcir | 1.254 | 1.22 | 1.53 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 1.244 | 15.32 | 19.05 |
| sc-ungrounded-1x2X2x2_2.qcir | 1.066 | 5.43 | 5.79 |
| 4.1.qcir | 1.051 | 8.06 | 8.48 |
| sc-ungrounded-2x1X1x2_2.qcir | 1.045 | 6.41 | 6.70 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.043 | 5.41 | 5.64 |
| hadw4-7.qcir | 1.041 | 52.95 | 55.11 |
| 9.2.qcir | 1.034 | 20.47 | 21.16 |
| amba2c7n.sat.qcir | 1.030 | 27.57 | 28.41 |
| eequery_query42_1344.qcir | 1.030 | 23.61 | 24.33 |
| 8.1.qcir | 1.030 | 4.15 | 4.27 |
| jctc6-pass.qcir | 1.029 | 2.14 | 2.21 |
| test_5_5_knobby.pg-7.qcir | 1.024 | 7.00 | 7.17 |
| test_5_5_domino.pg-11.qcir | 1.024 | 4.09 | 4.19 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-unsat-09-22-1.qcir | 0.527 | 17.30 | 9.11 |
| DW-sat-08-22-1.qcir | 0.647 | 2.68 | 1.73 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 0.657 | 17.25 | 11.34 |
| DW-sat-08-23-1.qcir | 0.673 | 2.73 | 1.83 |
| hadw9-10.qcir | 0.738 | 1.35 | 1.00 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 70/44/114 | 86.3 | 72/43/115 | 86.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 114-114 | 86.3-86.3 |
| B | 115-115 | 86.1-86.1 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `5.1-1.qcir`, `Lights2_b02056d6.tlsf.qcir`
- lost by B (1): `jctc14-unrolled-fail.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 103.1 | 103.1 | -0.0 | 0 | 0 |
| DW | 7 | 41.3 | 39.7 | -1.6 | 1 | 0 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 120.0 | 87.6 | -32.4 | 1 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.5 | 101.7 | +0.2 | 0 | 0 |
| arbiter | 6 | 85.2 | 85.0 | -0.2 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 93.7 | 93.7 | -0.0 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.9 | 29.4 | -0.4 | 4 | 1 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 0 |
| collector | 1 | 3.5 | 3.4 | -0.2 | 0 | 0 |
| connect | 7 | 89.1 | 89.1 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 71.8 | 72.2 | +0.4 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 11.7 | 9.3 | -2.4 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 72.2 | 72.2 | +0.0 | 0 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 70.8 | 77.1 | +6.2 | 0 | 2 |
| klieber | 26 | 116.5 | 116.5 | +0.0 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.0 | 61.0 | +0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | +0.0 | 0 | 0 |
| ltl | 5 | 97.8 | 97.8 | -0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.8 | 110.8 | -0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 34.4 | 32.0 | -2.4 | 2 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 91.5 | 91.7 | +0.2 | 0 | 0 |
| robot | 1 | 4.0 | 3.8 | -0.2 | 0 | 0 |
| round | 1 | 1.5 | 1.4 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.8 | 56.7 | -0.1 | 1 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 70.7 | 70.7 | +0.0 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_b02056d6.tlsf.qcir | 120.0 | 55.3 | -64.7 |
| 5.1-1.qcir | 120.0 | 59.8 | -60.2 |
| DW-unsat-09-22-1.qcir | 17.3 | 9.2 | -8.2 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 38.8 | 32.8 | -6.0 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 17.3 | 11.4 | -5.9 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 41.5 | 36.8 | -4.7 |
| 5.2-1.qcir | 36.4 | 31.9 | -4.5 |
| finding_nemo_1.tlsf.qcir | 11.7 | 9.3 | -2.4 |
| sc-ungrounded-2x2X2x2_1.qcir | 16.7 | 14.5 | -2.1 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 17.4 | 15.8 | -1.6 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc14-unrolled-fail.qcir | 40.3 | 120.0 | +79.7 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 15.3 | 19.1 | +3.7 |
| jctc2-pass.qcir | 4.3 | 6.6 | +2.3 |
| hadw4-7.qcir | 53.0 | 55.1 | +2.2 |
| amba2c7n.sat.qcir | 27.6 | 28.5 | +0.9 |
| eequery_query42_1344.qcir | 23.7 | 24.4 | +0.7 |
| 9.2.qcir | 20.5 | 21.2 | +0.7 |
| 3.1.qcir | 45.5 | 46.1 | +0.6 |
| reachqu_query64_1344.qcir | 34.5 | 35.1 | +0.6 |
| 11.1.qcir | 35.2 | 35.7 | +0.5 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

