# Paired comparison: B (M1-r2-mode2-s1) against A (M1-r1-mode2-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:34:06 |
| B | `-mode=2` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:22:37 |

Order in which the runs started:

- 2026-11-23T02:34:06 `M1-r1-mode2-s1`
- 2026-11-23T14:22:37 `M1-r2-mode2-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.18 s**, 95% bootstrap interval [-0.68, +0.36] (10000 resamples).

Sign test: B wins on 12 instances, loses on 4, ties on 360; two-sided p = 0.0768 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 89 | 0.959 | 15 | 74 |
| all (per instance) | 89 | 0.959 | 15 | 74 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.973 |  |
| DW | 4 | 0.838 |  |
| DWs | 3 | 0.804 |  |
| Lights | 1 | 0.917 |  |
| SR | 1 | 0.780 |  |
| bt | 1 | 0.974 |  |
| chess | 13 | 1.053 |  |
| ci | 1 | 0.928 |  |
| collector | 1 | 0.779 |  |
| eequery | 1 | 0.960 |  |
| finding | 1 | 0.979 |  |
| hadw | 7 | 1.013 |  |
| jctc | 1 | 0.900 |  |
| klieber | 21 | 0.955 |  |
| lift | 1 | 1.173 |  |
| load | 1 | 0.957 |  |
| numeric | 14 | 0.940 |  |
| reachqu | 2 | 0.965 |  |
| robot | 1 | 1.037 |  |
| round | 1 | 1.183 |  |
| sc | 4 | 0.869 |  |
| test | 8 | 0.986 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 1.280 | 9.93 | 12.70 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.253 | 1.31 | 1.64 |
| round_robin_arbiter3.tlsf.qcir | 1.183 | 2.53 | 3.00 |
| lift_gr1+2.tlsf.qcir | 1.173 | 4.31 | 5.06 |
| hadw3-7.qcir | 1.147 | 48.30 | 55.38 |
| hadw5-7.qcir | 1.140 | 4.15 | 4.73 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 1.122 | 16.06 | 18.02 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.103 | 5.95 | 6.56 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.096 | 4.76 | 5.21 |
| reachqu_query60_1344.qcir | 1.059 | 3.28 | 3.47 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 1.058 | 1.11 | 1.18 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 1.041 | 22.41 | 23.33 |
| robot_grid6_1.tlsf.qcir | 1.037 | 24.21 | 25.10 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.033 | 4.46 | 4.61 |
| 5.2-1.qcir | 1.009 | 6.24 | 6.29 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-unsat-08-17-1.qcir | 0.762 | 50.94 | 38.83 |
| collector_v17.tlsf.qcir | 0.779 | 7.74 | 6.03 |
| SR-unsat-04-01-08-1.qcir | 0.780 | 7.33 | 5.72 |
| DW-sat-08-23-1.qcir | 0.781 | 1.01 | 0.79 |
| sc-ungrounded-1x2X2x2_2.qcir | 0.816 | 29.90 | 24.39 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 76/58/134 | 81.3 | 77/57/134 | 81.2 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 134-134 | 81.3-81.3 |
| B | 134-134 | 81.2-81.2 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `ltl2dba_beta6.tlsf.qcir`
- lost by B (1): `JP-unsat-02-06-3.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 103.2 | 103.2 | -0.0 | 0 | 0 |
| DW | 7 | 42.0 | 40.9 | -1.1 | 2 | 0 |
| DWs | 13 | 98.0 | 96.8 | -1.2 | 2 | 0 |
| JP | 6 | 108.7 | 120.0 | +11.3 | 0 | 1 |
| Lights | 2 | 75.8 | 74.5 | -1.3 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.5 | 97.1 | -0.3 | 1 | 0 |
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
| bt | 12 | 91.4 | 91.3 | -0.0 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 33.0 | 33.1 | +0.1 | 0 | 2 |
| ci | 30 | 88.8 | 88.8 | -0.1 | 0 | 0 |
| collector | 1 | 7.8 | 6.0 | -1.7 | 1 | 0 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 65.8 | 65.5 | -0.2 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 52.0 | 50.9 | -1.1 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.3 | 69.4 | +0.2 | 0 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.4 | 83.3 | -0.0 | 0 | 0 |
| klieber | 26 | 37.6 | 36.8 | -0.8 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.2 | 62.5 | +0.4 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | -0.0 | 0 | 0 |
| ltl | 5 | 120.0 | 107.5 | -12.5 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.7 | 0.7 | -0.0 | 0 | 0 |
| numeric | 26 | 32.3 | 31.8 | -0.5 | 1 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 57.5 | 55.6 | -1.9 | 1 | 0 |
| robot | 1 | 24.2 | 25.1 | +0.9 | 0 | 0 |
| round | 1 | 2.6 | 3.0 | +0.5 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 75.2 | 74.0 | -1.2 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 79.0 | 79.0 | -0.0 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| ltl2dba_beta6.tlsf.qcir | 120.0 | 57.5 | -62.5 |
| DWs-unsat-08-17-1.qcir | 50.9 | 38.9 | -12.1 |
| reachqu_query64_1344.qcir | 49.3 | 43.3 | -6.0 |
| sc-ungrounded-1x2X2x2_2.qcir | 29.9 | 24.4 | -5.5 |
| DW-unsat-09-22-1.qcir | 26.5 | 22.4 | -4.1 |
| hadw2-8.qcir | 58.6 | 55.0 | -3.7 |
| DWs-unsat-08-18-1.qcir | 20.4 | 16.9 | -3.6 |
| sc-ungrounded-2x1X1x2_2.qcir | 33.1 | 29.7 | -3.4 |
| DW-unsat-09-23-1.qcir | 24.6 | 21.4 | -3.2 |
| 11.1.qcir | 55.1 | 52.1 | -3.0 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| JP-unsat-02-06-3.qcir | 52.1 | 120.0 | +67.9 |
| hadw3-7.qcir | 48.3 | 55.4 | +7.1 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 10.0 | 12.7 | +2.8 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 16.1 | 18.0 | +1.9 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 22.5 | 23.4 | +0.9 |
| robot_grid6_1.tlsf.qcir | 24.2 | 25.1 | +0.9 |
| lift_gr1+2.tlsf.qcir | 4.3 | 5.1 | +0.8 |
| hadw5-7.qcir | 4.2 | 4.8 | +0.6 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 6.0 | 6.6 | +0.6 |
| round_robin_arbiter3.tlsf.qcir | 2.6 | 3.0 | +0.5 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

