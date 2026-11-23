# Paired comparison: B (M1-r3-ccmin3-s1) against A (M1-r2-ccmin3-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-ccmin-mode=3` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:28:38 |
| B | `-ccmin-mode=3` | 46874d9 | 006221175f2f | 2026-11-23T21:00:38 |

Order in which the runs started:

- 2026-11-23T14:28:38 `M1-r2-ccmin3-s1`
- 2026-11-23T21:00:38 `M1-r3-ccmin3-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.20 s**, 95% bootstrap interval [-0.82, +0.35] (10000 resamples).

Sign test: B wins on 11 instances, loses on 6, ties on 359; two-sided p = 0.3323 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 99 | 0.989 | 65 | 34 |
| all (per instance) | 99 | 0.989 | 65 | 34 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.974 |  |
| DW | 6 | 0.908 |  |
| DWs | 1 | 1.003 |  |
| amba | 2 | 1.026 |  |
| arbiter | 2 | 0.949 |  |
| bt | 2 | 1.002 |  |
| chess | 14 | 0.969 |  |
| collector | 1 | 0.999 |  |
| connect | 2 | 1.006 |  |
| eequery | 1 | 1.019 |  |
| finding | 1 | 0.987 |  |
| hadw | 5 | 0.947 |  |
| jctc | 4 | 0.919 |  |
| klieber | 21 | 1.017 |  |
| lift | 1 | 0.946 |  |
| ltl | 1 | 0.957 |  |
| mult | 1 | 1.012 |  |
| numeric | 13 | 0.993 |  |
| reachqu | 1 | 0.999 |  |
| robot | 1 | 1.023 |  |
| round | 1 | 0.937 |  |
| sc | 5 | 1.062 |  |
| test | 12 | 1.013 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.401 | 3.23 | 4.52 |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 1.290 | 5.12 | 6.61 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.235 | 8.93 | 11.03 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 1.153 | 20.79 | 23.98 |
| DW-unsat-10-25-1.qcir | 1.143 | 51.27 | 58.58 |
| 4.2.qcir | 1.104 | 1.59 | 1.76 |
| DW-sat-08-22-1.qcir | 1.103 | 1.53 | 1.69 |
| sc-ungrounded-2x1X1x3_1.qcir | 1.102 | 2.46 | 2.71 |
| sc-ungrounded-2x2X2x2_1.qcir | 1.087 | 16.72 | 18.17 |
| hadw9-10.qcir | 1.071 | 1.42 | 1.52 |
| DW-unsat-09-23-1.qcir | 1.069 | 19.86 | 21.24 |
| jctc8-pass.qcir | 1.065 | 24.75 | 26.37 |
| jctc10-fail.qcir | 1.061 | 52.37 | 55.57 |
| klieber2017q-070-17-eq.qcir | 1.061 | 15.51 | 16.45 |
| sc-ungrounded-2x1X1x2_2.qcir | 1.048 | 7.36 | 7.72 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 0.604 | 3.22 | 1.94 |
| DW-sat-08-23-1.qcir | 0.633 | 1.08 | 0.69 |
| DW-unsat-09-22-1.qcir | 0.636 | 19.20 | 12.20 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 0.758 | 36.21 | 27.45 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 0.768 | 14.84 | 11.40 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 85/61/146 | 77.7 | 87/60/147 | 77.5 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-146 | 77.7-77.7 |
| B | 147-147 | 77.5-77.5 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`
- lost by B (1): `klieber2017q-100-25-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 104.8 | 104.8 | -0.1 | 0 | 0 |
| DW | 7 | 31.0 | 31.2 | +0.2 | 1 | 1 |
| DWs | 13 | 110.9 | 110.9 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 120.0 | 55.2 | -64.8 | 2 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.3 | 87.6 | +0.3 | 0 | 0 |
| arbiter | 6 | 83.8 | 83.5 | -0.3 | 1 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 84.1 | 84.1 | +0.0 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.1 | 28.7 | -0.5 | 5 | 4 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 0 |
| collector | 1 | 2.6 | 2.6 | +0.0 | 0 | 0 |
| connect | 7 | 86.9 | 86.9 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 73.1 | 73.3 | +0.2 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 8.0 | 7.9 | -0.1 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.0 | 75.9 | -0.1 | 1 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 71.0 | 71.2 | +0.3 | 1 | 0 |
| klieber | 26 | 38.5 | 41.2 | +2.7 | 0 | 1 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.6 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | +0.0 | 0 | 0 |
| ltl | 5 | 97.4 | 97.3 | -0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 109.9 | 109.9 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 34.7 | 34.5 | -0.2 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 81.1 | 81.1 | -0.0 | 0 | 0 |
| robot | 1 | 2.5 | 2.6 | +0.0 | 0 | 0 |
| round | 1 | 2.0 | 1.9 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.9 | 57.1 | +0.2 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 41.6 | 41.7 | +0.1 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_b02056d6.tlsf.qcir | 120.0 | 53.7 | -66.3 |
| Lights2_0f5381e9.tlsf.qcir | 120.0 | 56.7 | -63.3 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 36.2 | 27.5 | -8.7 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 38.5 | 30.1 | -8.4 |
| DW-unsat-09-22-1.qcir | 19.2 | 12.2 | -7.0 |
| 5.2-1.qcir | 45.7 | 42.1 | -3.6 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 14.8 | 11.4 | -3.4 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 13.4 | 11.0 | -2.5 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 14.3 | 12.2 | -2.2 |
| arbiter_on_inpchange5.tlsf.qcir | 14.8 | 13.0 | -1.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-100-25-t1.qcir | 56.7 | 120.0 | +63.3 |
| DW-unsat-10-25-1.qcir | 51.3 | 58.7 | +7.4 |
| jctc10-fail.qcir | 52.4 | 55.6 | +3.2 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 20.8 | 24.0 | +3.2 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 9.0 | 11.1 | +2.1 |
| jctc8-pass.qcir | 24.8 | 26.4 | +1.6 |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 5.1 | 6.6 | +1.5 |
| sc-ungrounded-2x2X2x2_1.qcir | 16.8 | 18.2 | +1.4 |
| klieber2017q-086-21-t1.qcir | 57.7 | 59.1 | +1.4 |
| DW-unsat-09-23-1.qcir | 19.9 | 21.2 | +1.4 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

