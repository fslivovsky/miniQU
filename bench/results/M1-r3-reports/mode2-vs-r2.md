# Paired comparison: B (M1-r3-mode2-s1) against A (M1-r2-mode2-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:22:37 |
| B | `-mode=2` | 46874d9 | 006221175f2f | 2026-11-23T20:54:38 |

Order in which the runs started:

- 2026-11-23T14:22:37 `M1-r2-mode2-s1`
- 2026-11-23T20:54:38 `M1-r3-mode2-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.29 s**, 95% bootstrap interval [-0.97, +0.29] (10000 resamples).

Sign test: B wins on 12 instances, loses on 8, ties on 356; two-sided p = 0.5034 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 88 | 0.969 | 42 | 46 |
| all (per instance) | 88 | 0.969 | 42 | 46 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.901 |  |
| DW | 2 | 0.883 |  |
| DWs | 3 | 0.933 |  |
| Lights | 1 | 0.957 |  |
| SR | 1 | 1.163 |  |
| bt | 1 | 1.000 |  |
| chess | 14 | 0.879 |  |
| ci | 1 | 1.028 |  |
| collector | 1 | 1.187 |  |
| eequery | 1 | 1.019 |  |
| finding | 1 | 0.803 |  |
| hadw | 6 | 0.931 |  |
| jctc | 1 | 0.962 |  |
| klieber | 21 | 1.016 |  |
| lift | 1 | 0.713 |  |
| load | 1 | 1.031 |  |
| ltl | 1 | 0.947 |  |
| numeric | 14 | 0.974 |  |
| reachqu | 2 | 0.948 |  |
| robot | 1 | 0.967 |  |
| round | 1 | 0.840 |  |
| sc | 4 | 1.184 | > 1.10 |
| test | 8 | 1.001 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| sc-ungrounded-2x1X1x3_1.qcir | 1.281 | 5.60 | 7.17 |
| sc-ungrounded-1x3X3x2_1.qcir | 1.218 | 6.48 | 7.89 |
| collector_v17.tlsf.qcir | 1.187 | 6.03 | 7.16 |
| SR-unsat-04-01-08-1.qcir | 1.163 | 5.72 | 6.66 |
| sc-ungrounded-1x2X2x2_2.qcir | 1.145 | 24.39 | 27.93 |
| klieber2017q-076-19-t1.qcir | 1.134 | 17.46 | 19.80 |
| DWs-unsat-08-17-1.qcir | 1.106 | 38.83 | 42.94 |
| sc-ungrounded-2x1X1x2_2.qcir | 1.102 | 29.70 | 32.72 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 1.093 | 7.36 | 8.05 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.052 | 1.49 | 1.56 |
| DWs-sat-10-25-1.qcir | 1.040 | 2.66 | 2.77 |
| klieber2017q-070-17-t1.qcir | 1.039 | 5.76 | 5.99 |
| 9.1.qcir | 1.033 | 4.00 | 4.13 |
| load_balancer5.tlsf.qcir | 1.031 | 3.74 | 3.86 |
| 8.1.qcir | 1.031 | 4.93 | 5.08 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-unsat-08-18-1.qcir | 0.705 | 16.81 | 11.86 |
| lift_gr1+2.tlsf.qcir | 0.713 | 5.06 | 3.61 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 0.726 | 1.64 | 1.19 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 0.727 | 1.10 | 0.80 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 0.743 | 12.70 | 9.44 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 77/57/134 | 81.2 | 78/57/135 | 80.9 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 134-134 | 81.2-81.2 |
| B | 135-135 | 80.9-80.9 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `JP-unsat-02-06-3.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`
- lost by B (1): `hadw3-7.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 103.2 | 103.2 | -0.0 | 0 | 0 |
| DW | 7 | 40.9 | 40.1 | -0.7 | 1 | 0 |
| DWs | 13 | 96.8 | 96.7 | -0.1 | 1 | 1 |
| JP | 6 | 120.0 | 108.7 | -11.3 | 1 | 0 |
| Lights | 2 | 74.5 | 73.9 | -0.6 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.1 | 97.3 | +0.2 | 0 | 0 |
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
| bt | 12 | 91.3 | 91.3 | +0.0 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 33.1 | 31.0 | -2.1 | 6 | 0 |
| ci | 30 | 88.8 | 88.8 | +0.0 | 0 | 0 |
| collector | 1 | 6.0 | 7.2 | +1.2 | 0 | 1 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 65.5 | 65.6 | +0.1 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 50.9 | 40.9 | -10.0 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.4 | 72.1 | +2.7 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.3 | 83.3 | -0.0 | 0 | 0 |
| klieber | 26 | 36.8 | 37.0 | +0.2 | 0 | 1 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.5 | 61.8 | -0.7 | 1 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | +0.0 | 0 | 0 |
| ltl | 5 | 107.5 | 106.9 | -0.6 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.7 | 0.7 | +0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 31.6 | -0.3 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 55.6 | 54.9 | -0.7 | 0 | 0 |
| robot | 1 | 25.1 | 24.3 | -0.8 | 0 | 0 |
| round | 1 | 3.0 | 2.6 | -0.5 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 74.0 | 75.1 | +1.1 | 0 | 4 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 79.0 | 79.0 | +0.0 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 120.0 | 50.5 | -69.5 |
| JP-unsat-02-06-3.qcir | 120.0 | 52.4 | -67.6 |
| finding_nemo_1.tlsf.qcir | 50.9 | 40.9 | -10.0 |
| hadw2-8.qcir | 55.0 | 48.9 | -6.0 |
| DWs-unsat-08-18-1.qcir | 16.9 | 11.9 | -5.0 |
| DW-unsat-09-22-1.qcir | 22.4 | 17.6 | -4.9 |
| 5.2-2.qcir | 56.2 | 51.8 | -4.3 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 12.7 | 9.5 | -3.3 |
| ltl2dba_beta6.tlsf.qcir | 57.5 | 54.4 | -3.1 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 23.4 | 20.6 | -2.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| hadw3-7.qcir | 55.4 | 120.0 | +64.6 |
| DWs-unsat-08-17-1.qcir | 38.9 | 43.0 | +4.1 |
| sc-ungrounded-1x2X2x2_2.qcir | 24.4 | 28.0 | +3.5 |
| sc-ungrounded-2x1X1x2_2.qcir | 29.7 | 32.7 | +3.0 |
| klieber2017q-076-19-t1.qcir | 17.5 | 19.8 | +2.3 |
| sc-ungrounded-2x1X1x3_1.qcir | 5.6 | 7.2 | +1.6 |
| sc-ungrounded-1x3X3x2_1.qcir | 6.5 | 7.9 | +1.4 |
| collector_v17.tlsf.qcir | 6.0 | 7.2 | +1.2 |
| SR-unsat-04-01-08-1.qcir | 5.7 | 6.7 | +1.0 |
| klieber2017q-074-18-eq.qcir | 54.0 | 54.9 | +0.9 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

