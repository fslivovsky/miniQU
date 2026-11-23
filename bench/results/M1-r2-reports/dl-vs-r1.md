# Paired comparison: B (M1-r2-dl-s1, M1-r2-dl-s2, M1-r2-dl-s3) against A (M1-r1-dl-s1, M1-r1-dl-s2, M1-r1-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | 00eb7a4 | a48a1a946f47 | 2026-11-23T01:22:04 |
| B | `-dl` | 25216c2 | 30bd8fe6b956 | 2026-11-23T13:58:44 |

Order in which the runs started:

- 2026-11-23T01:22:04 `M1-r1-dl-s1`
- 2026-11-23T01:45:54 `M1-r1-dl-s2`
- 2026-11-23T02:09:46 `M1-r1-dl-s3`
- 2026-11-23T13:58:44 `M1-r2-dl-s1`
- 2026-11-23T14:04:39 `M1-r2-dl-s2`
- 2026-11-23T14:10:31 `M1-r2-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.34 s**, 95% bootstrap interval [-0.55, -0.19] (10000 resamples).

Sign test: B wins on 18 instances, loses on 0, ties on 358; two-sided p = 0.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 110 | 0.928 | 17 | 93 |
| 2 | 119 | 0.943 | 21 | 98 |
| 3 | 112 | 0.936 | 14 | 98 |
| all (per instance) | 129 | 0.939 | 16 | 113 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 3 | 0.974 |  |
| DW | 7 | 0.822 |  |
| JP | 1 | 0.948 |  |
| Lights | 1 | 0.947 |  |
| SR | 2 | 0.926 |  |
| amba | 2 | 0.981 |  |
| arbiter | 2 | 0.963 |  |
| bt | 2 | 0.978 |  |
| chess | 21 | 0.848 |  |
| ci | 3 | 0.989 |  |
| collector | 1 | 0.895 |  |
| connect | 2 | 0.982 |  |
| eequery | 1 | 0.975 |  |
| finding | 1 | 0.963 |  |
| hadw | 7 | 0.982 |  |
| jctc | 7 | 0.966 |  |
| klieber | 26 | 0.974 |  |
| lift | 1 | 1.039 |  |
| load | 1 | 0.966 |  |
| ltl | 1 | 1.027 |  |
| mult | 1 | 0.977 |  |
| numeric | 14 | 0.948 |  |
| reachqu | 2 | 1.004 |  |
| robot | 1 | 0.981 |  |
| round | 1 | 1.029 |  |
| sc | 5 | 0.865 |  |
| test | 12 | 0.998 |  |
| voter | 1 | 1.033 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| hadw11-12.qcir | 1.239 | 44.22 | 54.80 |
| reachqu_query60_1344.qcir | 1.065 | 18.91 | 20.15 |
| 5.2-1.qcir | 1.057 | 28.62 | 30.25 |
| hadw5-7.qcir | 1.045 | 2.09 | 2.19 |
| lift_gr1+2.tlsf.qcir | 1.039 | 2.13 | 2.26 |
| jctc2-pass.qcir | 1.034 | 5.12 | 5.06 |
| voter_size_202219_1U43.qcir | 1.033 | 12.18 | 12.58 |
| round_robin_arbiter3.tlsf.qcir | 1.029 | 1.64 | 1.68 |
| ltl2dba_beta6.tlsf.qcir | 1.027 | 15.70 | 16.08 |
| test_5_5_fatty.pg-9.qcir | 1.012 | 46.89 | 47.48 |
| test_5_5_knobby.pg-9.qcir | 1.011 | 17.90 | 18.09 |
| test_5_5_skinny.pg-9.qcir | 1.009 | 31.79 | 32.06 |
| test_5_5_elly.pg-9.qcir | 1.006 | 10.82 | 10.88 |
| test_5_5_elly.pg-7.qcir | 1.003 | 1.16 | 1.16 |
| hadw2-7.qcir | 1.002 | 18.87 | 18.91 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | 0.701 | 6.41 | 4.41 |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 0.717 | 5.52 | 4.07 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.763 | 6.96 | 5.49 |
| DW-sat-08-22-1.qcir | 0.763 | 12.18 | 9.30 |
| DW-sat-09-26-1.qcir | 0.779 | 35.31 | 26.93 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/64/148 | 77.0 | 84/65/149 | 76.6 |
| 2 | 86/65/151 | 76.2 | 86/65/151 | 76.0 |
| 3 | 82/63/145 | 77.8 | 83/63/146 | 77.4 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 145-151 | 76.2-77.8 |
| B | 146-151 | 76.0-77.4 |

## Instances gained and lost in a majority of seeds

- gained by B (0): none
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 89.1 | 88.9 | -0.2 | 0 | 0 |
| DW | 7 | 21.6 | 18.4 | -3.2 | 5 | 0 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 113.0 | 109.1 | -3.8 | 1 | 0 |
| Lights | 2 | 75.5 | 74.7 | -0.8 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 105.1 | 104.2 | -1.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 91.3 | 91.1 | -0.2 | 0 | 0 |
| arbiter | 6 | 84.9 | 84.6 | -0.2 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 83.6 | 83.6 | -0.1 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 62.7 | 61.5 | -1.2 | 12 | 0 |
| ci | 30 | 88.6 | 88.6 | -0.0 | 0 | 0 |
| collector | 1 | 4.8 | 4.3 | -0.5 | 0 | 0 |
| connect | 7 | 87.7 | 87.6 | -0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 70.2 | 69.9 | -0.3 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 9.4 | 9.1 | -0.4 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.5 | 78.4 | -0.1 | 0 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 39.9 | 39.7 | -0.2 | 0 | 0 |
| klieber | 26 | 16.3 | 16.0 | -0.3 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.1 | 61.1 | +0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.1 | 99.2 | +0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.8 | 111.6 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | -0.0 | 0 | 0 |
| numeric | 26 | 37.8 | 37.6 | -0.2 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 80.2 | 79.8 | -0.4 | 0 | 0 |
| robot | 1 | 3.3 | 3.3 | -0.0 | 0 | 0 |
| round | 1 | 1.3 | 1.3 | +0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.4 | 56.2 | -0.2 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 37.3 | 37.3 | +0.0 | 0 | 0 |
| voter | 2 | 102.0 | 102.1 | +0.1 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| JP-unsat-02-06-3.qcir | 77.8 | 54.7 | -23.1 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 62.5 | 40.9 | -21.6 |
| DW-sat-09-26-1.qcir | 35.3 | 26.9 | -8.4 |
| SR-unsat-04-01-08-1.qcir | 75.3 | 70.6 | -4.7 |
| DW-unsat-10-25-1.qcir | 23.8 | 19.5 | -4.3 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 20.2 | 16.2 | -4.0 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 19.0 | 15.1 | -3.9 |
| hadw10-11.qcir | 65.1 | 61.4 | -3.6 |
| DW-unsat-11-26-1.qcir | 59.6 | 56.2 | -3.4 |
| DW-sat-08-22-1.qcir | 12.2 | 9.3 | -2.9 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| hadw11-12.qcir | 94.7 | 98.3 | +3.5 |
| 5.2-1.qcir | 59.1 | 60.2 | +1.1 |
| test_5_5_fatty.pg-9.qcir | 46.9 | 47.5 | +0.6 |
| reachqu_query60_1344.qcir | 86.3 | 86.7 | +0.4 |
| ltl2dba_beta6.tlsf.qcir | 15.7 | 16.1 | +0.4 |
| test_5_5_skinny.pg-9.qcir | 61.2 | 61.4 | +0.2 |
| test_5_5_knobby.pg-9.qcir | 17.9 | 18.1 | +0.2 |
| lift_gr1+2.tlsf.qcir | 2.1 | 2.3 | +0.1 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 7.1 | 7.2 | +0.1 |
| voter_size_202219_1U43.qcir | 84.1 | 84.2 | +0.1 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

