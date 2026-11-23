# Paired comparison: B (M1-r3-dl-s1, M1-r3-dl-s2, M1-r3-dl-s3) against A (M1-r2-dl-s1, M1-r2-dl-s2, M1-r2-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | 25216c2 | 30bd8fe6b956 | 2026-11-23T13:58:44 |
| B | `-dl` | 46874d9 | 006221175f2f | 2026-11-23T20:30:44 |

Order in which the runs started:

- 2026-11-23T13:58:44 `M1-r2-dl-s1`
- 2026-11-23T14:04:39 `M1-r2-dl-s2`
- 2026-11-23T14:10:31 `M1-r2-dl-s3`
- 2026-11-23T20:30:44 `M1-r3-dl-s1`
- 2026-11-23T20:36:39 `M1-r3-dl-s2`
- 2026-11-23T20:42:30 `M1-r3-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.17 s**, 95% bootstrap interval [-0.52, +0.13] (10000 resamples).

Sign test: B wins on 11 instances, loses on 4, ties on 361; two-sided p = 0.1185 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 109 | 0.979 | 58 | 51 |
| 2 | 119 | 0.979 | 64 | 55 |
| 3 | 111 | 0.979 | 59 | 51 |
| all (per instance) | 128 | 0.979 | 64 | 64 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 3 | 0.948 |  |
| DW | 7 | 0.932 |  |
| JP | 1 | 1.023 |  |
| Lights | 1 | 0.897 |  |
| SR | 2 | 0.945 |  |
| amba | 2 | 1.022 |  |
| arbiter | 2 | 0.909 |  |
| bt | 2 | 0.996 |  |
| chess | 21 | 0.965 |  |
| ci | 3 | 1.038 |  |
| collector | 1 | 0.867 |  |
| connect | 2 | 1.010 |  |
| eequery | 1 | 1.020 |  |
| finding | 1 | 0.855 |  |
| hadw | 7 | 0.935 |  |
| jctc | 7 | 0.990 |  |
| klieber | 26 | 1.011 |  |
| lift | 1 | 0.927 |  |
| load | 1 | 0.962 |  |
| ltl | 1 | 0.879 |  |
| mult | 1 | 0.984 |  |
| numeric | 14 | 0.995 |  |
| reachqu | 2 | 0.982 |  |
| robot | 1 | 0.975 |  |
| round | 1 | 0.950 |  |
| sc | 4 | 0.983 |  |
| test | 12 | 1.004 |  |
| voter | 1 | 0.944 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 1.344 | 6.36 | 8.53 |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | 1.130 | 9.88 | 11.53 |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | 1.084 | 3.65 | 3.92 |
| DW-sat-09-26-1.qcir | 1.082 | 26.93 | 29.18 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.064 | 31.45 | 33.70 |
| jctc6-pass.qcir | 1.052 | 8.77 | 9.22 |
| ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir | 1.045 | 1.47 | 1.54 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 1.038 | 13.26 | 13.86 |
| 9.2.qcir | 1.035 | 18.88 | 19.54 |
| jctc17-vals-0,2-pass.qcir | 1.033 | 15.15 | 15.42 |
| ci.e#1.a#3.E#40.A#60.c#208.w#6.s#8.asp.qcir | 1.032 | 1.40 | 1.44 |
| jctc4-fail.qcir | 1.028 | 3.61 | 3.71 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.027 | 15.07 | 15.63 |
| arbiter_with_buffer5.tlsf.qcir | 1.025 | 5.36 | 5.49 |
| 4.2.qcir | 1.025 | 4.36 | 4.50 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir | 0.741 | 1.95 | 1.46 |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.804 | 4.50 | 3.65 |
| arbiter_on_inpchange5.tlsf.qcir | 0.805 | 22.24 | 18.03 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 0.815 | 6.32 | 4.73 |
| DW-sat-08-22-1.qcir | 0.848 | 9.30 | 7.59 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/65/149 | 76.6 | 85/64/149 | 76.5 |
| 2 | 86/65/151 | 76.0 | 88/65/153 | 75.6 |
| 3 | 83/63/146 | 77.4 | 83/63/146 | 77.4 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-151 | 76.0-77.4 |
| B | 146-153 | 75.6-77.4 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `Lights2_0f5381e9.tlsf.qcir`
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 88.9 | 88.4 | -0.5 | 0 | 0 |
| DW | 7 | 18.4 | 18.2 | -0.2 | 2 | 0 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 109.1 | 112.8 | +3.7 | 0 | 1 |
| Lights | 2 | 74.7 | 52.0 | -22.7 | 2 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 104.2 | 104.0 | -0.2 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 91.1 | 91.3 | +0.2 | 0 | 0 |
| arbiter | 6 | 84.6 | 83.9 | -0.7 | 1 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 83.6 | 83.5 | -0.0 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.5 | 62.0 | +0.5 | 1 | 3 |
| ci | 30 | 88.6 | 88.6 | +0.0 | 0 | 0 |
| collector | 1 | 4.3 | 3.8 | -0.6 | 0 | 0 |
| connect | 7 | 87.6 | 87.7 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.9 | 70.1 | +0.2 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 9.1 | 7.8 | -1.3 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.4 | 78.0 | -0.4 | 1 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 39.7 | 38.2 | -1.5 | 1 | 0 |
| klieber | 26 | 16.0 | 16.1 | +0.1 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.1 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.2 | 98.8 | -0.4 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.6 | 111.6 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | +0.0 | 0 | 0 |
| numeric | 26 | 37.6 | 36.7 | -0.9 | 1 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 79.8 | 79.8 | +0.0 | 0 | 0 |
| robot | 1 | 3.3 | 3.2 | -0.1 | 0 | 0 |
| round | 1 | 1.3 | 1.3 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.2 | 56.1 | -0.1 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 37.3 | 37.3 | +0.0 | 0 | 0 |
| voter | 2 | 102.1 | 102.0 | -0.1 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_0f5381e9.tlsf.qcir | 120.0 | 77.6 | -42.4 |
| 5.2-1.qcir | 60.2 | 37.1 | -23.1 |
| jctc1-pass.qcir | 80.0 | 60.0 | -20.0 |
| hadw10-11.qcir | 61.4 | 56.1 | -5.4 |
| arbiter_on_inpchange5.tlsf.qcir | 22.3 | 18.1 | -4.2 |
| Lights2_b02056d6.tlsf.qcir | 29.4 | 26.4 | -3.0 |
| ltl2dba_beta6.tlsf.qcir | 16.1 | 14.2 | -1.9 |
| DW-sat-08-22-1.qcir | 9.3 | 7.6 | -1.7 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 6.4 | 4.7 | -1.6 |
| CM-sat-04-01-06-3.qcir | 24.6 | 23.1 | -1.5 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| JP-unsat-02-06-3.qcir | 54.7 | 76.6 | +21.9 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 40.9 | 62.5 | +21.6 |
| DW-sat-09-26-1.qcir | 26.9 | 29.2 | +2.3 |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 6.4 | 8.6 | +2.2 |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | 9.9 | 11.5 | +1.6 |
| DW-unsat-10-25-1.qcir | 19.5 | 20.8 | +1.3 |
| amba2f9n.sat.qcir | 75.6 | 76.3 | +0.8 |
| 9.2.qcir | 18.9 | 19.6 | +0.7 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 13.3 | 13.9 | +0.6 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 15.1 | 15.7 | +0.6 |

## Peak memory

1 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| bt-3x6_9.ig.qcir | 16 | 20 | 1.22x |

