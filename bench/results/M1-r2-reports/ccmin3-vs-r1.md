# Paired comparison: B (M1-r2-ccmin3-s1) against A (M1-r1-ccmin3-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-ccmin-mode=3` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:46:10 |
| B | `-ccmin-mode=3` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:28:38 |

Order in which the runs started:

- 2026-11-23T02:46:10 `M1-r1-ccmin3-s1`
- 2026-11-23T14:28:38 `M1-r2-ccmin3-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.48 s**, 95% bootstrap interval [-1.05, -0.09] (10000 resamples).

Sign test: B wins on 7 instances, loses on 3, ties on 366; two-sided p = 0.3438 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 98 | 0.949 | 13 | 85 |
| all (per instance) | 98 | 0.949 | 13 | 85 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.985 |  |
| DW | 5 | 0.834 |  |
| DWs | 1 | 0.894 |  |
| amba | 2 | 0.973 |  |
| arbiter | 2 | 1.017 |  |
| bt | 2 | 0.964 |  |
| chess | 14 | 0.967 |  |
| collector | 1 | 0.892 |  |
| connect | 2 | 0.988 |  |
| eequery | 1 | 0.970 |  |
| finding | 1 | 0.926 |  |
| hadw | 5 | 0.972 |  |
| jctc | 3 | 0.803 |  |
| klieber | 22 | 0.971 |  |
| lift | 1 | 0.938 |  |
| ltl | 1 | 0.913 |  |
| mult | 1 | 0.976 |  |
| numeric | 13 | 0.923 |  |
| reachqu | 1 | 0.906 |  |
| robot | 1 | 0.941 |  |
| round | 1 | 1.033 |  |
| sc | 5 | 0.926 |  |
| test | 12 | 0.992 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 1.249 | 28.98 | 36.21 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 1.141 | 33.74 | 38.48 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.125 | 13.19 | 14.84 |
| hadw2-7.qcir | 1.080 | 15.23 | 16.45 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.072 | 1.12 | 1.20 |
| arbiter_on_inpchange5.tlsf.qcir | 1.067 | 13.87 | 14.79 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 1.060 | 13.53 | 14.34 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.035 | 1.76 | 1.82 |
| round_robin_arbiter3.tlsf.qcir | 1.033 | 1.88 | 1.95 |
| hadw5-7.qcir | 1.031 | 9.91 | 10.22 |
| test_5_5_snaky.pg-7.qcir | 1.010 | 4.95 | 5.00 |
| test_5_5_tippy.pg-7.qcir | 1.005 | 2.20 | 2.21 |
| test_5_5_tippy.pg-9.qcir | 1.001 | 17.37 | 17.39 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 0.999 | 18.04 | 18.02 |
| test_5_5_knobby.pg-9.qcir | 0.998 | 52.53 | 52.43 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 0.559 | 5.76 | 3.22 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 0.720 | 12.40 | 8.93 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.786 | 4.11 | 3.23 |
| DW-sat-08-22-1.qcir | 0.792 | 1.94 | 1.53 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 0.793 | 26.24 | 20.79 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 85/59/144 | 78.2 | 85/61/146 | 77.7 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 144-144 | 78.2-78.2 |
| B | 146-146 | 77.7-77.7 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `DW-unsat-10-25-1.qcir`, `jctc10-fail.qcir`
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 104.8 | 104.8 | -0.0 | 0 | 0 |
| DW | 7 | 42.0 | 31.0 | -11.0 | 3 | 0 |
| DWs | 13 | 110.9 | 110.9 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.7 | 87.3 | -0.4 | 0 | 0 |
| arbiter | 6 | 83.6 | 83.8 | +0.1 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 84.3 | 84.1 | -0.2 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.1 | 29.1 | +0.0 | 2 | 3 |
| ci | 30 | 100.1 | 100.1 | -0.0 | 0 | 0 |
| collector | 1 | 2.9 | 2.6 | -0.4 | 0 | 0 |
| connect | 7 | 86.9 | 86.9 | -0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 73.5 | 73.1 | -0.4 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 8.7 | 8.0 | -0.7 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.0 | 76.0 | +0.0 | 0 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 76.5 | 71.0 | -5.5 | 2 | 0 |
| klieber | 26 | 39.1 | 38.5 | -0.6 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.7 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.5 | 97.4 | -0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.0 | 109.9 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 35.1 | 34.7 | -0.4 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 81.2 | 81.1 | -0.1 | 0 | 0 |
| robot | 1 | 2.7 | 2.5 | -0.1 | 0 | 0 |
| round | 1 | 1.9 | 2.0 | +0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 57.2 | 56.9 | -0.3 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 41.7 | 41.6 | -0.0 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| DW-unsat-10-25-1.qcir | 120.0 | 51.3 | -68.7 |
| jctc10-fail.qcir | 120.0 | 52.4 | -67.6 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 26.3 | 20.8 | -5.4 |
| DW-unsat-09-23-1.qcir | 23.6 | 19.9 | -3.7 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.4 | 9.0 | -3.5 |
| DW-unsat-09-22-1.qcir | 22.4 | 19.2 | -3.2 |
| jctc2-pass.qcir | 5.8 | 3.3 | -2.5 |
| 3.1.qcir | 54.1 | 51.9 | -2.1 |
| klieber2017q-100-25-t1.qcir | 58.8 | 56.7 | -2.1 |
| klieber2017q-086-21-t1.qcir | 59.4 | 57.7 | -1.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 29.0 | 36.2 | +7.2 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 33.8 | 38.5 | +4.7 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 13.2 | 14.8 | +1.7 |
| hadw2-7.qcir | 15.3 | 16.5 | +1.2 |
| arbiter_on_inpchange5.tlsf.qcir | 13.9 | 14.8 | +0.9 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 13.5 | 14.3 | +0.8 |
| hadw5-7.qcir | 9.9 | 10.2 | +0.3 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 0.5 | 0.6 | +0.1 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.8 | 1.9 | +0.1 |
| hadw8-9.qcir | 0.5 | 0.6 | +0.1 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

