# Paired comparison: B (M1-r3-default-s1, M1-r3-default-s2, M1-r3-default-s3) against A (baseline-c96-default-t60-s1, baseline-c96-default-t60-s2, baseline-c96-default-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-23T01:16:03 |
| B | `` | 46874d9 | 006221175f2f | 2026-11-23T20:12:40 |

Order in which the runs started:

- 2026-11-23T01:16:03 `baseline-c96-default-t60-s1`
- 2026-11-23T01:39:53 `baseline-c96-default-t60-s2`
- 2026-11-23T02:03:45 `baseline-c96-default-t60-s3`
- 2026-11-23T20:12:40 `M1-r3-default-s1`
- 2026-11-23T20:18:43 `M1-r3-default-s2`
- 2026-11-23T20:24:43 `M1-r3-default-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.00 s**, 95% bootstrap interval [-0.77, +0.80] (10000 resamples).

Sign test: B wins on 36 instances, loses on 18, ties on 322; two-sided p = 0.0198 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 41 | 0.991 | 18 | 23 |
| 2 | 40 | 0.965 | 20 | 20 |
| 3 | 37 | 0.891 | 13 | 24 |
| all (per instance) | 51 | 0.964 | 22 | 29 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.859 |  |
| DW | 6 | 0.855 |  |
| DWs | 1 | 1.003 |  |
| Lights | 1 | 1.017 |  |
| chess | 16 | 0.975 |  |
| collector | 1 | 0.902 |  |
| finding | 1 | 0.926 |  |
| hadw | 3 | 0.921 |  |
| jctc | 4 | 1.330 | > 1.10 |
| lift | 1 | 0.906 |  |
| ltl | 1 | 0.930 |  |
| numeric | 15 | 0.941 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 2.007 | 2.05 | 4.12 |
| jctc10-fail.qcir | 1.670 | 6.18 | 10.27 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.156 | 8.43 | 9.77 |
| 5.1-1.qcir | 1.153 | 40.74 | 47.06 |
| 5.2-1.qcir | 1.149 | 31.70 | 35.85 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 1.144 | 9.56 | 10.94 |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | 1.123 | 1.08 | 1.21 |
| 4.1.qcir | 1.094 | 6.67 | 7.27 |
| 9.2.qcir | 1.071 | 18.38 | 19.71 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.067 | 3.78 | 4.03 |
| DW-unsat-09-22-1.qcir | 1.063 | 15.38 | 15.84 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.061 | 1.13 | 1.19 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.060 | 1.26 | 1.32 |
| 11.1.qcir | 1.037 | 31.68 | 32.95 |
| jctc17-vals-0,2-pass.qcir | 1.036 | 12.14 | 12.58 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.577 | 2.93 | 1.69 |
| DW-sat-08-22-1.qcir | 0.691 | 2.54 | 1.71 |
| 3.2.qcir | 0.737 | 1.26 | 0.93 |
| DW-unsat-09-23-1.qcir | 0.749 | 26.02 | 21.93 |
| 9.1.qcir | 0.753 | 2.16 | 1.63 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 83/59/142 | 79.7 |
| 2 | 86/60/146 | 77.9 | 86/59/145 | 78.0 |
| 3 | 85/58/143 | 79.1 | 83/60/143 | 78.7 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.9-79.3 |
| B | 142-145 | 78.0-79.7 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `test_5_5_knobby.pg-9.qcir`
- lost by B (2): `klieber2017q-076-19-eq.qcir`, `klieber2017q-108-27-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.1 | 105.6 | +10.4 | 1 | 3 |
| DW | 7 | 31.8 | 30.8 | -1.0 | 2 | 0 |
| DWs | 13 | 117.3 | 117.3 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.8 | 80.4 | +0.6 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 100.8 | -0.4 | 0 | 0 |
| arbiter | 6 | 84.8 | 84.5 | -0.3 | 1 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.7 | 77.6 | -5.2 | 3 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.3 | 27.5 | +0.2 | 1 | 4 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 1 |
| collector | 1 | 4.4 | 4.0 | -0.4 | 0 | 0 |
| connect | 7 | 86.9 | 86.8 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 74.7 | 79.2 | +4.5 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.3 | 9.6 | -0.8 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.5 | 76.0 | -0.5 | 2 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.7 | 75.9 | +0.1 | 0 | 0 |
| klieber | 26 | 49.9 | 52.6 | +2.7 | 14 | 6 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.7 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.6 | 98.5 | -0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.3 | 111.9 | +0.7 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 32.1 | +0.3 | 2 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 88.9 | 88.1 | -0.8 | 0 | 0 |
| robot | 1 | 5.2 | 3.9 | -1.3 | 1 | 0 |
| round | 1 | 2.0 | 1.8 | -0.2 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 59.0 | 57.5 | -1.5 | 3 | 0 |
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
| test_5_5_knobby.pg-9.qcir | 90.6 | 41.5 | -49.1 |
| CM-sat-04-01-06-3.qcir | 90.4 | 58.6 | -31.8 |
| klieber2017q-112-28-t1.qcir | 120.0 | 89.9 | -30.1 |
| klieber2017q-084-21-eq.qcir | 120.0 | 92.3 | -27.7 |
| klieber2017q-100-25-t1.qcir | 93.7 | 71.2 | -22.4 |
| bt2nd-3x4_12.ig.qcir | 97.7 | 75.4 | -22.3 |
| Lights2_0f5381e9.tlsf.qcir | 61.6 | 40.8 | -20.8 |
| bt2nd-3x6_10.ig.qcir | 120.0 | 99.6 | -20.4 |
| bt-2x5_17.ig.qcir | 120.0 | 99.8 | -20.2 |
| klieber2017q-068-17-t1.qcir | 40.2 | 26.4 | -13.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-088-22-t1.qcir | 10.2 | 71.7 | +61.5 |
| klieber2017q-108-27-t1.qcir | 35.4 | 84.6 | +49.2 |
| klieber2017q-076-19-t1.qcir | 29.2 | 72.3 | +43.1 |
| klieber2017q-076-19-eq.qcir | 51.4 | 92.3 | +40.9 |
| CM-sat-04-01-06-4.qcir | 43.8 | 80.3 | +36.5 |
| CM-sat-04-01-07-3.qcir | 84.4 | 120.0 | +35.6 |
| CM-sat-07-01-06-3.qcir | 87.2 | 120.0 | +32.8 |
| Lights2_b02056d6.tlsf.qcir | 97.9 | 120.0 | +22.1 |
| klieber2017q-078-19-eq.qcir | 48.1 | 68.7 | +20.6 |
| eequery_query42_1344.qcir | 29.3 | 38.3 | +9.0 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-1x3X3x2_1.qcir | 26 | 34 | 1.32x |
| bt-3x6_9.ig.qcir | 15 | 17 | 1.14x |
| sc-ungrounded-2x1X1x2_2.qcir | 47 | 53 | 1.13x |

