# Paired comparison: B (M1-r2-dl-s1, M1-r2-dl-s2, M1-r2-dl-s3) against A (baseline-c96-dl-t60-s1, baseline-c96-dl-t60-s2, baseline-c96-dl-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-23T01:28:03 |
| B | `-dl` | 25216c2 | 30bd8fe6b956 | 2026-11-23T13:58:44 |

Order in which the runs started:

- 2026-11-23T01:28:03 `baseline-c96-dl-t60-s1`
- 2026-11-23T01:51:49 `baseline-c96-dl-t60-s2`
- 2026-11-23T02:15:46 `baseline-c96-dl-t60-s3`
- 2026-11-23T13:58:44 `M1-r2-dl-s1`
- 2026-11-23T14:04:39 `M1-r2-dl-s2`
- 2026-11-23T14:10:31 `M1-r2-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.05 s**, 95% bootstrap interval [-0.68, +0.76] (10000 resamples).

Sign test: B wins on 36 instances, loses on 30, ties on 310; two-sided p = 0.5386 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 40 | 1.007 | 16 | 24 |
| 2 | 42 | 0.990 | 14 | 28 |
| 3 | 30 | 0.995 | 10 | 20 |
| all (per instance) | 50 | 1.001 | 23 | 27 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 4 | 1.107 | > 1.10 |
| Lights | 1 | 1.221 |  |
| chess | 18 | 1.008 |  |
| collector | 1 | 1.018 |  |
| finding | 1 | 1.173 |  |
| hadw | 4 | 0.963 |  |
| jctc | 3 | 0.966 |  |
| lift | 1 | 0.968 |  |
| ltl | 1 | 1.016 |  |
| numeric | 14 | 0.957 |  |
| round | 1 | 1.018 |  |
| voter | 1 | 0.980 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.343 | 10.04 | 13.49 |
| Lights2_b02056d6.tlsf.qcir | 1.221 | 24.76 | 29.39 |
| 5.2-1.qcir | 1.200 | 25.35 | 30.25 |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 1.197 | 3.30 | 4.07 |
| chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir | 1.174 | 1.35 | 1.62 |
| finding_nemo_1.tlsf.qcir | 1.173 | 7.79 | 9.06 |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 1.169 | 4.46 | 4.44 |
| jctc17-vals-0,2-pass.qcir | 1.167 | 11.54 | 15.15 |
| DW-unsat-09-22-1.qcir | 1.146 | 2.65 | 3.04 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.071 | 4.06 | 4.70 |
| hadw11-12.qcir | 1.060 | 51.69 | 54.80 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.056 | 10.94 | 11.56 |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 1.055 | 6.59 | 6.63 |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 1.051 | 4.52 | 4.63 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 1.047 | 5.67 | 6.13 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 0.764 | 8.51 | 6.36 |
| 9.1.qcir | 0.796 | 2.22 | 1.77 |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | 0.799 | 4.89 | 3.91 |
| 3.2.qcir | 0.847 | 2.16 | 1.84 |
| jctc4-fail.qcir | 0.849 | 4.25 | 3.61 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.4 | 84/65/149 | 76.6 |
| 2 | 86/67/153 | 75.7 | 86/65/151 | 76.0 |
| 3 | 84/62/146 | 77.7 | 83/63/146 | 77.4 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.7-77.7 |
| B | 146-151 | 76.0-77.4 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `CM-sat-04-01-06-3.qcir`
- lost by B (1): `Lights2_0f5381e9.tlsf.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.2 | 88.9 | -8.3 | 2 | 2 |
| DW | 7 | 21.4 | 18.4 | -3.0 | 3 | 0 |
| DWs | 13 | 117.8 | 120.0 | +2.2 | 0 | 1 |
| JP | 6 | 109.9 | 109.1 | -0.8 | 0 | 0 |
| Lights | 2 | 50.2 | 74.7 | +24.5 | 0 | 2 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 104.2 | -3.5 | 1 | 1 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.2 | 91.1 | +3.9 | 1 | 1 |
| arbiter | 6 | 84.2 | 84.6 | +0.4 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.8 | 83.6 | +2.8 | 1 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.8 | 61.5 | -0.4 | 5 | 4 |
| ci | 30 | 88.6 | 88.6 | -0.0 | 1 | 1 |
| collector | 1 | 4.3 | 4.3 | +0.0 | 0 | 0 |
| connect | 7 | 88.4 | 87.6 | -0.8 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.5 | 69.9 | +0.5 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.8 | 9.1 | +1.3 | 0 | 1 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.7 | 78.4 | -0.3 | 1 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.4 | 39.7 | +2.3 | 2 | 2 |
| klieber | 26 | 17.3 | 16.0 | -1.3 | 11 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.1 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.2 | 99.2 | +0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.1 | 111.6 | +0.5 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | -0.0 | 0 | 0 |
| numeric | 26 | 36.8 | 37.6 | +0.8 | 0 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 79.8 | +6.9 | 0 | 1 |
| robot | 1 | 4.4 | 3.3 | -1.1 | 1 | 0 |
| round | 1 | 1.4 | 1.3 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.7 | 56.2 | -0.6 | 2 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 37.3 | -0.9 | 4 | 2 |
| voter | 2 | 102.1 | 102.1 | -0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 90.4 | 24.6 | -65.8 |
| klieber2017q-084-21-eq.qcir | 68.4 | 26.7 | -41.6 |
| jctc10-fail.qcir | 120.0 | 89.1 | -30.9 |
| SR-sat-02-01-06-3.qcir | 120.0 | 90.3 | -29.7 |
| test_5_5_fatty.pg-9.qcir | 73.9 | 47.5 | -26.4 |
| CM-sat-07-01-07-3.qcir | 120.0 | 97.4 | -22.6 |
| DW-unsat-11-26-1.qcir | 72.9 | 56.2 | -16.7 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 57.5 | 40.9 | -16.6 |
| klieber2017q-086-21-t1.qcir | 18.6 | 9.4 | -9.3 |
| test_5_5_knobby.pg-9.qcir | 26.3 | 18.1 | -8.1 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_0f5381e9.tlsf.qcir | 75.5 | 120.0 | +44.5 |
| jctc4-fail.qcir | 9.9 | 41.3 | +31.4 |
| bt2nd-3x6_10.ig.qcir | 90.8 | 120.0 | +29.2 |
| DWs-unsat-08-17-1.qcir | 91.7 | 120.0 | +28.3 |
| klieber2017q-088-22-eq.qcir | 62.7 | 90.9 | +28.2 |
| jctc14-unrolled-fail.qcir | 92.4 | 120.0 | +27.6 |
| 5.2-1.qcir | 35.5 | 60.2 | +24.7 |
| CM-sat-04-01-06-4.qcir | 96.5 | 120.0 | +23.5 |
| amba2f9n.sat.qcir | 53.5 | 75.6 | +22.1 |
| reachqu_query64_1344.qcir | 17.6 | 32.7 | +15.1 |

## Peak memory

5 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc6-pass.qcir | 64 | 121 | 1.89x |
| jctc13-fail.qcir | 17 | 26 | 1.54x |
| CM-sat-04-01-07-3.qcir | 480 | 577 | 1.20x |
| jctc8-pass.qcir | 49 | 58 | 1.18x |
| bt-3x6_9.ig.qcir | 14 | 16 | 1.16x |

