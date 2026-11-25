# Paired comparison: B (post-ref-dl-s1, post-ref-dl-s2, post-ref-dl-s3) against A (post-base-dl-s1, post-base-dl-s2, post-base-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-25T11:12:17 |
| B | `-dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:30:23 |

Order in which the runs started:

- 2026-11-25T10:30:23 `post-ref-dl-s1`
- 2026-11-25T11:12:17 `post-base-dl-s1`
- 2026-11-25T15:01:54 `post-ref-dl-s2`
- 2026-11-25T15:43:44 `post-base-dl-s2`
- 2026-11-25T16:48:49 `post-ref-dl-s3`
- 2026-11-25T17:30:53 `post-base-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-2.49 s**, 95% bootstrap interval [-3.83, -1.27] (10000 resamples).

Sign test: B wins on 76 instances, loses on 21, ties on 279; two-sided p = 0.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 6 | 0.822 | 0 | 6 |
| 2 | 9 | 0.891 | 2 | 7 |
| 3 | 7 | 0.799 | 0 | 7 |
| all (per instance) | 9 | 0.855 | 1 | 8 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| chess | 2 | 0.847 |  |
| numeric | 7 | 0.857 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 8.1.qcir | 1.043 | 3.91 | 4.08 |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 0.877 | 1.72 | 1.54 |
| 1.3.qcir | 0.864 | 11.36 | 9.82 |
| 1.4.qcir | 0.863 | 11.44 | 9.88 |
| 10.2.qcir | 0.842 | 3.24 | 2.78 |
| 10.1.qcir | 0.836 | 2.84 | 2.39 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 0.817 | 1.62 | 1.32 |
| 3.2.qcir | 0.804 | 2.16 | 1.75 |
| 9.1.qcir | 0.772 | 2.23 | 1.72 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 9.1.qcir | 0.772 | 2.23 | 1.72 |
| 3.2.qcir | 0.804 | 2.16 | 1.75 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 0.817 | 1.62 | 1.32 |
| 10.1.qcir | 0.836 | 2.84 | 2.39 |
| 10.2.qcir | 0.842 | 3.24 | 2.78 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.3 | 85/69/154 | 74.6 |
| 2 | 86/67/153 | 75.6 | 92/69/161 | 73.3 |
| 3 | 84/62/146 | 77.7 | 89/69/158 | 74.2 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.6-77.7 |
| B | 154-161 | 73.3-74.6 |

## Instances gained and lost in a majority of seeds

- gained by B (10): `3.1.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `DWs-unsat-08-17-1.qcir`, `bt-2x5_17.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `hadw11-12.qcir`, `hadw7-9.qcir`, `jctc1-pass.qcir`
- lost by B (1): `test_5_5_domino.pg-15.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.1 | 79.7 | -17.4 | 2 | 1 |
| DW | 7 | 21.1 | 11.8 | -9.3 | 5 | 0 |
| DWs | 13 | 117.8 | 114.0 | -3.8 | 1 | 0 |
| JP | 6 | 109.9 | 109.3 | -0.6 | 0 | 0 |
| Lights | 2 | 51.4 | 53.7 | +2.2 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 105.4 | -2.4 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 86.9 | 83.9 | -3.0 | 2 | 0 |
| arbiter | 6 | 84.0 | 84.3 | +0.3 | 1 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.7 | 66.8 | -13.9 | 5 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.7 | 60.8 | -0.9 | 7 | 2 |
| ci | 30 | 88.6 | 87.4 | -1.2 | 3 | 0 |
| collector | 1 | 3.7 | 3.5 | -0.2 | 0 | 0 |
| connect | 7 | 88.3 | 86.6 | -1.7 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.0 | 65.0 | -4.0 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 6.5 | 7.3 | +0.7 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.2 | 70.2 | -7.9 | 7 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.9 | 35.7 | -2.2 | 5 | 4 |
| klieber | 26 | 17.1 | 14.0 | -3.1 | 16 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.1 | 60.7 | -0.3 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.9 | 98.2 | -0.7 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.0 | 111.4 | +0.4 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 36.8 | 35.8 | -1.0 | 4 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 69.7 | -3.2 | 1 | 0 |
| robot | 1 | 4.3 | 3.2 | -1.1 | 1 | 0 |
| round | 1 | 1.4 | 1.0 | -0.4 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 57.0 | 55.8 | -1.3 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 33.5 | -4.6 | 9 | 2 |
| voter | 2 | 102.2 | 120.0 | +17.8 | 0 | 1 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 90.3 | 5.4 | -84.9 |
| jctc1-pass.qcir | 80.0 | 1.3 | -78.7 |
| bt2nd-3x4_12.ig.qcir | 120.0 | 54.0 | -66.0 |
| hadw11-12.qcir | 95.8 | 35.6 | -60.2 |
| test_5_5_fatty.pg-9.qcir | 73.5 | 20.3 | -53.2 |
| bt2nd-3x6_10.ig.qcir | 90.4 | 38.8 | -51.6 |
| hadw7-9.qcir | 120.0 | 69.2 | -50.8 |
| DWs-unsat-08-17-1.qcir | 91.1 | 42.3 | -48.8 |
| DW-unsat-11-26-1.qcir | 70.0 | 22.7 | -47.3 |
| klieber2017q-084-21-eq.qcir | 67.7 | 21.9 | -45.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc2-pass.qcir | 4.8 | 53.3 | +48.5 |
| test_5_5_domino.pg-15.qcir | 51.8 | 99.2 | +47.5 |
| jctc8-pass.qcir | 1.3 | 40.1 | +38.8 |
| voter_size_202219_1U43.qcir | 84.4 | 120.0 | +35.6 |
| 5.2-2.qcir | 89.2 | 120.0 | +30.8 |
| jctc14-unrolled-fail.qcir | 96.2 | 120.0 | +23.8 |
| klieber2017q-112-28-t1.qcir | 20.6 | 42.0 | +21.5 |
| klieber2017q-074-18-t1.qcir | 5.8 | 21.4 | +15.5 |
| Lights2_b02056d6.tlsf.qcir | 26.4 | 35.8 | +9.5 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 4.5 | 11.6 | +7.1 |

## Peak memory

38 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| klieber2017q-076-19-eq.qcir | 13 | 46 | 3.51x |
| klieber2017q-078-19-eq.qcir | 12 | 39 | 3.17x |
| bt-3x6_9.ig.qcir | 15 | 46 | 3.14x |
| mult9.sat.qcir | 15 | 44 | 2.99x |
| klieber2017q-108-27-t1.qcir | 12 | 30 | 2.46x |
| connect-4x4_9_connect3.ig.qcir | 12 | 29 | 2.40x |
| bt2nd-2x5_10.ig.qcir | 12 | 28 | 2.34x |
| test_5_5_tippy.pg-9.qcir | 12 | 28 | 2.30x |
| klieber2017q-072-18-eq.qcir | 12 | 27 | 2.21x |
| klieber2017q-074-18-t1.qcir | 12 | 26 | 2.12x |
| klieber2017q-074-18-eq.qcir | 12 | 26 | 2.09x |
| klieber2017q-070-17-eq.qcir | 12 | 24 | 1.94x |
| klieber2017q-082-20-t1.qcir | 12 | 24 | 1.94x |
| test_5_5_knobby.pg-9.qcir | 12 | 24 | 1.93x |
| klieber2017q-066-16-eq.qcir | 12 | 24 | 1.91x |
| klieber2017q-086-21-t1.qcir | 12 | 24 | 1.91x |
| jctc13-fail.qcir | 17 | 32 | 1.86x |
| test_5_5_domino.pg-13.qcir | 12 | 22 | 1.76x |
| eequery_query42_1344.qcir | 12 | 19 | 1.59x |
| klieber2017q-084-21-t1.qcir | 12 | 19 | 1.54x |
| klieber2017q-064-16-eq.qcir | 12 | 19 | 1.51x |
| klieber2017q-076-19-t1.qcir | 12 | 19 | 1.51x |
| klieber2017q-100-25-t1.qcir | 12 | 18 | 1.42x |
| connect-3x3_9_connect3.ig.qcir | 12 | 17 | 1.41x |
| klieber2017q-072-18-t1.qcir | 12 | 17 | 1.39x |
| klieber2017q-080-20-t1.qcir | 12 | 17 | 1.39x |
| klieber2017q-064-16-t1.qcir | 12 | 16 | 1.33x |
| klieber2017q-070-17-t1.qcir | 12 | 16 | 1.33x |
| klieber2017q-068-17-eq.qcir | 12 | 16 | 1.30x |
| klieber2017q-068-17-t1.qcir | 12 | 16 | 1.30x |

