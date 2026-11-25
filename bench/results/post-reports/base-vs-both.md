# Paired comparison: B (post-both-s1, post-both-s2, post-both-s3) against A (post-base-s1, post-base-s2, post-base-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-25T10:19:03 |
| B | `--elim --vivify ` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:08:53 |

Order in which the runs started:

- 2026-11-25T10:08:53 `post-both-s1`
- 2026-11-25T10:19:03 `post-base-s1`
- 2026-11-25T14:40:31 `post-both-s2`
- 2026-11-25T14:50:43 `post-base-s2`
- 2026-11-25T16:27:03 `post-both-s3`
- 2026-11-25T16:37:22 `post-base-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-7.50 s**, 95% bootstrap interval [-9.82, -5.36] (10000 resamples).

Sign test: B wins on 99 instances, loses on 10, ties on 267; two-sided p = 0.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 6 | 0.878 | 0 | 6 |
| 2 | 5 | 0.868 | 0 | 5 |
| 3 | 6 | 0.860 | 0 | 6 |
| all (per instance) | 7 | 0.870 | 0 | 7 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| numeric | 7 | 0.870 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.1.qcir | 0.891 | 43.18 | 38.48 |
| 1.4.qcir | 0.880 | 8.04 | 7.07 |
| 1.3.qcir | 0.877 | 8.06 | 7.07 |
| 3.2.qcir | 0.871 | 1.25 | 1.08 |
| 10.2.qcir | 0.860 | 1.64 | 1.41 |
| 10.1.qcir | 0.858 | 1.82 | 1.56 |
| 9.1.qcir | 0.852 | 2.14 | 1.82 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 9.1.qcir | 0.852 | 2.14 | 1.82 |
| 10.1.qcir | 0.858 | 1.82 | 1.56 |
| 10.2.qcir | 0.860 | 1.64 | 1.41 |
| 3.2.qcir | 0.871 | 1.25 | 1.08 |
| 1.3.qcir | 0.877 | 8.06 | 7.07 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 97/69/166 | 70.7 |
| 2 | 86/60/146 | 77.8 | 97/69/166 | 70.8 |
| 3 | 86/58/144 | 78.9 | 94/67/161 | 72.0 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.8-79.3 |
| B | 161-166 | 70.7-72.0 |

## Instances gained and lost in a majority of seeds

- gained by B (25): `5.2-2.qcir`, `CM-sat-04-01-07-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2f9n.sat.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt2nd-2x6_14.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `connect-5x5_9_connect3.ig.qcir`, `connect-6x6_9_connect3.ig.qcir`, `hadw6-8.qcir`, `jctc1-pass.qcir`, `klieber2017q-066-16-eq.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-eq.qcir`, `klieber2017q-100-25-t1.qcir`, `klieber2017q-112-28-t1.qcir`, `s-ungrounded-1x1X1x3_1.qcir`, `test_5_5_Z.pg-9.qcir`, `test_5_5_el.pg-13.qcir`, `test_5_5_knobby.pg-9.qcir`, `test_5_5_snaky.pg-9.qcir`, `test_5_5_tippy.pg-11.qcir`
- lost by B (2): `CM-sat-04-01-06-4.qcir`, `jctc10-fail.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.2 | 98.3 | +3.0 | 2 | 2 |
| DW | 7 | 30.6 | 25.9 | -4.7 | 3 | 0 |
| DWs | 13 | 117.2 | 117.0 | -0.2 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.9 | 22.2 | -57.6 | 2 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 80.4 | -20.8 | 2 | 0 |
| arbiter | 6 | 84.5 | 81.3 | -3.2 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.6 | 40.9 | -41.7 | 7 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.2 | 26.1 | -1.0 | 8 | 2 |
| ci | 30 | 100.1 | 100.3 | +0.2 | 0 | 2 |
| collector | 1 | 4.1 | 0.6 | -3.5 | 1 | 0 |
| connect | 7 | 86.9 | 66.2 | -20.7 | 3 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 73.8 | 70.9 | -2.9 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.1 | 3.0 | -7.1 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.4 | 70.7 | -5.7 | 5 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.9 | 74.7 | -1.2 | 4 | 3 |
| klieber | 26 | 48.9 | 12.0 | -36.9 | 26 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.3 | -0.5 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.1 | -0.2 | 0 | 0 |
| ltl | 5 | 98.5 | 96.7 | -1.8 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.2 | 109.3 | -1.9 | 1 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 81.1 | +1.1 | 0 | 0 |
| numeric | 26 | 31.8 | 27.6 | -4.2 | 6 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 89.3 | 72.2 | -17.1 | 2 | 0 |
| robot | 1 | 5.2 | 0.3 | -4.9 | 1 | 0 |
| round | 1 | 2.1 | 0.3 | -1.8 | 1 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 51.6 | -68.4 | 1 | 0 |
| sc | 9 | 59.1 | 55.0 | -4.1 | 4 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 47.2 | 30.1 | -17.1 | 15 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| bt2nd-3x6_10.ig.qcir | 120.0 | 13.5 | -106.5 |
| klieber2017q-084-21-eq.qcir | 120.0 | 21.0 | -99.0 |
| bt-3x4_19.ig.qcir | 120.0 | 21.0 | -99.0 |
| klieber2017q-088-22-eq.qcir | 120.0 | 21.1 | -98.9 |
| Lights2_b02056d6.tlsf.qcir | 120.0 | 22.6 | -97.4 |
| test_5_5_snaky.pg-9.qcir | 120.0 | 23.0 | -97.0 |
| hadw6-8.qcir | 120.0 | 25.5 | -94.5 |
| bt-2x5_17.ig.qcir | 120.0 | 26.3 | -93.7 |
| amba2f9n.sat.qcir | 120.0 | 29.7 | -90.3 |
| connect-5x5_9_connect3.ig.qcir | 120.0 | 34.0 | -86.0 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc10-fail.qcir | 45.7 | 120.0 | +74.3 |
| CM-sat-04-01-06-4.qcir | 43.8 | 88.8 | +45.0 |
| jctc2-pass.qcir | 81.4 | 120.0 | +38.6 |
| jctc9-pass.qcir | 82.1 | 120.0 | +37.9 |
| CM-sat-07-01-06-3.qcir | 88.1 | 120.0 | +31.9 |
| 11.1.qcir | 31.2 | 41.2 | +10.1 |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 0.8 | 4.8 | +4.0 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 10.7 | 13.4 | +2.8 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 4.5 | 6.6 | +2.1 |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | 0.7 | 2.0 | +1.3 |

## Peak memory

79 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| bt-3x6_9.ig.qcir | 15 | 42 | 2.75x |
| mult9.sat.qcir | 12 | 33 | 2.65x |
| klieber2017q-076-19-eq.qcir | 13 | 34 | 2.58x |
| eequery_query42_1344.qcir | 12 | 28 | 2.28x |
| bt2nd-2x5_10.ig.qcir | 12 | 26 | 2.23x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 12 | 26 | 2.18x |
| test_5_5_domino.pg-13.qcir | 12 | 26 | 2.12x |
| klieber2017q-108-27-t1.qcir | 12 | 25 | 2.00x |
| klieber2017q-084-21-t1.qcir | 12 | 24 | 1.97x |
| klieber2017q-070-17-eq.qcir | 12 | 24 | 1.92x |
| klieber2017q-076-19-t1.qcir | 12 | 23 | 1.88x |
| klieber2017q-064-16-t1.qcir | 12 | 23 | 1.87x |
| connect-4x4_9_connect3.ig.qcir | 12 | 22 | 1.85x |
| test_5_5_fatty.pg-9.qcir | 12 | 23 | 1.83x |
| klieber2017q-088-22-t1.qcir | 12 | 22 | 1.79x |
| klieber2017q-078-19-eq.qcir | 15 | 26 | 1.75x |
| hadw7-8.qcir | 22 | 37 | 1.72x |
| hadw6-7.qcir | 14 | 23 | 1.66x |
| amba2c7n.sat.qcir | 16 | 26 | 1.65x |
| test_5_5_tippy.pg-9.qcir | 12 | 20 | 1.65x |
| jctc13-fail.qcir | 13 | 20 | 1.48x |
| klieber2017q-072-18-eq.qcir | 12 | 18 | 1.48x |
| klieber2017q-074-18-t1.qcir | 12 | 18 | 1.46x |
| klieber2017q-074-18-eq.qcir | 12 | 18 | 1.42x |
| connect-3x3_9_connect3.ig.qcir | 12 | 17 | 1.40x |
| klieber2017q-064-16-eq.qcir | 12 | 17 | 1.39x |
| hadw8-9.qcir | 33 | 45 | 1.36x |
| klieber2017q-068-17-t1.qcir | 12 | 17 | 1.36x |
| klieber2017q-072-18-t1.qcir | 12 | 17 | 1.36x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | 43 | 57 | 1.33x |

