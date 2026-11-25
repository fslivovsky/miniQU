# Paired comparison: B (post-both-s1, post-both-s2, post-both-s3) against A (post-elim-s1, post-elim-s2, post-elim-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `--elim ` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T09:47:20 |
| B | `--elim --vivify ` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:08:53 |

Order in which the runs started:

- 2026-11-25T09:47:20 `post-elim-s1`
- 2026-11-25T10:08:53 `post-both-s1`
- 2026-11-25T14:19:15 `post-elim-s2`
- 2026-11-25T14:40:31 `post-both-s2`
- 2026-11-25T16:05:40 `post-elim-s3`
- 2026-11-25T16:27:03 `post-both-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.72 s**, 95% bootstrap interval [-1.37, -0.13] (10000 resamples).

Sign test: B wins on 28 instances, loses on 26, ties on 322; two-sided p = 0.8919 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 12 | 1.025 | 11 | 1 |
| 2 | 10 | 1.041 | 7 | 2 |
| 3 | 9 | 0.978 | 5 | 4 |
| all (per instance) | 14 | 1.034 | 12 | 2 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 2 | 1.254 |  |
| DWs | 1 | 1.199 |  |
| chess | 1 | 0.812 |  |
| numeric | 10 | 1.004 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-sat-08-23-1.qcir | 1.435 | 1.22 | 1.75 |
| DWs-sat-10-25-1.qcir | 1.199 | 3.81 | 4.56 |
| DW-sat-09-26-1.qcir | 1.095 | 3.01 | 3.29 |
| 11.1.qcir | 1.020 | 32.87 | 33.52 |
| 9.3.qcir | 1.013 | 1.71 | 1.73 |
| 3.2.qcir | 1.012 | 1.13 | 1.14 |
| 9.1.qcir | 1.010 | 1.80 | 1.82 |
| 10.1.qcir | 1.009 | 1.65 | 1.67 |
| 10.2.qcir | 1.007 | 1.72 | 1.73 |
| 1.3.qcir | 1.006 | 7.02 | 7.07 |
| 1.4.qcir | 1.004 | 7.05 | 7.07 |
| 8.1.qcir | 1.004 | 3.94 | 3.96 |
| 3.1.qcir | 0.960 | 36.49 | 34.82 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.812 | 1.13 | 0.92 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.812 | 1.13 | 0.92 |
| 3.1.qcir | 0.960 | 36.49 | 34.82 |
| 8.1.qcir | 1.004 | 3.94 | 3.96 |
| 1.4.qcir | 1.004 | 7.05 | 7.07 |
| 1.3.qcir | 1.006 | 7.02 | 7.07 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 94/67/161 | 72.2 | 97/69/166 | 70.7 |
| 2 | 98/68/166 | 70.8 | 97/69/166 | 70.8 |
| 3 | 92/67/159 | 72.7 | 94/67/161 | 72.0 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 159-166 | 70.8-72.7 |
| B | 161-166 | 70.7-72.0 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `test_5_5_Z.pg-9.qcir`
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 113.3 | 98.3 | -15.1 | 3 | 0 |
| DW | 7 | 32.1 | 25.9 | -6.1 | 4 | 1 |
| DWs | 13 | 117.0 | 117.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 22.8 | 22.2 | -0.6 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 80.4 | 80.4 | +0.0 | 0 | 0 |
| arbiter | 6 | 81.2 | 81.3 | +0.1 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 41.0 | 40.9 | -0.1 | 1 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 26.4 | 26.1 | -0.2 | 2 | 5 |
| ci | 30 | 100.3 | 100.3 | +0.1 | 0 | 1 |
| collector | 1 | 0.6 | 0.6 | -0.0 | 0 | 0 |
| connect | 7 | 68.0 | 66.2 | -1.8 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.9 | 70.9 | +0.9 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 2.8 | 3.0 | +0.2 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.5 | 70.7 | +0.2 | 0 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 71.4 | 74.7 | +3.3 | 0 | 2 |
| klieber | 26 | 10.5 | 12.0 | +1.5 | 6 | 12 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.3 | 60.3 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.1 | 96.1 | -0.0 | 0 | 0 |
| ltl | 5 | 96.9 | 96.7 | -0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 109.3 | 109.3 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.6 | 81.1 | +0.5 | 0 | 0 |
| numeric | 26 | 28.6 | 27.6 | -1.0 | 2 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 87.7 | 72.2 | -15.5 | 2 | 0 |
| robot | 1 | 0.3 | 0.3 | -0.0 | 0 | 0 |
| round | 1 | 0.4 | 0.3 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 78.7 | 51.6 | -27.1 | 1 | 0 |
| sc | 9 | 55.1 | 55.0 | -0.2 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 33.1 | 30.1 | -3.0 | 5 | 2 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_Z.pg-9.qcir | 120.0 | 74.7 | -45.3 |
| CM-sat-04-01-07-3.qcir | 98.2 | 55.6 | -42.6 |
| DW-unsat-10-25-1.qcir | 69.6 | 32.9 | -36.8 |
| reachqu_query60_1344.qcir | 120.0 | 84.3 | -35.7 |
| CM-sat-04-01-06-3.qcir | 94.9 | 63.3 | -31.6 |
| CM-sat-04-01-06-4.qcir | 120.0 | 88.8 | -31.2 |
| s-ungrounded-1x1X1x3_1.qcir | 78.7 | 51.6 | -27.1 |
| test_5_5_tippy.pg-11.qcir | 96.4 | 70.7 | -25.7 |
| 5.2-2.qcir | 96.8 | 76.6 | -20.2 |
| klieber2017q-088-22-t1.qcir | 21.9 | 7.0 | -14.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-112-28-t1.qcir | 27.1 | 67.0 | +39.9 |
| jctc9-pass.qcir | 97.6 | 120.0 | +22.4 |
| jctc2-pass.qcir | 98.7 | 120.0 | +21.3 |
| klieber2017q-084-21-t1.qcir | 3.8 | 9.1 | +5.4 |
| klieber2017q-064-16-t1.qcir | 7.0 | 11.5 | +4.5 |
| Lights2_b02056d6.tlsf.qcir | 18.4 | 22.6 | +4.3 |
| klieber2017q-084-21-eq.qcir | 17.1 | 21.0 | +3.9 |
| 11.1.qcir | 37.5 | 41.2 | +3.7 |
| hadw6-8.qcir | 21.8 | 25.5 | +3.7 |
| klieber2017q-078-19-eq.qcir | 10.1 | 13.3 | +3.2 |

## Peak memory

15 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| klieber2017q-084-21-t1.qcir | 17 | 24 | 1.45x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 19 | 26 | 1.40x |
| klieber2017q-064-16-t1.qcir | 17 | 23 | 1.38x |
| klieber2017q-070-17-eq.qcir | 17 | 24 | 1.38x |
| bt2nd-2x5_10.ig.qcir | 20 | 26 | 1.32x |
| klieber2017q-076-19-t1.qcir | 18 | 23 | 1.32x |
| test_5_5_tippy.pg-9.qcir | 16 | 20 | 1.31x |
| test_5_5_knobby.pg-9.qcir | 24 | 31 | 1.26x |
| klieber2017q-078-19-t1.qcir | 19 | 23 | 1.25x |
| klieber2017q-082-20-t1.qcir | 13 | 16 | 1.23x |
| test_5_5_domino.pg-13.qcir | 22 | 26 | 1.20x |
| bt2nd-3x6_10.ig.qcir | 44 | 51 | 1.14x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | 12 | 14 | 1.14x |
| bt2nd-2x6_14.ig.qcir | 86 | 98 | 1.13x |
| amba2c7n.sat.qcir | 23 | 26 | 1.11x |

