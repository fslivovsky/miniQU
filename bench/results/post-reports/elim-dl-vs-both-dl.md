# Paired comparison: B (post-both-dl-s1, post-both-dl-s2, post-both-dl-s3) against A (post-elim-dl-s1, post-elim-dl-s2, post-elim-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `--elim -dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:41:01 |
| B | `--elim --vivify -dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T11:02:01 |

Order in which the runs started:

- 2026-11-25T10:41:01 `post-elim-dl-s1`
- 2026-11-25T11:02:01 `post-both-dl-s1`
- 2026-11-25T15:12:32 `post-elim-dl-s2`
- 2026-11-25T15:33:24 `post-both-dl-s2`
- 2026-11-25T16:59:29 `post-elim-dl-s3`
- 2026-11-25T17:20:31 `post-both-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.59 s**, 95% bootstrap interval [-1.35, +0.10] (10000 resamples).

Sign test: B wins on 47 instances, loses on 24, ties on 305; two-sided p = 0.0086 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 12 | 0.994 | 7 | 5 |
| 2 | 8 | 0.999 | 2 | 6 |
| 3 | 9 | 0.996 | 8 | 1 |
| all (per instance) | 13 | 0.989 | 8 | 5 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| chess | 4 | 0.962 |  |
| numeric | 9 | 1.001 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 1.081 | 1.27 | 1.37 |
| 10.1.qcir | 1.007 | 2.52 | 2.54 |
| 10.2.qcir | 1.004 | 3.00 | 3.01 |
| 1.3.qcir | 1.004 | 10.39 | 10.43 |
| 1.4.qcir | 1.002 | 10.47 | 10.50 |
| 8.1.qcir | 1.002 | 4.41 | 4.42 |
| 9.1.qcir | 1.001 | 1.97 | 1.98 |
| 9.3.qcir | 1.000 | 2.50 | 2.50 |
| 11.1.qcir | 0.998 | 34.56 | 34.48 |
| 3.2.qcir | 0.995 | 1.68 | 1.68 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.941 | 1.30 | 1.23 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 0.924 | 1.53 | 1.42 |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 0.910 | 1.13 | 1.03 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 0.910 | 1.13 | 1.03 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 0.924 | 1.53 | 1.42 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.941 | 1.30 | 1.23 |
| 3.2.qcir | 0.995 | 1.68 | 1.68 |
| 11.1.qcir | 0.998 | 34.56 | 34.48 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 89/69/158 | 72.8 | 92/72/164 | 71.3 |
| 2 | 89/71/160 | 72.1 | 91/72/163 | 71.7 |
| 3 | 92/70/162 | 71.9 | 91/71/162 | 72.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 158-162 | 71.9-72.8 |
| B | 162-164 | 71.3-72.1 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `connect-5x5_9_connect3.ig.qcir`, `test_5_5_tippy.pg-11.qcir`
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 83.5 | 80.3 | -3.1 | 2 | 1 |
| DW | 7 | 10.1 | 8.5 | -1.6 | 3 | 1 |
| DWs | 13 | 111.4 | 107.4 | -4.0 | 3 | 0 |
| JP | 6 | 107.9 | 104.1 | -3.8 | 1 | 0 |
| Lights | 2 | 19.0 | 17.6 | -1.3 | 1 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 102.9 | 102.2 | -0.7 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 79.4 | 79.3 | -0.0 | 0 | 0 |
| arbiter | 6 | 81.2 | 81.2 | -0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 53.1 | 54.1 | +0.9 | 1 | 3 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 56.6 | 56.9 | +0.2 | 6 | 3 |
| ci | 30 | 88.1 | 88.3 | +0.2 | 0 | 1 |
| collector | 1 | 0.5 | 0.5 | +0.0 | 0 | 0 |
| connect | 7 | 83.7 | 74.5 | -9.2 | 3 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.4 | 64.1 | -0.3 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 2.7 | 2.7 | -0.0 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 73.1 | 70.4 | -2.7 | 4 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 33.5 | 40.3 | +6.8 | 1 | 3 |
| klieber | 26 | 7.4 | 8.0 | +0.6 | 10 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.3 | 60.3 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.1 | 96.1 | -0.0 | 0 | 0 |
| ltl | 5 | 96.7 | 96.6 | -0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 109.5 | 109.5 | -0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.2 | 80.2 | +0.1 | 0 | 0 |
| numeric | 26 | 37.5 | 38.6 | +1.1 | 0 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 71.2 | 67.8 | -3.4 | 1 | 0 |
| robot | 1 | 0.2 | 0.2 | +0.0 | 0 | 0 |
| round | 1 | 0.4 | 0.4 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 99.4 | -20.6 | 1 | 0 |
| sc | 9 | 55.2 | 54.9 | -0.3 | 1 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 31.5 | 28.5 | -3.0 | 7 | 3 |
| voter | 2 | 120.0 | 106.9 | -13.1 | 1 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_tippy.pg-11.qcir | 120.0 | 65.9 | -54.1 |
| CM-sat-04-01-06-3.qcir | 59.4 | 19.6 | -39.8 |
| connect-5x5_9_connect3.ig.qcir | 99.9 | 63.8 | -36.1 |
| hadw11-12.qcir | 75.4 | 42.7 | -32.7 |
| DWs-sat-10-25-1.qcir | 120.0 | 88.7 | -31.3 |
| connect-6x6_9_connect3.ig.qcir | 120.0 | 93.6 | -26.4 |
| voter_size_202219_1U43.qcir | 120.0 | 93.8 | -26.2 |
| JP-unsat-02-06-3.qcir | 47.5 | 24.6 | -22.9 |
| jctc14-unrolled-fail.qcir | 120.0 | 97.3 | -22.7 |
| DWs-sat-10-23-1.qcir | 120.0 | 97.6 | -22.4 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc8-pass.qcir | 0.2 | 40.1 | +39.9 |
| jctc4-fail.qcir | 5.8 | 41.4 | +35.5 |
| jctc1-pass.qcir | 5.5 | 40.6 | +35.1 |
| 11.1.qcir | 39.4 | 62.9 | +23.5 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 97.2 | 120.0 | +22.8 |
| CM-sat-07-01-07-3.qcir | 99.9 | 120.0 | +20.1 |
| bt2nd-3x6_10.ig.qcir | 17.3 | 31.8 | +14.6 |
| test_5_5_domino.pg-15.qcir | 88.6 | 98.8 | +10.1 |
| klieber2017q-108-27-t1.qcir | 8.2 | 17.3 | +9.1 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 26.2 | 34.4 | +8.2 |

## Peak memory

13 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| klieber2017q-064-16-eq.qcir | 13 | 22 | 1.73x |
| klieber2017q-082-20-t1.qcir | 18 | 27 | 1.54x |
| klieber2017q-112-28-t1.qcir | 28 | 41 | 1.48x |
| jctc9-pass.qcir | 37 | 52 | 1.41x |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 12 | 16 | 1.32x |
| eequery_query42_1344.qcir | 19 | 25 | 1.31x |
| sc-ungrounded-2x2X2x2_1.qcir | 137 | 176 | 1.29x |
| klieber2017q-088-22-eq.qcir | 38 | 45 | 1.20x |
| test_5_5_domino.pg-13.qcir | 19 | 23 | 1.17x |
| klieber2017q-068-17-eq.qcir | 14 | 16 | 1.13x |
| test_5_5_tippy.pg-9.qcir | 13 | 14 | 1.12x |
| hadw8-9.qcir | 58 | 64 | 1.10x |
| klieber2017q-070-17-eq.qcir | 24 | 26 | 1.10x |

