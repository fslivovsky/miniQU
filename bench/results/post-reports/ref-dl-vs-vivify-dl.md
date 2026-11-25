# Paired comparison: B (post-vivify-dl-s1, post-vivify-dl-s2, post-vivify-dl-s3) against A (post-ref-dl-s1, post-ref-dl-s2, post-ref-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:30:23 |
| B | `--vivify -dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:51:22 |

Order in which the runs started:

- 2026-11-25T10:30:23 `post-ref-dl-s1`
- 2026-11-25T10:51:22 `post-vivify-dl-s1`
- 2026-11-25T15:01:54 `post-ref-dl-s2`
- 2026-11-25T15:22:48 `post-vivify-dl-s2`
- 2026-11-25T16:48:49 `post-ref-dl-s3`
- 2026-11-25T17:09:49 `post-vivify-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.04 s**, 95% bootstrap interval [-0.75, +0.87] (10000 resamples).

Sign test: B wins on 42 instances, loses on 34, ties on 300; two-sided p = 0.4222 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 10 | 0.969 | 6 | 4 |
| 2 | 14 | 0.972 | 4 | 10 |
| 3 | 14 | 1.061 | 11 | 3 |
| all (per instance) | 18 | 1.009 | 9 | 9 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| chess | 8 | 1.024 |  |
| numeric | 10 | 0.997 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | 1.447 | 1.51 | 2.19 |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 1.218 | 1.28 | 1.56 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 1.085 | 1.32 | 1.44 |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | 1.047 | 1.68 | 1.76 |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 1.039 | 1.54 | 1.57 |
| 3.1.qcir | 1.008 | 57.11 | 57.59 |
| 1.4.qcir | 1.004 | 9.88 | 9.92 |
| 1.3.qcir | 1.002 | 9.82 | 9.84 |
| 9.3.qcir | 1.001 | 2.89 | 2.89 |
| 11.1.qcir | 0.996 | 31.13 | 31.04 |
| 10.1.qcir | 0.994 | 2.39 | 2.38 |
| 8.1.qcir | 0.994 | 4.19 | 4.17 |
| 9.1.qcir | 0.993 | 1.72 | 1.71 |
| 10.2.qcir | 0.992 | 2.78 | 2.76 |
| 3.2.qcir | 0.990 | 1.75 | 1.73 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir | 0.723 | 2.12 | 1.53 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.833 | 1.65 | 1.38 |
| chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir | 0.965 | 2.48 | 2.40 |
| 3.2.qcir | 0.990 | 1.75 | 1.73 |
| 10.2.qcir | 0.992 | 2.78 | 2.76 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 85/69/154 | 74.6 | 86/69/155 | 74.5 |
| 2 | 92/69/161 | 73.3 | 89/68/157 | 73.7 |
| 3 | 89/69/158 | 74.2 | 90/68/158 | 74.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 154-161 | 73.3-74.6 |
| B | 155-158 | 73.7-74.5 |

## Instances gained and lost in a majority of seeds

- gained by B (0): none
- lost by B (3): `bt2nd-3x4_12.ig.qcir`, `hadw11-12.qcir`, `reachqu_query64_1344.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 79.7 | 66.8 | -12.9 | 4 | 1 |
| DW | 7 | 11.8 | 10.0 | -1.8 | 3 | 2 |
| DWs | 13 | 114.0 | 116.4 | +2.4 | 0 | 1 |
| JP | 6 | 109.3 | 109.1 | -0.2 | 0 | 0 |
| Lights | 2 | 53.7 | 49.3 | -4.4 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 105.4 | 104.4 | -0.9 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 83.9 | 83.8 | -0.2 | 0 | 0 |
| arbiter | 6 | 84.3 | 84.3 | -0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 66.8 | 68.6 | +1.9 | 2 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 60.8 | 61.9 | +1.1 | 5 | 7 |
| ci | 30 | 87.4 | 87.8 | +0.4 | 1 | 3 |
| collector | 1 | 3.5 | 3.8 | +0.4 | 0 | 0 |
| connect | 7 | 86.6 | 84.2 | -2.4 | 1 | 1 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 65.0 | 64.5 | -0.6 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.3 | 6.8 | -0.5 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.2 | 72.5 | +2.3 | 1 | 2 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 35.7 | 37.1 | +1.4 | 3 | 4 |
| klieber | 26 | 14.0 | 12.7 | -1.4 | 11 | 8 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.7 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.2 | 97.9 | -0.2 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.4 | 111.4 | -0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | +0.0 | 0 | 0 |
| numeric | 26 | 35.8 | 36.7 | +0.9 | 1 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 69.7 | 94.3 | +24.6 | 0 | 1 |
| robot | 1 | 3.2 | 3.1 | -0.1 | 0 | 0 |
| round | 1 | 1.0 | 0.9 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 55.8 | 55.7 | -0.1 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 33.5 | 31.4 | -2.1 | 5 | 1 |
| voter | 2 | 120.0 | 108.2 | -11.8 | 1 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-4.qcir | 52.9 | 12.7 | -40.2 |
| jctc14-unrolled-fail.qcir | 120.0 | 87.6 | -32.4 |
| CM-sat-07-01-06-3.qcir | 120.0 | 88.1 | -31.9 |
| test_5_5_el.pg-13.qcir | 63.0 | 35.0 | -28.1 |
| klieber2017q-112-28-t1.qcir | 42.0 | 16.5 | -25.5 |
| Lights2_0f5381e9.tlsf.qcir | 71.5 | 47.9 | -23.6 |
| voter_size_202219_1U43.qcir | 120.0 | 96.5 | -23.5 |
| connect-5x5_9_connect3.ig.qcir | 120.0 | 98.7 | -21.3 |
| CM-sat-07-01-07-3.qcir | 120.0 | 98.9 | -21.1 |
| ci.e#1.a#3.E#40.A#60.c#296.w#6.s#7.asp.qcir | 120.0 | 99.2 | -20.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query64_1344.qcir | 8.9 | 80.6 | +71.7 |
| hadw11-12.qcir | 35.6 | 87.6 | +52.0 |
| bt2nd-3x4_12.ig.qcir | 54.0 | 96.2 | +42.2 |
| jctc17-vals-0,2-pass.qcir | 17.6 | 51.5 | +33.9 |
| DWs-unsat-08-17-1.qcir | 42.3 | 73.4 | +31.1 |
| ci.e#1.a#3.E#40.A#60.c#280.w#6.s#7.asp.qcir | 95.8 | 120.0 | +24.2 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 62.5 | 86.5 | +24.0 |
| jctc10-fail.qcir | 96.4 | 120.0 | +23.6 |
| 11.1.qcir | 38.2 | 60.7 | +22.6 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 97.5 | 120.0 | +22.5 |

## Peak memory

18 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc1-pass.qcir | 49 | 108 | 2.21x |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 12 | 25 | 2.07x |
| klieber2017q-068-17-eq.qcir | 16 | 23 | 1.44x |
| klieber2017q-072-18-t1.qcir | 17 | 25 | 1.44x |
| hadw7-8.qcir | 24 | 34 | 1.42x |
| test_5_5_tic.pg-11.qcir | 15 | 20 | 1.37x |
| klieber2017q-076-19-t1.qcir | 19 | 25 | 1.33x |
| sc-ungrounded-1x3X3x2_1.qcir | 25 | 33 | 1.30x |
| ci.e#1.a#3.E#40.A#60.c#208.w#6.s#8.asp.qcir | 12 | 15 | 1.24x |
| hadw6-8.qcir | 65 | 81 | 1.24x |
| klieber2017q-074-18-eq.qcir | 26 | 32 | 1.24x |
| connect-4x4_9_connect3.ig.qcir | 29 | 35 | 1.22x |
| klieber2017q-076-19-eq.qcir | 46 | 55 | 1.20x |
| DW-unsat-09-23-1.qcir | 39 | 46 | 1.18x |
| klieber2017q-064-16-eq.qcir | 19 | 21 | 1.15x |
| sc-ungrounded-1x2X2x2_2.qcir | 32 | 37 | 1.15x |
| connect-3x3_9_connect3.ig.qcir | 17 | 19 | 1.13x |
| test_5_5_fatty.pg-9.qcir | 23 | 25 | 1.10x |

