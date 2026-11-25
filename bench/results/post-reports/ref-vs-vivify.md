# Paired comparison: B (post-vivify-s1, post-vivify-s2, post-vivify-s3) against A (post-ref-s1, post-ref-s2, post-ref-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T09:36:14 |
| B | `--vivify ` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T09:57:39 |

Order in which the runs started:

- 2026-11-25T09:36:14 `post-ref-s1`
- 2026-11-25T09:57:39 `post-vivify-s1`
- 2026-11-25T14:08:16 `post-ref-s2`
- 2026-11-25T14:29:28 `post-vivify-s2`
- 2026-11-25T15:54:39 `post-ref-s3`
- 2026-11-25T16:16:01 `post-vivify-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.10 s**, 95% bootstrap interval [-0.64, +0.84] (10000 resamples).

Sign test: B wins on 29 instances, loses on 33, ties on 314; two-sided p = 0.7035 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 11 | 1.016 | 10 | 1 |
| 2 | 11 | 1.033 | 9 | 2 |
| 3 | 10 | 0.976 | 8 | 2 |
| all (per instance) | 15 | 1.008 | 13 | 2 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 3 | 1.152 | > 1.10 |
| DWs | 1 | 0.941 |  |
| chess | 1 | 0.706 |  |
| numeric | 10 | 1.011 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-sat-08-23-1.qcir | 1.382 | 1.84 | 2.54 |
| DW-sat-09-26-1.qcir | 1.074 | 4.29 | 4.61 |
| DW-sat-08-22-1.qcir | 1.029 | 1.03 | 1.06 |
| 9.3.qcir | 1.024 | 2.02 | 2.07 |
| 11.1.qcir | 1.013 | 29.38 | 29.80 |
| 3.2.qcir | 1.012 | 1.06 | 1.07 |
| 9.1.qcir | 1.012 | 1.55 | 1.57 |
| 3.1.qcir | 1.010 | 34.26 | 34.63 |
| 1.3.qcir | 1.009 | 6.27 | 6.33 |
| 1.4.qcir | 1.009 | 6.29 | 6.35 |
| 10.2.qcir | 1.008 | 1.53 | 1.53 |
| 8.1.qcir | 1.006 | 3.71 | 3.73 |
| 10.1.qcir | 1.004 | 1.44 | 1.45 |
| DWs-sat-10-25-1.qcir | 0.941 | 5.25 | 4.94 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.706 | 1.72 | 1.22 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.706 | 1.72 | 1.22 |
| DWs-sat-10-25-1.qcir | 0.941 | 5.25 | 4.94 |
| 10.1.qcir | 1.004 | 1.44 | 1.45 |
| 8.1.qcir | 1.006 | 3.71 | 3.73 |
| 10.2.qcir | 1.008 | 1.53 | 1.53 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 89/61/150 | 76.4 | 90/63/153 | 76.5 |
| 2 | 90/61/151 | 76.3 | 90/61/151 | 76.3 |
| 3 | 90/61/151 | 76.3 | 89/61/150 | 76.5 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 150-151 | 76.3-76.4 |
| B | 150-153 | 76.3-76.5 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `5.2-2.qcir`, `klieber2017q-076-19-t1.qcir`
- lost by B (1): `bt2nd-2x6_14.ig.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 114.7 | -5.3 | 1 | 0 |
| DW | 7 | 38.3 | 34.3 | -4.0 | 3 | 1 |
| DWs | 13 | 117.1 | 117.1 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 69.7 | 81.6 | +11.9 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 115.5 | -4.5 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 85.8 | 90.5 | +4.7 | 0 | 1 |
| arbiter | 6 | 83.4 | 84.0 | +0.6 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 52.9 | 56.4 | +3.5 | 1 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.6 | 28.6 | +1.0 | 3 | 5 |
| ci | 30 | 101.4 | 100.4 | -1.0 | 4 | 0 |
| collector | 1 | 3.1 | 3.0 | -0.1 | 0 | 0 |
| connect | 7 | 70.2 | 71.1 | +0.9 | 0 | 1 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 70.0 | 71.3 | +1.3 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.9 | 7.7 | -0.2 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.7 | 70.7 | +0.0 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 64.0 | 66.8 | +2.7 | 0 | 1 |
| klieber | 26 | 52.0 | 52.5 | +0.5 | 7 | 12 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.6 | 60.6 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.9 | 97.9 | +0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.8 | 111.7 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | +0.0 | 0 | 0 |
| numeric | 26 | 29.9 | 29.7 | -0.2 | 1 | 3 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 94.3 | 96.6 | +2.3 | 0 | 0 |
| robot | 1 | 4.1 | 2.6 | -1.5 | 1 | 0 |
| round | 1 | 0.8 | 1.1 | +0.3 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.2 | 57.2 | +1.0 | 0 | 1 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 35.8 | 34.3 | -1.5 | 6 | 2 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| 5.2-2.qcir | 120.0 | 74.0 | -46.0 |
| klieber2017q-080-20-t1.qcir | 60.9 | 19.3 | -41.6 |
| CM-sat-04-01-07-3.qcir | 120.0 | 82.8 | -37.2 |
| klieber2017q-076-19-t1.qcir | 88.9 | 56.1 | -32.9 |
| klieber2017q-078-19-t1.qcir | 88.1 | 55.8 | -32.3 |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 29.8 | 5.4 | -24.3 |
| SR-sat-02-01-06-3.qcir | 120.0 | 97.4 | -22.6 |
| DW-unsat-10-25-1.qcir | 98.3 | 76.8 | -21.5 |
| klieber2017q-086-21-t1.qcir | 120.0 | 99.3 | -20.7 |
| test_5_5_tippy.pg-11.qcir | 120.0 | 99.3 | -20.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| bt2nd-2x6_14.ig.qcir | 73.7 | 120.0 | +46.3 |
| klieber2017q-076-19-eq.qcir | 34.2 | 66.7 | +32.4 |
| jctc8-pass.qcir | 9.3 | 40.1 | +30.8 |
| klieber2017q-112-28-t1.qcir | 93.6 | 120.0 | +26.4 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 38.7 | 62.7 | +24.0 |
| amba2f9n.sat.qcir | 48.4 | 72.1 | +23.7 |
| 11.1.qcir | 36.5 | 59.9 | +23.4 |
| klieber2017q-100-25-t1.qcir | 98.9 | 120.0 | +21.1 |
| Lights2_b02056d6.tlsf.qcir | 99.7 | 120.0 | +20.3 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 10.9 | 26.4 | +15.5 |

## Peak memory

15 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-2x2X2x2_1.qcir | 84 | 178 | 2.12x |
| klieber2017q-064-16-t1.qcir | 16 | 24 | 1.48x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 77 | 106 | 1.38x |
| klieber2017q-108-27-t1.qcir | 19 | 26 | 1.35x |
| klieber2017q-074-18-t1.qcir | 17 | 22 | 1.32x |
| hadw6-8.qcir | 76 | 98 | 1.28x |
| klieber2017q-072-18-eq.qcir | 26 | 34 | 1.28x |
| klieber2017q-082-20-t1.qcir | 19 | 25 | 1.28x |
| bt2nd-2x5_10.ig.qcir | 23 | 28 | 1.23x |
| connect-3x3_9_connect3.ig.qcir | 14 | 17 | 1.18x |
| 5.2-1.qcir | 303 | 354 | 1.17x |
| arbiter_on_inpchange5.tlsf.qcir | 18 | 21 | 1.16x |
| test_5_5_skinny.pg-9.qcir | 20 | 23 | 1.14x |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 54 | 60 | 1.12x |
| sc-ungrounded-2x1X1x3_1.qcir | 30 | 33 | 1.12x |

