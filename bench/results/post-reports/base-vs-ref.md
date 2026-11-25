# Paired comparison: B (post-ref-s1, post-ref-s2, post-ref-s3) against A (post-base-s1, post-base-s2, post-base-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-25T10:19:03 |
| B | `` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T09:36:14 |

Order in which the runs started:

- 2026-11-25T09:36:14 `post-ref-s1`
- 2026-11-25T10:19:03 `post-base-s1`
- 2026-11-25T14:08:16 `post-ref-s2`
- 2026-11-25T14:50:43 `post-base-s2`
- 2026-11-25T15:54:39 `post-ref-s3`
- 2026-11-25T16:37:22 `post-base-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-2.34 s**, 95% bootstrap interval [-4.09, -0.73] (10000 resamples).

Sign test: B wins on 67 instances, loses on 31, ties on 278; two-sided p = 0.0004 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 6 | 0.755 | 0 | 6 |
| 2 | 6 | 0.758 | 0 | 6 |
| 3 | 6 | 0.734 | 0 | 6 |
| all (per instance) | 7 | 0.759 | 0 | 7 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| numeric | 7 | 0.759 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.1.qcir | 0.873 | 43.18 | 37.69 |
| 1.4.qcir | 0.782 | 8.04 | 6.29 |
| 1.3.qcir | 0.778 | 8.06 | 6.27 |
| 10.1.qcir | 0.730 | 1.82 | 1.33 |
| 10.2.qcir | 0.724 | 2.05 | 1.53 |
| 9.1.qcir | 0.724 | 2.14 | 1.55 |
| 3.2.qcir | 0.713 | 1.25 | 0.89 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.713 | 1.25 | 0.89 |
| 9.1.qcir | 0.724 | 2.14 | 1.55 |
| 10.2.qcir | 0.724 | 2.05 | 1.53 |
| 10.1.qcir | 0.730 | 1.82 | 1.33 |
| 1.3.qcir | 0.778 | 8.06 | 6.27 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 89/61/150 | 76.4 |
| 2 | 86/60/146 | 77.8 | 90/61/151 | 76.3 |
| 3 | 86/58/144 | 78.9 | 90/61/151 | 76.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.8-79.3 |
| B | 150-151 | 76.3-76.4 |

## Instances gained and lost in a majority of seeds

- gained by B (13): `amba2f9n.sat.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt2nd-2x6_14.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `connect-5x5_9_connect3.ig.qcir`, `hadw6-8.qcir`, `jctc6-pass.qcir`, `jctc9-pass.qcir`, `test_5_5_el.pg-13.qcir`, `test_5_5_knobby.pg-9.qcir`, `test_5_5_snaky.pg-9.qcir`
- lost by B (3): `CM-sat-04-01-06-4.qcir`, `DW-unsat-10-25-1.qcir`, `klieber2017q-076-19-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.2 | 120.0 | +24.8 | 0 | 4 |
| DW | 7 | 30.6 | 38.3 | +7.7 | 1 | 4 |
| DWs | 13 | 117.2 | 117.1 | -0.2 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.9 | 69.7 | -10.2 | 1 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 85.8 | -15.4 | 2 | 0 |
| arbiter | 6 | 84.5 | 83.4 | -1.1 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.6 | 52.9 | -29.6 | 6 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.2 | 27.6 | +0.4 | 3 | 6 |
| ci | 30 | 100.1 | 101.4 | +1.3 | 0 | 4 |
| collector | 1 | 4.1 | 3.1 | -1.0 | 1 | 0 |
| connect | 7 | 86.9 | 70.2 | -16.6 | 3 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 73.8 | 70.0 | -3.8 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.1 | 7.9 | -2.2 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.4 | 70.7 | -5.7 | 3 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.9 | 64.0 | -11.9 | 5 | 2 |
| klieber | 26 | 48.9 | 52.0 | +3.1 | 13 | 8 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.6 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.5 | 97.9 | -0.6 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.2 | 111.8 | +0.6 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 29.9 | -1.9 | 5 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 89.3 | 94.3 | +5.0 | 1 | 1 |
| robot | 1 | 5.2 | 4.1 | -1.1 | 1 | 0 |
| round | 1 | 2.1 | 0.8 | -1.3 | 1 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 59.1 | 56.2 | -2.9 | 4 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 47.2 | 35.8 | -11.4 | 12 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| bt2nd-3x6_10.ig.qcir | 120.0 | 20.1 | -99.9 |
| hadw6-8.qcir | 120.0 | 22.0 | -98.0 |
| connect-5x5_9_connect3.ig.qcir | 120.0 | 29.3 | -90.7 |
| jctc6-pass.qcir | 87.5 | 7.9 | -79.6 |
| test_5_5_snaky.pg-9.qcir | 120.0 | 43.8 | -76.2 |
| test_5_5_knobby.pg-9.qcir | 90.6 | 16.4 | -74.2 |
| bt-3x4_19.ig.qcir | 120.0 | 48.0 | -72.0 |
| amba2f9n.sat.qcir | 120.0 | 48.4 | -71.6 |
| bt2nd-3x4_12.ig.qcir | 96.9 | 31.9 | -65.0 |
| test_5_5_el.pg-13.qcir | 98.1 | 40.0 | -58.1 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-4.qcir | 43.8 | 120.0 | +76.2 |
| klieber2017q-076-19-t1.qcir | 29.1 | 88.9 | +59.8 |
| DW-unsat-10-25-1.qcir | 49.1 | 98.3 | +49.2 |
| klieber2017q-088-22-t1.qcir | 10.1 | 54.8 | +44.7 |
| jctc2-pass.qcir | 81.4 | 120.0 | +38.6 |
| jctc10-fail.qcir | 45.7 | 83.0 | +37.3 |
| CM-sat-04-01-07-3.qcir | 84.2 | 120.0 | +35.8 |
| klieber2017q-086-21-t1.qcir | 87.8 | 120.0 | +32.2 |
| CM-sat-07-01-06-3.qcir | 88.1 | 120.0 | +31.9 |
| klieber2017q-072-18-t1.qcir | 43.1 | 74.1 | +31.0 |

## Peak memory

33 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| mult9.sat.qcir | 12 | 48 | 3.86x |
| klieber2017q-076-19-eq.qcir | 13 | 42 | 3.25x |
| bt-3x6_9.ig.qcir | 15 | 43 | 2.86x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 12 | 34 | 2.81x |
| klieber2017q-078-19-eq.qcir | 15 | 39 | 2.66x |
| klieber2017q-074-18-eq.qcir | 12 | 30 | 2.43x |
| klieber2017q-070-17-eq.qcir | 12 | 29 | 2.33x |
| eequery_query42_1344.qcir | 12 | 26 | 2.17x |
| klieber2017q-072-18-eq.qcir | 12 | 26 | 2.13x |
| klieber2017q-068-17-t1.qcir | 12 | 26 | 2.09x |
| bt2nd-2x5_10.ig.qcir | 12 | 23 | 1.91x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | 12 | 21 | 1.77x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | 12 | 21 | 1.76x |
| test_5_5_fatty.pg-9.qcir | 12 | 21 | 1.69x |
| klieber2017q-068-17-eq.qcir | 12 | 20 | 1.61x |
| test_5_5_skinny.pg-9.qcir | 12 | 20 | 1.60x |
| klieber2017q-082-20-t1.qcir | 12 | 19 | 1.58x |
| test_5_5_tippy.pg-9.qcir | 12 | 19 | 1.56x |
| connect-4x4_9_connect3.ig.qcir | 12 | 19 | 1.54x |
| klieber2017q-108-27-t1.qcir | 12 | 19 | 1.54x |
| test_5_5_domino.pg-13.qcir | 12 | 19 | 1.54x |
| amba2c7n.sat.qcir | 16 | 24 | 1.52x |
| klieber2017q-064-16-eq.qcir | 12 | 18 | 1.42x |
| ci.e#1.a#3.E#40.A#60.c#424.w#2.s#1.asp.qcir | 12 | 16 | 1.37x |
| klieber2017q-070-17-t1.qcir | 12 | 17 | 1.36x |
| klieber2017q-074-18-t1.qcir | 12 | 17 | 1.36x |
| klieber2017q-060-15-eq.qcir | 12 | 16 | 1.33x |
| klieber2017q-064-16-t1.qcir | 12 | 16 | 1.33x |
| hadw11-12.qcir | 126 | 154 | 1.23x |
| test_5_5_tic.pg-11.qcir | 12 | 15 | 1.23x |

