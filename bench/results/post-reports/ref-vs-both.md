# Paired comparison: B (post-both-s1, post-both-s2, post-both-s3) against A (post-ref-s1, post-ref-s2, post-ref-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T09:36:14 |
| B | `--elim --vivify ` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:08:53 |

Order in which the runs started:

- 2026-11-25T09:36:14 `post-ref-s1`
- 2026-11-25T10:08:53 `post-both-s1`
- 2026-11-25T14:08:16 `post-ref-s2`
- 2026-11-25T14:40:31 `post-both-s2`
- 2026-11-25T15:54:39 `post-ref-s3`
- 2026-11-25T16:27:03 `post-both-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-5.16 s**, 95% bootstrap interval [-6.96, -3.46] (10000 resamples).

Sign test: B wins on 90 instances, loses on 8, ties on 278; two-sided p = 0.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 8 | 1.111 | 7 | 1 |
| 2 | 7 | 1.121 | 6 | 1 |
| 3 | 6 | 1.146 | 6 | 0 |
| all (per instance) | 9 | 1.117 | 8 | 1 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| numeric | 9 | 1.117 | > 1.10 |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 10.2.qcir | 1.258 | 1.12 | 1.41 |
| 3.2.qcir | 1.196 | 1.06 | 1.27 |
| 9.1.qcir | 1.177 | 1.55 | 1.82 |
| 10.1.qcir | 1.160 | 1.44 | 1.67 |
| 1.3.qcir | 1.127 | 6.27 | 7.07 |
| 1.4.qcir | 1.125 | 6.29 | 7.07 |
| 8.1.qcir | 1.067 | 3.71 | 3.96 |
| 3.1.qcir | 1.008 | 34.06 | 34.38 |
| 11.1.qcir | 0.968 | 34.64 | 33.52 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 11.1.qcir | 0.968 | 34.64 | 33.52 |
| 3.1.qcir | 1.008 | 34.06 | 34.38 |
| 8.1.qcir | 1.067 | 3.71 | 3.96 |
| 1.4.qcir | 1.125 | 6.29 | 7.07 |
| 1.3.qcir | 1.127 | 6.27 | 7.07 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 89/61/150 | 76.4 | 97/69/166 | 70.7 |
| 2 | 90/61/151 | 76.3 | 97/69/166 | 70.8 |
| 3 | 90/61/151 | 76.3 | 94/67/161 | 72.0 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 150-151 | 76.3-76.4 |
| B | 161-166 | 70.7-72.0 |

## Instances gained and lost in a majority of seeds

- gained by B (17): `5.2-2.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `connect-6x6_9_connect3.ig.qcir`, `klieber2017q-066-16-eq.qcir`, `klieber2017q-076-19-t1.qcir`, `klieber2017q-078-19-t1.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-eq.qcir`, `klieber2017q-100-25-t1.qcir`, `reachqu_query64_1344.qcir`, `s-ungrounded-1x1X1x3_1.qcir`, `test_5_5_Z.pg-9.qcir`, `test_5_5_tippy.pg-11.qcir`
- lost by B (1): `jctc9-pass.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 98.3 | -21.7 | 3 | 0 |
| DW | 7 | 38.3 | 25.9 | -12.4 | 5 | 0 |
| DWs | 13 | 117.1 | 117.0 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 69.7 | 22.2 | -47.5 | 2 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 85.8 | 80.4 | -5.4 | 2 | 0 |
| arbiter | 6 | 83.4 | 81.3 | -2.1 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 52.9 | 40.9 | -12.1 | 7 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.6 | 26.1 | -1.4 | 9 | 1 |
| ci | 30 | 101.4 | 100.3 | -1.1 | 4 | 0 |
| collector | 1 | 3.1 | 0.6 | -2.5 | 1 | 0 |
| connect | 7 | 70.2 | 66.2 | -4.1 | 2 | 1 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 70.0 | 70.9 | +0.9 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.9 | 3.0 | -4.9 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.7 | 70.7 | +0.0 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 64.0 | 74.7 | +10.6 | 1 | 4 |
| klieber | 26 | 52.0 | 12.0 | -40.0 | 26 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.6 | 60.3 | -0.3 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.1 | -0.1 | 0 | 0 |
| ltl | 5 | 97.9 | 96.7 | -1.2 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.8 | 109.3 | -2.5 | 1 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 81.1 | +1.1 | 0 | 0 |
| numeric | 26 | 29.9 | 27.6 | -2.3 | 4 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 94.3 | 72.2 | -22.1 | 1 | 0 |
| robot | 1 | 4.1 | 0.3 | -3.8 | 1 | 0 |
| round | 1 | 0.8 | 0.3 | -0.5 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 51.6 | -68.4 | 1 | 0 |
| sc | 9 | 56.2 | 55.0 | -1.2 | 4 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 35.8 | 30.1 | -5.7 | 11 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-086-21-t1.qcir | 120.0 | 12.4 | -107.6 |
| klieber2017q-088-22-eq.qcir | 120.0 | 21.1 | -98.9 |
| klieber2017q-100-25-t1.qcir | 98.9 | 14.2 | -84.8 |
| klieber2017q-066-16-eq.qcir | 96.1 | 15.1 | -80.9 |
| klieber2017q-076-19-t1.qcir | 88.9 | 11.0 | -77.9 |
| klieber2017q-078-19-t1.qcir | 88.1 | 10.8 | -77.3 |
| Lights2_b02056d6.tlsf.qcir | 99.7 | 22.6 | -77.1 |
| klieber2017q-084-21-eq.qcir | 97.9 | 21.0 | -76.9 |
| reachqu_query64_1344.qcir | 81.1 | 12.3 | -68.8 |
| s-ungrounded-1x1X1x3_1.qcir | 120.0 | 51.6 | -68.4 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc9-pass.qcir | 40.8 | 120.0 | +79.2 |
| jctc10-fail.qcir | 83.0 | 120.0 | +37.0 |
| jctc6-pass.qcir | 7.9 | 40.3 | +32.4 |
| jctc8-pass.qcir | 9.3 | 40.2 | +30.9 |
| 11.1.qcir | 36.5 | 41.2 | +4.7 |
| connect-5x5_9_connect3.ig.qcir | 29.3 | 34.0 | +4.7 |
| hadw6-8.qcir | 22.0 | 25.5 | +3.5 |
| test_5_5_el.pg-13.qcir | 40.0 | 42.6 | +2.6 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 10.9 | 13.4 | +2.6 |
| reachqu_query60_1344.qcir | 81.8 | 84.3 | +2.5 |

## Peak memory

77 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| hadw7-8.qcir | 18 | 37 | 2.14x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | 29 | 57 | 1.97x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 29 | 57 | 1.95x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 30 | 57 | 1.95x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 30 | 58 | 1.95x |
| chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir | 30 | 58 | 1.95x |
| 4.2.qcir | 62 | 120 | 1.93x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 30 | 57 | 1.93x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 30 | 58 | 1.93x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | 30 | 58 | 1.93x |
| chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir | 30 | 57 | 1.93x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 30 | 58 | 1.93x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | 30 | 58 | 1.93x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | 30 | 58 | 1.92x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 30 | 57 | 1.91x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 30 | 58 | 1.91x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | 30 | 57 | 1.91x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | 30 | 58 | 1.90x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 30 | 58 | 1.89x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 31 | 58 | 1.88x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 30 | 57 | 1.88x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 31 | 58 | 1.88x |
| hadw6-7.qcir | 12 | 23 | 1.83x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 43 | 76 | 1.78x |
| hadw6-8.qcir | 76 | 133 | 1.75x |
| 4.1.qcir | 72 | 121 | 1.68x |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 54 | 90 | 1.66x |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 54 | 89 | 1.66x |
| jctc4-fail.qcir | 17 | 28 | 1.65x |
| 3.2.qcir | 179 | 292 | 1.64x |

