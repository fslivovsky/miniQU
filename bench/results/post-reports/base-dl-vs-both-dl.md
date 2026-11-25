# Paired comparison: B (post-both-dl-s1, post-both-dl-s2, post-both-dl-s3) against A (post-base-dl-s1, post-base-dl-s2, post-base-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-25T11:12:17 |
| B | `--elim --vivify -dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T11:02:01 |

Order in which the runs started:

- 2026-11-25T11:02:01 `post-both-dl-s1`
- 2026-11-25T11:12:17 `post-base-dl-s1`
- 2026-11-25T15:33:24 `post-both-dl-s2`
- 2026-11-25T15:43:44 `post-base-dl-s2`
- 2026-11-25T17:20:31 `post-both-dl-s3`
- 2026-11-25T17:30:53 `post-base-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-4.86 s**, 95% bootstrap interval [-6.44, -3.36] (10000 resamples).

Sign test: B wins on 113 instances, loses on 10, ties on 253; two-sided p = 0.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 6 | 0.881 | 0 | 6 |
| 2 | 7 | 0.910 | 1 | 6 |
| 3 | 5 | 0.866 | 0 | 5 |
| all (per instance) | 7 | 0.904 | 1 | 6 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| numeric | 7 | 0.904 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 8.1.qcir | 1.087 | 3.91 | 4.25 |
| 1.3.qcir | 0.918 | 11.36 | 10.43 |
| 1.4.qcir | 0.918 | 11.44 | 10.50 |
| 10.1.qcir | 0.896 | 2.84 | 2.54 |
| 9.1.qcir | 0.888 | 2.23 | 1.98 |
| 10.2.qcir | 0.874 | 3.11 | 2.70 |
| 3.2.qcir | 0.778 | 2.16 | 1.68 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.778 | 2.16 | 1.68 |
| 10.2.qcir | 0.874 | 3.11 | 2.70 |
| 9.1.qcir | 0.888 | 2.23 | 1.98 |
| 10.1.qcir | 0.896 | 2.84 | 2.54 |
| 1.4.qcir | 0.918 | 11.44 | 10.50 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.3 | 92/72/164 | 71.3 |
| 2 | 86/67/153 | 75.6 | 91/72/163 | 71.7 |
| 3 | 84/62/146 | 77.7 | 91/71/162 | 72.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.6-77.7 |
| B | 162-164 | 71.3-72.1 |

## Instances gained and lost in a majority of seeds

- gained by B (12): `CM-sat-04-01-06-3.qcir`, `DWs-unsat-08-17-1.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir`, `connect-5x5_9_connect3.ig.qcir`, `hadw11-12.qcir`, `hadw7-9.qcir`, `test_5_5_el.pg-13.qcir`, `test_5_5_tippy.pg-11.qcir`
- lost by B (1): `test_5_5_domino.pg-15.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.1 | 80.3 | -16.8 | 2 | 0 |
| DW | 7 | 21.1 | 8.5 | -12.6 | 6 | 0 |
| DWs | 13 | 117.8 | 107.4 | -10.3 | 4 | 0 |
| JP | 6 | 109.9 | 104.1 | -5.8 | 1 | 0 |
| Lights | 2 | 51.4 | 17.6 | -33.8 | 2 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 102.2 | -5.5 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 86.9 | 79.3 | -7.6 | 2 | 0 |
| arbiter | 6 | 84.0 | 81.2 | -2.8 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.7 | 54.1 | -26.6 | 6 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.7 | 56.9 | -4.8 | 23 | 0 |
| ci | 30 | 88.6 | 88.3 | -0.3 | 2 | 0 |
| collector | 1 | 3.7 | 0.5 | -3.2 | 1 | 0 |
| connect | 7 | 88.3 | 74.5 | -13.8 | 3 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.0 | 64.1 | -4.9 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 6.5 | 2.7 | -3.9 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.2 | 70.4 | -7.8 | 7 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.9 | 40.3 | +2.3 | 3 | 4 |
| klieber | 26 | 17.1 | 8.0 | -9.1 | 23 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.1 | 60.3 | -0.8 | 1 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.1 | -0.2 | 0 | 0 |
| ltl | 5 | 98.9 | 96.6 | -2.2 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.0 | 109.5 | -1.5 | 1 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.2 | +0.2 | 0 | 0 |
| numeric | 26 | 36.8 | 38.6 | +1.8 | 3 | 3 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 67.8 | -5.1 | 1 | 0 |
| robot | 1 | 4.3 | 0.2 | -4.1 | 1 | 0 |
| round | 1 | 1.4 | 0.4 | -1.1 | 1 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 99.4 | -20.6 | 1 | 0 |
| sc | 9 | 57.0 | 54.9 | -2.1 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 28.5 | -9.6 | 10 | 2 |
| voter | 2 | 102.2 | 106.9 | +4.7 | 0 | 1 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| bt2nd-3x4_12.ig.qcir | 120.0 | 35.5 | -84.5 |
| bt-2x5_17.ig.qcir | 120.0 | 42.8 | -77.2 |
| test_5_5_el.pg-13.qcir | 89.8 | 14.9 | -74.9 |
| bt-3x4_19.ig.qcir | 120.0 | 45.7 | -74.3 |
| CM-sat-04-01-06-3.qcir | 90.3 | 19.6 | -70.7 |
| test_5_5_fatty.pg-9.qcir | 73.5 | 6.3 | -67.2 |
| DWs-unsat-08-17-1.qcir | 91.1 | 31.2 | -59.9 |
| bt2nd-3x6_10.ig.qcir | 90.4 | 31.8 | -58.6 |
| test_5_5_skinny.pg-9.qcir | 68.4 | 10.7 | -57.7 |
| connect-5x5_9_connect3.ig.qcir | 120.0 | 63.8 | -56.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_domino.pg-15.qcir | 51.8 | 98.8 | +47.0 |
| jctc8-pass.qcir | 1.3 | 40.1 | +38.8 |
| jctc2-pass.qcir | 4.8 | 40.9 | +36.1 |
| jctc4-fail.qcir | 10.1 | 41.4 | +31.3 |
| 5.2-2.qcir | 89.2 | 120.0 | +30.8 |
| 11.1.qcir | 33.7 | 62.9 | +29.2 |
| voter_size_202219_1U43.qcir | 84.4 | 93.8 | +9.4 |
| 5.2-1.qcir | 36.2 | 44.2 | +8.0 |
| jctc18-vals-0,2-pass.qcir | 6.4 | 8.5 | +2.1 |
| test_5_5_domino.pg-13.qcir | 2.4 | 3.7 | +1.3 |

## Peak memory

85 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| klieber2017q-112-28-t1.qcir | 12 | 41 | 3.35x |
| bt-3x6_9.ig.qcir | 15 | 41 | 2.78x |
| klieber2017q-108-27-t1.qcir | 12 | 29 | 2.36x |
| bt2nd-2x5_10.ig.qcir | 12 | 27 | 2.29x |
| connect-4x4_9_connect3.ig.qcir | 12 | 28 | 2.28x |
| klieber2017q-082-20-t1.qcir | 12 | 27 | 2.19x |
| klieber2017q-070-17-eq.qcir | 12 | 26 | 2.15x |
| klieber2017q-100-25-t1.qcir | 12 | 26 | 2.15x |
| klieber2017q-086-21-t1.qcir | 12 | 26 | 2.10x |
| mult9.sat.qcir | 15 | 31 | 2.10x |
| eequery_query42_1344.qcir | 12 | 25 | 2.07x |
| klieber2017q-078-19-eq.qcir | 12 | 25 | 2.05x |
| klieber2017q-078-19-t1.qcir | 12 | 24 | 1.98x |
| test_5_5_domino.pg-13.qcir | 12 | 23 | 1.83x |
| klieber2017q-064-16-eq.qcir | 12 | 22 | 1.79x |
| klieber2017q-072-18-eq.qcir | 12 | 22 | 1.79x |
| klieber2017q-074-18-eq.qcir | 12 | 22 | 1.79x |
| test_5_5_knobby.pg-9.qcir | 12 | 22 | 1.79x |
| klieber2017q-084-21-t1.qcir | 12 | 22 | 1.76x |
| klieber2017q-076-19-eq.qcir | 13 | 22 | 1.69x |
| hadw7-8.qcir | 24 | 39 | 1.66x |
| hadw6-7.qcir | 14 | 24 | 1.65x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 44 | 71 | 1.61x |
| jctc9-pass.qcir | 32 | 52 | 1.61x |
| klieber2017q-080-20-t1.qcir | 12 | 19 | 1.58x |
| jctc13-fail.qcir | 17 | 27 | 1.56x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | 44 | 67 | 1.54x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 44 | 68 | 1.53x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 44 | 68 | 1.53x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 44 | 67 | 1.53x |

