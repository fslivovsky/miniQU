# Paired comparison: B (post-both-dl-s1, post-both-dl-s2, post-both-dl-s3) against A (post-ref-dl-s1, post-ref-dl-s2, post-ref-dl-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8.0, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T10:30:23 |
| B | `--elim --vivify -dl` | bcc7ed2 | 3e47d7e820a7 | 2026-11-25T11:02:01 |

Order in which the runs started:

- 2026-11-25T10:30:23 `post-ref-dl-s1`
- 2026-11-25T11:02:01 `post-both-dl-s1`
- 2026-11-25T15:01:54 `post-ref-dl-s2`
- 2026-11-25T15:33:24 `post-both-dl-s2`
- 2026-11-25T16:48:49 `post-ref-dl-s3`
- 2026-11-25T17:20:31 `post-both-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-2.37 s**, 95% bootstrap interval [-3.42, -1.42] (10000 resamples).

Sign test: B wins on 102 instances, loses on 13, ties on 261; two-sided p = 0.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 8 | 1.054 | 7 | 1 |
| 2 | 7 | 1.038 | 5 | 2 |
| 3 | 6 | 1.067 | 5 | 1 |
| all (per instance) | 8 | 1.043 | 6 | 2 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| numeric | 8 | 1.043 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 9.1.qcir | 1.149 | 1.72 | 1.98 |
| 10.1.qcir | 1.071 | 2.39 | 2.54 |
| 1.4.qcir | 1.063 | 9.88 | 10.50 |
| 1.3.qcir | 1.062 | 9.82 | 10.43 |
| 8.1.qcir | 1.053 | 4.19 | 4.42 |
| 10.2.qcir | 1.038 | 2.69 | 2.70 |
| 3.2.qcir | 0.967 | 1.75 | 1.68 |
| 11.1.qcir | 0.954 | 36.15 | 34.48 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 11.1.qcir | 0.954 | 36.15 | 34.48 |
| 3.2.qcir | 0.967 | 1.75 | 1.68 |
| 10.2.qcir | 1.038 | 2.69 | 2.70 |
| 8.1.qcir | 1.053 | 4.19 | 4.42 |
| 1.3.qcir | 1.062 | 9.82 | 10.43 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 85/69/154 | 74.6 | 92/72/164 | 71.3 |
| 2 | 92/69/161 | 73.3 | 91/72/163 | 71.7 |
| 3 | 89/69/158 | 74.2 | 91/71/162 | 72.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 154-161 | 73.3-74.6 |
| B | 162-164 | 71.3-72.1 |

## Instances gained and lost in a majority of seeds

- gained by B (3): `bt-3x4_19.ig.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir`, `connect-5x5_9_connect3.ig.qcir`
- lost by B (1): `3.1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 79.7 | 80.3 | +0.7 | 1 | 1 |
| DW | 7 | 11.8 | 8.5 | -3.3 | 5 | 0 |
| DWs | 13 | 114.0 | 107.4 | -6.6 | 4 | 0 |
| JP | 6 | 109.3 | 104.1 | -5.2 | 1 | 0 |
| Lights | 2 | 53.7 | 17.6 | -36.0 | 2 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 105.4 | 102.2 | -3.2 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 83.9 | 79.3 | -4.6 | 2 | 0 |
| arbiter | 6 | 84.3 | 81.2 | -3.1 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 66.8 | 54.1 | -12.7 | 6 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 60.8 | 56.9 | -3.9 | 24 | 1 |
| ci | 30 | 87.4 | 88.3 | +0.9 | 0 | 2 |
| collector | 1 | 3.5 | 0.5 | -2.9 | 1 | 0 |
| connect | 7 | 86.6 | 74.5 | -12.1 | 3 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 65.0 | 64.1 | -0.9 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.3 | 2.7 | -4.6 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.2 | 70.4 | +0.2 | 2 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 35.7 | 40.3 | +4.5 | 5 | 4 |
| klieber | 26 | 14.0 | 8.0 | -6.0 | 23 | 1 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.3 | -0.5 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.1 | -0.1 | 0 | 0 |
| ltl | 5 | 98.2 | 96.6 | -1.5 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.4 | 109.5 | -1.9 | 1 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.2 | +0.2 | 0 | 0 |
| numeric | 26 | 35.8 | 38.6 | +2.8 | 3 | 3 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 69.7 | 67.8 | -1.9 | 1 | 0 |
| robot | 1 | 3.2 | 0.2 | -3.0 | 1 | 0 |
| round | 1 | 1.0 | 0.4 | -0.7 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 99.4 | -20.6 | 1 | 0 |
| sc | 9 | 55.8 | 54.9 | -0.9 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 33.5 | 28.5 | -5.0 | 6 | 0 |
| voter | 2 | 120.0 | 106.9 | -13.1 | 1 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| bt-3x4_19.ig.qcir | 120.0 | 45.7 | -74.3 |
| connect-5x5_9_connect3.ig.qcir | 120.0 | 63.8 | -56.2 |
| Lights2_0f5381e9.tlsf.qcir | 71.5 | 23.1 | -48.4 |
| test_5_5_el.pg-13.qcir | 63.0 | 14.9 | -48.2 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 120.0 | 74.7 | -45.3 |
| bt-2x5_17.ig.qcir | 77.0 | 42.8 | -34.2 |
| test_5_5_tippy.pg-11.qcir | 97.8 | 65.9 | -31.8 |
| DWs-sat-10-25-1.qcir | 120.0 | 88.7 | -31.3 |
| JP-unsat-02-06-3.qcir | 55.8 | 24.6 | -31.2 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 62.5 | 34.4 | -28.1 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| 3.1.qcir | 78.1 | 120.0 | +41.9 |
| jctc1-pass.qcir | 1.3 | 40.6 | +39.2 |
| jctc4-fail.qcir | 4.9 | 41.4 | +36.5 |
| 11.1.qcir | 38.2 | 62.9 | +24.8 |
| ci.e#1.a#3.E#40.A#60.c#280.w#6.s#7.asp.qcir | 95.8 | 120.0 | +24.2 |
| jctc10-fail.qcir | 96.4 | 120.0 | +23.6 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 97.5 | 120.0 | +22.5 |
| 5.2-1.qcir | 21.9 | 44.2 | +22.3 |
| CM-sat-04-01-06-3.qcir | 5.4 | 19.6 | +14.2 |
| hadw11-12.qcir | 35.6 | 42.7 | +7.1 |

## Peak memory

68 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | 35 | 68 | 1.94x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 38 | 71 | 1.87x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | 34 | 62 | 1.83x |
| chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir | 34 | 62 | 1.82x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 37 | 68 | 1.81x |
| chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir | 34 | 61 | 1.81x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | 38 | 68 | 1.81x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 38 | 69 | 1.80x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 38 | 68 | 1.80x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 37 | 67 | 1.80x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | 37 | 67 | 1.80x |
| 4.2.qcir | 73 | 130 | 1.79x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 38 | 67 | 1.79x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 38 | 68 | 1.79x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 38 | 67 | 1.78x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | 38 | 67 | 1.78x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 39 | 68 | 1.77x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 38 | 67 | 1.76x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 37 | 62 | 1.66x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | 38 | 62 | 1.65x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 37 | 61 | 1.64x |
| hadw7-8.qcir | 24 | 39 | 1.64x |
| jctc9-pass.qcir | 32 | 52 | 1.64x |
| CM-sat-04-01-06-3.qcir | 205 | 330 | 1.61x |
| hadw6-7.qcir | 15 | 24 | 1.60x |
| 4.1.qcir | 83 | 132 | 1.59x |
| 9.3.qcir | 108 | 166 | 1.54x |
| 3.2.qcir | 213 | 326 | 1.53x |
| 9.2.qcir | 118 | 179 | 1.52x |
| klieber2017q-078-19-t1.qcir | 16 | 24 | 1.52x |

