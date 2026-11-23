# Paired comparison: B (M1-r1-dl-s1, M1-r1-dl-s2, M1-r1-dl-s3) against A (baseline-c96-dl-t60-s1, baseline-c96-dl-t60-s2, baseline-c96-dl-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-23T01:28:03 |
| B | `-dl` | 00eb7a4 | a48a1a946f47 | 2026-11-23T01:22:04 |

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.40 s**, 95% bootstrap interval [-0.34, +1.11] (10000 resamples).

Sign test: B wins on 27 instances, loses on 44, ties on 305; two-sided p = 0.0568 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.4 | 84/64/148 | 77.0 |
| 2 | 86/67/153 | 75.7 | 86/65/151 | 76.2 |
| 3 | 84/62/146 | 77.7 | 82/63/145 | 77.8 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.7-77.7 |
| B | 145-151 | 76.2-77.8 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `CM-sat-04-01-06-3.qcir`
- lost by B (1): `Lights2_0f5381e9.tlsf.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.2 | 89.1 | -8.1 | 2 | 2 |
| DW | 7 | 21.4 | 21.6 | +0.2 | 1 | 5 |
| DWs | 13 | 117.8 | 120.0 | +2.2 | 0 | 1 |
| JP | 6 | 109.9 | 113.0 | +3.1 | 0 | 1 |
| Lights | 2 | 50.2 | 75.5 | +25.4 | 0 | 2 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 105.1 | -2.5 | 1 | 1 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.2 | 91.3 | +4.1 | 1 | 1 |
| arbiter | 6 | 84.2 | 84.9 | +0.7 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.8 | 83.6 | +2.9 | 1 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.8 | 62.7 | +0.8 | 0 | 12 |
| ci | 30 | 88.6 | 88.6 | +0.0 | 1 | 1 |
| collector | 1 | 4.3 | 4.8 | +0.5 | 0 | 0 |
| connect | 7 | 88.4 | 87.7 | -0.8 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.5 | 70.2 | +0.7 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.8 | 9.4 | +1.6 | 0 | 1 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.7 | 78.5 | -0.2 | 1 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.4 | 39.9 | +2.5 | 1 | 2 |
| klieber | 26 | 17.3 | 16.3 | -1.0 | 11 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.1 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.2 | 99.1 | -0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.1 | 111.8 | +0.7 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | -0.0 | 0 | 0 |
| numeric | 26 | 36.8 | 37.8 | +1.0 | 0 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 80.2 | +7.4 | 0 | 1 |
| robot | 1 | 4.4 | 3.3 | -1.1 | 1 | 0 |
| round | 1 | 1.4 | 1.3 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.7 | 56.4 | -0.3 | 1 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 37.3 | -0.9 | 4 | 2 |
| voter | 2 | 102.1 | 102.0 | -0.1 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 90.4 | 25.1 | -65.3 |
| klieber2017q-084-21-eq.qcir | 68.4 | 27.3 | -41.1 |
| jctc10-fail.qcir | 120.0 | 89.5 | -30.5 |
| SR-sat-02-01-06-3.qcir | 120.0 | 90.4 | -29.6 |
| test_5_5_fatty.pg-9.qcir | 73.9 | 46.9 | -27.0 |
| CM-sat-07-01-07-3.qcir | 120.0 | 98.2 | -21.8 |
| DW-unsat-11-26-1.qcir | 72.9 | 59.6 | -13.2 |
| klieber2017q-086-21-t1.qcir | 18.6 | 9.7 | -8.9 |
| test_5_5_knobby.pg-9.qcir | 26.3 | 17.9 | -8.3 |
| test_5_5_skinny.pg-9.qcir | 68.3 | 61.2 | -7.1 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_0f5381e9.tlsf.qcir | 75.5 | 120.0 | +44.5 |
| jctc4-fail.qcir | 9.9 | 41.3 | +31.4 |
| bt2nd-3x6_10.ig.qcir | 90.8 | 120.0 | +29.2 |
| klieber2017q-088-22-eq.qcir | 62.7 | 91.2 | +28.5 |
| DWs-unsat-08-17-1.qcir | 91.7 | 120.0 | +28.3 |
| jctc14-unrolled-fail.qcir | 92.4 | 120.0 | +27.6 |
| 5.2-1.qcir | 35.5 | 59.1 | +23.6 |
| CM-sat-04-01-06-4.qcir | 96.5 | 120.0 | +23.5 |
| amba2f9n.sat.qcir | 53.5 | 76.1 | +22.7 |
| JP-unsat-02-06-3.qcir | 59.4 | 77.8 | +18.4 |

## Peak memory

5 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc6-pass.qcir | 64 | 122 | 1.90x |
| jctc13-fail.qcir | 17 | 25 | 1.50x |
| CM-sat-04-01-07-3.qcir | 480 | 581 | 1.21x |
| bt-3x6_9.ig.qcir | 14 | 17 | 1.20x |
| jctc8-pass.qcir | 49 | 58 | 1.19x |

