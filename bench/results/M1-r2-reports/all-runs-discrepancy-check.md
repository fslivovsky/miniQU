# Benchmark comparison: M1-r2-ccmin3-s1 vs M1-r2-default-s1 vs M1-r2-default-s2 vs M1-r2-default-s3 vs M1-r2-dl-s1 vs M1-r2-dl-s2 vs M1-r2-dl-s3 vs M1-r2-mode1-s1 vs M1-r2-mode2-s1 vs baseline-c96-ccmin3-t60-s1 vs baseline-c96-default-t60-s1 vs baseline-c96-default-t60-s2 vs baseline-c96-default-t60-s3 vs baseline-c96-dl-t60-s1 vs baseline-c96-dl-t60-s2 vs baseline-c96-dl-t60-s3 vs baseline-c96-mode1-t60-s1 vs baseline-c96-mode2-t60-s1 vs baseline-dl-t180 vs baseline-t180

No result discrepancies, solver errors or proof problems.

376 common instances compared (376 in the union).
**Warning:** timeouts differ between runs: {'M1-r2-ccmin3-s1': 60.0, 'M1-r2-default-s1': 60.0, 'M1-r2-default-s2': 60.0, 'M1-r2-default-s3': 60.0, 'M1-r2-dl-s1': 60.0, 'M1-r2-dl-s2': 60.0, 'M1-r2-dl-s3': 60.0, 'M1-r2-mode1-s1': 60.0, 'M1-r2-mode2-s1': 60.0, 'baseline-c96-ccmin3-t60-s1': 60.0, 'baseline-c96-default-t60-s1': 60.0, 'baseline-c96-default-t60-s2': 60.0, 'baseline-c96-default-t60-s3': 60.0, 'baseline-c96-dl-t60-s1': 60.0, 'baseline-c96-dl-t60-s2': 60.0, 'baseline-c96-dl-t60-s3': 60.0, 'baseline-c96-mode1-t60-s1': 60.0, 'baseline-c96-mode2-t60-s1': 60.0, 'baseline-dl-t180': 180.0, 'baseline-t180': 180.0}

## Summary

| run | SAT | UNSAT | solved | total | PAR2 | wall sum (solved) s | cpu sum (solved) s | max RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| M1-r2-ccmin3-s1 | 85 | 61 | 146 | 376 | 77.7 | 1619 | 1616 | 8203 |
| M1-r2-default-s1 | 81 | 59 | 140 | 376 | 79.9 | 1739 | 1735 | 8219 |
| M1-r2-default-s2 | 85 | 59 | 144 | 376 | 78.3 | 1596 | 1593 | 8197 |
| M1-r2-default-s3 | 83 | 60 | 143 | 376 | 78.9 | 1689 | 1686 | 8215 |
| M1-r2-dl-s1 | 84 | 65 | 149 | 376 | 76.6 | 1557 | 1553 | 8294 |
| M1-r2-dl-s2 | 86 | 65 | 151 | 376 | 76.0 | 1573 | 1569 | 8255 |
| M1-r2-dl-s3 | 83 | 63 | 146 | 376 | 77.4 | 1496 | 1493 | 8209 |
| M1-r2-mode1-s1 | 70 | 44 | 114 | 376 | 86.3 | 994 | 991 | 8203 |
| M1-r2-mode2-s1 | 77 | 57 | 134 | 376 | 81.2 | 1478 | 1476 | 8203 |
| baseline-c96-ccmin3-t60-s1 | 87 | 55 | 142 | 376 | 79.0 | 1636 | 1633 | 8223 |
| baseline-c96-default-t60-s1 | 82 | 59 | 141 | 376 | 79.3 | 1628 | 1625 | 8245 |
| baseline-c96-default-t60-s2 | 86 | 60 | 146 | 376 | 77.9 | 1689 | 1686 | 8286 |
| baseline-c96-default-t60-s3 | 85 | 58 | 143 | 376 | 79.1 | 1798 | 1795 | 8255 |
| baseline-c96-dl-t60-s1 | 84 | 66 | 150 | 376 | 76.4 | 1590 | 1586 | 8230 |
| baseline-c96-dl-t60-s2 | 86 | 67 | 153 | 376 | 75.7 | 1703 | 1700 | 8261 |
| baseline-c96-dl-t60-s3 | 84 | 62 | 146 | 376 | 77.7 | 1632 | 1629 | 8253 |
| baseline-c96-mode1-t60-s1 | 72 | 44 | 116 | 376 | 85.9 | 1080 | 1078 | 8226 |
| baseline-c96-mode2-t60-s1 | 77 | 53 | 130 | 376 | 82.3 | 1413 | 1410 | 8248 |
| baseline-dl-t180 | 96 | 72 | 168 | 376 | 208.5 | 3521 | 3495 | 8227 |
| baseline-t180 | 100 | 67 | 167 | 376 | 209.9 | 3668 | 3664 | 8262 |

| run | git | args | timeout | date |
|---|---:|---:|---:|---:|
| M1-r2-ccmin3-s1 | 25216c2 | `-ccmin-mode=3` | 60.0 | 2026-11-23T14:28:38 |
| M1-r2-default-s1 | 25216c2 | `` | 60.0 | 2026-11-23T13:40:40 |
| M1-r2-default-s2 | 25216c2 | `` | 60.0 | 2026-11-23T13:46:42 |
| M1-r2-default-s3 | 25216c2 | `` | 60.0 | 2026-11-23T13:52:43 |
| M1-r2-dl-s1 | 25216c2 | `-dl` | 60.0 | 2026-11-23T13:58:44 |
| M1-r2-dl-s2 | 25216c2 | `-dl` | 60.0 | 2026-11-23T14:04:39 |
| M1-r2-dl-s3 | 25216c2 | `-dl` | 60.0 | 2026-11-23T14:10:31 |
| M1-r2-mode1-s1 | 25216c2 | `-mode=1` | 60.0 | 2026-11-23T14:16:26 |
| M1-r2-mode2-s1 | 25216c2 | `-mode=2` | 60.0 | 2026-11-23T14:22:37 |
| baseline-c96-ccmin3-t60-s1 | c39005a | `-ccmin-mode=3` | 60.0 | 2026-11-23T02:52:10 |
| baseline-c96-default-t60-s1 | c39005a | `` | 60.0 | 2026-11-23T01:16:03 |
| baseline-c96-default-t60-s2 | c39005a | `` | 60.0 | 2026-11-23T01:39:53 |
| baseline-c96-default-t60-s3 | c39005a | `` | 60.0 | 2026-11-23T02:03:45 |
| baseline-c96-dl-t60-s1 | c39005a | `-dl` | 60.0 | 2026-11-23T01:28:03 |
| baseline-c96-dl-t60-s2 | c39005a | `-dl` | 60.0 | 2026-11-23T01:51:49 |
| baseline-c96-dl-t60-s3 | c39005a | `-dl` | 60.0 | 2026-11-23T02:15:46 |
| baseline-c96-mode1-t60-s1 | c39005a | `-mode=1` | 60.0 | 2026-11-23T02:27:56 |
| baseline-c96-mode2-t60-s1 | c39005a | `-mode=2` | 60.0 | 2026-11-23T02:40:07 |
| baseline-dl-t180 | c39005a | `-dl` | 180.0 | 2026-11-21T17:56:52 |
| baseline-t180 | c39005a | `` | 180.0 | 2026-11-21T16:46:30 |

## Uniquely solved

- **M1-r2-dl-s2** only (1): `SR-sat-02-01-06-3.qcir` (30.8s)
- **M1-r2-mode2-s1** only (2): `hadw2-8.qcir` (55.0s), `hadw3-7.qcir` (55.4s)
- **baseline-c96-default-t60-s3** only (1): `CM-sat-07-01-06-3.qcir` (21.5s)
- **baseline-dl-t180** only (3): `DWs-sat-10-23-1.qcir` (171.2s), `hadw7-9.qcir` (165.6s), `jctc5-fail.qcir` (7.5s)
- **baseline-t180** only (2): `connect-5x5_9_connect3.ig.qcir` (72.1s), `connect-6x6_9_connect3.ig.qcir` (49.2s)


## Per family (solved / total)

| family | n | M1-r2-ccmin3-s1 | M1-r2-default-s1 | M1-r2-default-s2 | M1-r2-default-s3 | M1-r2-dl-s1 | M1-r2-dl-s2 | M1-r2-dl-s3 | M1-r2-mode1-s1 | M1-r2-mode2-s1 | baseline-c96-ccmin3-t60-s1 | baseline-c96-default-t60-s1 | baseline-c96-default-t60-s2 | baseline-c96-default-t60-s3 | baseline-c96-dl-t60-s1 | baseline-c96-dl-t60-s2 | baseline-c96-dl-t60-s3 | baseline-c96-mode1-t60-s1 | baseline-c96-mode2-t60-s1 | baseline-dl-t180 | baseline-t180 | PAR2 M1-r2-ccmin3-s1 | PAR2 M1-r2-default-s1 | PAR2 M1-r2-default-s2 | PAR2 M1-r2-default-s3 | PAR2 M1-r2-dl-s1 | PAR2 M1-r2-dl-s2 | PAR2 M1-r2-dl-s3 | PAR2 M1-r2-mode1-s1 | PAR2 M1-r2-mode2-s1 | PAR2 baseline-c96-ccmin3-t60-s1 | PAR2 baseline-c96-default-t60-s1 | PAR2 baseline-c96-default-t60-s2 | PAR2 baseline-c96-default-t60-s3 | PAR2 baseline-c96-dl-t60-s1 | PAR2 baseline-c96-dl-t60-s2 | PAR2 baseline-c96-dl-t60-s3 | PAR2 baseline-c96-mode1-t60-s1 | PAR2 baseline-c96-mode2-t60-s1 | PAR2 baseline-dl-t180 | PAR2 baseline-t180 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| CM | 7 | 1 | 2 | 1 | 0 | 3 | 2 | 2 | 1 | 1 | 2 | 1 | 1 | 3 | 3 | 1 | 1 | 0 | 1 | 4 | 1 | 104.8 | 93.5 | 103.2 | 120.0 | 83.4 | 94.7 | 88.5 | 103.1 | 103.2 | 89.4 | 103.0 | 107.3 | 75.0 | 81.0 | 107.0 | 103.6 | 120.0 | 108.8 | 170.7 | 318.3 |
| DW | 7 | 6 | 6 | 6 | 6 | 7 | 6 | 7 | 5 | 5 | 5 | 6 | 6 | 6 | 7 | 7 | 6 | 5 | 5 | 7 | 7 | 31.0 | 32.2 | 32.9 | 32.3 | 15.3 | 26.6 | 13.4 | 41.3 | 40.9 | 38.2 | 32.7 | 32.1 | 30.7 | 18.8 | 17.0 | 28.5 | 40.2 | 40.5 | 11.7 | 18.7 |
| DWs | 13 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 3 | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 3 | 3 | 0 | 110.9 | 120.0 | 120.0 | 111.8 | 120.0 | 120.0 | 120.0 | 120.0 | 96.8 | 110.9 | 120.0 | 120.0 | 111.9 | 113.5 | 120.0 | 120.0 | 120.0 | 97.2 | 305.4 | 360.0 |
| JP | 6 | 0 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 109.5 | 109.0 | 108.9 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 105.7 | 104.0 | 120.0 | 120.0 | 120.0 | 308.9 | 360.0 |
| Lights | 2 | 0 | 0 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 2 | 1 | 1 | 1 | 2 | 2 | 1 | 1 | 1 | 2 | 2 | 120.0 | 120.0 | 81.4 | 75.0 | 72.1 | 77.8 | 74.2 | 120.0 | 74.5 | 58.8 | 86.9 | 78.9 | 73.4 | 37.9 | 44.6 | 67.9 | 89.7 | 73.4 | 46.4 | 59.4 |
| LightsTotal | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| SR | 5 | 0 | 0 | 0 | 0 | 0 | 2 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | 1 | 1 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 87.3 | 105.2 | 120.0 | 97.1 | 120.0 | 120.0 | 120.0 | 120.0 | 107.8 | 107.9 | 107.3 | 120.0 | 97.6 | 304.3 | 360.0 |
| Sensor | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| abcg | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| add | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| adder | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| amba | 5 | 2 | 1 | 1 | 1 | 2 | 2 | 1 | 1 | 0 | 2 | 1 | 1 | 1 | 2 | 2 | 2 | 1 | 0 | 2 | 2 | 87.3 | 100.8 | 100.9 | 100.5 | 86.2 | 87.3 | 99.8 | 101.5 | 120.0 | 88.7 | 100.8 | 101.2 | 101.6 | 88.1 | 85.9 | 87.6 | 101.4 | 120.0 | 230.2 | 238.0 |
| arbiter | 6 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 83.8 | 84.5 | 85.4 | 84.8 | 84.3 | 85.0 | 84.5 | 85.2 | 120.0 | 84.8 | 84.6 | 84.5 | 85.2 | 83.8 | 84.8 | 83.9 | 85.0 | 120.0 | 244.3 | 244.4 |
| auto | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| bar | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| beemldelec | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| beemskbn | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| bs | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| bt | 12 | 4 | 5 | 5 | 5 | 4 | 4 | 4 | 3 | 3 | 4 | 4 | 5 | 4 | 4 | 4 | 5 | 3 | 3 | 8 | 8 | 84.1 | 80.3 | 79.9 | 77.6 | 83.7 | 83.8 | 83.3 | 93.7 | 91.3 | 84.5 | 84.6 | 79.1 | 84.6 | 83.2 | 83.2 | 75.9 | 92.5 | 92.3 | 160.6 | 159.8 |
| cavlc | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| chess | 40 | 32 | 32 | 32 | 32 | 21 | 21 | 21 | 32 | 30 | 32 | 32 | 32 | 32 | 21 | 21 | 20 | 32 | 31 | 26 | 32 | 29.1 | 28.2 | 27.3 | 28.5 | 61.8 | 60.5 | 62.1 | 29.9 | 33.1 | 28.8 | 27.2 | 27.2 | 27.6 | 61.7 | 60.4 | 63.3 | 29.3 | 31.1 | 140.5 | 75.3 |
| ci | 30 | 5 | 5 | 5 | 5 | 8 | 8 | 8 | 5 | 8 | 5 | 5 | 5 | 5 | 8 | 8 | 8 | 5 | 8 | 8 | 5 | 100.1 | 100.2 | 100.1 | 100.1 | 89.3 | 88.2 | 88.3 | 100.1 | 88.8 | 100.2 | 100.1 | 100.1 | 100.1 | 88.2 | 89.1 | 88.4 | 100.1 | 88.4 | 264.8 | 300.1 |
| collector | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2.6 | 2.9 | 5.5 | 4.3 | 4.5 | 4.4 | 4.0 | 3.5 | 6.0 | 3.7 | 3.2 | 5.3 | 4.8 | 4.1 | 5.2 | 3.6 | 3.5 | 7.2 | 4.8 | 4.0 |
| connect | 7 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 4 | 86.9 | 87.0 | 86.9 | 86.5 | 87.3 | 88.4 | 87.2 | 89.1 | 120.0 | 87.0 | 87.4 | 86.8 | 86.7 | 88.2 | 88.1 | 89.0 | 89.1 | 120.0 | 259.3 | 172.6 |
| cycle | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| driver | 6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| ea | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| eequery | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 73.1 | 78.7 | 81.9 | 77.3 | 68.4 | 69.5 | 71.9 | 71.8 | 65.5 | 75.4 | 75.4 | 73.8 | 74.7 | 68.4 | 71.6 | 68.4 | 71.2 | 64.2 | 188.7 | 199.4 |
| ex | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| finan | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| finding | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 8.0 | 12.0 | 9.4 | 9.1 | 8.6 | 9.1 | 9.6 | 11.7 | 50.9 | 8.3 | 12.3 | 9.5 | 9.3 | 6.4 | 9.2 | 7.8 | 11.7 | 48.4 | 10.3 | 13.2 |
| genbuf | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| hadw | 21 | 8 | 8 | 8 | 8 | 8 | 9 | 7 | 9 | 10 | 8 | 8 | 8 | 8 | 8 | 9 | 7 | 10 | 8 | 9 | 8 | 76.0 | 76.0 | 76.3 | 76.0 | 79.1 | 74.1 | 82.0 | 72.2 | 69.4 | 76.1 | 76.3 | 76.6 | 76.5 | 78.7 | 74.0 | 83.3 | 69.2 | 75.9 | 217.8 | 225.7 |
| i | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| jctc | 13 | 6 | 5 | 7 | 3 | 9 | 9 | 9 | 6 | 4 | 6 | 5 | 7 | 3 | 9 | 10 | 9 | 4 | 4 | 9 | 12 | 71.0 | 75.8 | 58.7 | 92.3 | 39.4 | 39.6 | 40.2 | 70.8 | 83.3 | 69.5 | 75.7 | 59.1 | 92.3 | 38.8 | 33.3 | 40.0 | 83.9 | 83.4 | 114.3 | 32.7 |
| klieber | 26 | 22 | 18 | 19 | 21 | 25 | 26 | 25 | 1 | 22 | 17 | 20 | 21 | 20 | 24 | 26 | 26 | 2 | 20 | 26 | 25 | 38.5 | 60.1 | 51.0 | 45.3 | 15.3 | 14.3 | 18.3 | 116.5 | 36.8 | 60.9 | 49.8 | 44.8 | 55.0 | 20.8 | 14.6 | 16.5 | 112.1 | 43.9 | 16.0 | 63.2 |
| l | 8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| lift | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 60.7 | 60.7 | 60.9 | 60.5 | 61.0 | 61.5 | 61.0 | 61.0 | 62.5 | 60.8 | 60.7 | 61.0 | 60.6 | 61.1 | 61.4 | 61.0 | 61.2 | 62.4 | 181.3 | 181.2 |
| linux | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| load | 5 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.8 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.3 | 96.2 | 96.3 | 96.8 | 288.3 | 288.3 |
| ltl | 5 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 97.4 | 98.0 | 100.0 | 98.4 | 99.3 | 99.2 | 99.2 | 97.8 | 107.5 | 98.4 | 98.2 | 99.5 | 98.1 | 98.9 | 99.5 | 99.1 | 97.8 | 120.0 | 291.6 | 290.0 |
| max | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| mem | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| mult | 9 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 109.9 | 112.5 | 111.4 | 111.8 | 110.8 | 112.5 | 111.6 | 110.8 | 120.0 | 110.1 | 111.0 | 111.2 | 111.6 | 111.3 | 111.3 | 110.7 | 110.3 | 120.0 | 325.5 | 326.4 |
| myciel | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| nreachq | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 120.0 | 120.0 | 0.1 | 120.0 | 120.0 | 0.2 | 120.0 | 120.0 | 0.7 | 120.0 | 120.0 | 0.1 | 120.0 | 120.0 | 0.2 | 120.0 | 120.0 | 0.8 | 360.0 | 360.0 |
| numeric | 26 | 20 | 19 | 21 | 21 | 19 | 19 | 19 | 20 | 21 | 20 | 20 | 21 | 21 | 19 | 19 | 20 | 21 | 21 | 21 | 22 | 34.7 | 37.2 | 30.3 | 31.4 | 37.0 | 37.7 | 38.1 | 34.4 | 31.8 | 33.6 | 34.7 | 29.7 | 31.0 | 37.0 | 37.6 | 35.7 | 31.3 | 31.8 | 81.1 | 66.5 |
| prioritized | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| priority | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| reachqu | 3 | 1 | 1 | 0 | 2 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 0 | 2 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 81.1 | 95.4 | 120.0 | 48.4 | 98.8 | 80.9 | 59.7 | 91.5 | 55.6 | 80.5 | 84.2 | 120.0 | 62.6 | 81.8 | 81.4 | 55.4 | 83.3 | 57.2 | 240.2 | 248.9 |
| robot | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2.5 | 4.8 | 2.2 | 4.6 | 2.2 | 5.3 | 2.3 | 4.0 | 25.1 | 3.3 | 7.2 | 2.5 | 5.8 | 2.6 | 8.1 | 2.4 | 4.5 | 51.1 | 2.0 | 6.4 |
| round | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2.0 | 1.9 | 2.0 | 1.8 | 1.5 | 0.6 | 1.9 | 1.5 | 3.0 | 1.6 | 2.0 | 2.2 | 1.8 | 1.5 | 0.6 | 2.0 | 1.5 | 3.0 | 1.8 | 1.5 |
| router | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| s | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| sc | 9 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 4 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 4 | 5 | 5 | 56.9 | 58.4 | 56.6 | 57.3 | 55.6 | 56.3 | 56.6 | 56.8 | 74.0 | 58.2 | 59.7 | 58.8 | 58.4 | 56.2 | 56.9 | 57.0 | 58.2 | 77.2 | 166.0 | 164.2 |
| simple | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| square | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| stay | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| test | 28 | 20 | 20 | 19 | 19 | 21 | 21 | 20 | 12 | 10 | 19 | 19 | 19 | 18 | 20 | 22 | 20 | 13 | 10 | 22 | 22 | 41.6 | 41.8 | 45.8 | 45.7 | 36.1 | 35.6 | 40.2 | 70.7 | 79.0 | 45.5 | 46.2 | 46.5 | 48.8 | 39.1 | 33.1 | 42.2 | 68.6 | 79.6 | 89.1 | 97.7 |
| voter | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 66.3 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 66.4 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| workstation | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |

## M1-r2-default-s1 relative to M1-r2-ccmin3-s1 (136 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.88x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-default-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc10-fail.qcir | UNSAT | 52.42 | 5.49 | 9.56x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 0.19 | 3.23x |
| test_5_5_domino.pg-13.qcir | SAT | 4.58 | 1.46 | 3.14x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 5.13 | 2.89x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 20.84 | 8.15 | 2.56x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 38.52 | 17.78 | 2.17x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 14.34 | 6.80 | 2.11x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.48 | 0.23 | 2.04x |
| test_5_5_knobby.pg-9.qcir | SAT | 52.48 | 26.89 | 1.95x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | SAT | 0.89 | 0.48 | 1.87x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-default-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 51.53 | 0.03x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 46.06 | 0.07x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.47 | 52.18 | 0.18x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.63 | 3.12 | 0.20x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.46 | 0.21x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.46 | 1.81 | 0.25x |
| CM-sat-04-01-06-3.qcir | SAT | 13.64 | 53.29 | 0.26x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 2.97 | 0.26x |
| klieber2017q-064-16-t1.qcir | UNSAT | 13.79 | 42.97 | 0.32x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 43.80 | 0.33x |

## M1-r2-default-s2 relative to M1-r2-ccmin3-s1 (138 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **1.01x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-default-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.24 | 104.93x |
| jctc10-fail.qcir | UNSAT | 52.42 | 6.24 | 8.40x |
| CM-sat-04-01-06-3.qcir | SAT | 13.64 | 2.41 | 5.65x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 0.59 | 5.55x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 3.32 | 4.47x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 38.52 | 10.57 | 3.64x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 17.82 | 5.03 | 3.54x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 0.20 | 3.06x |
| DW-sat-09-26-1.qcir | SAT | 3.87 | 1.41 | 2.75x |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | SAT | 5.13 | 2.26 | 2.27x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-default-s2 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 45.79 | 0.03x |
| jctc6-pass.qcir | SAT | 1.81 | 17.72 | 0.10x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 5.99 | 0.13x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.63 | 3.17 | 0.20x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.53 | 45.41 | 0.28x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 1.46 | 0.29x |
| DW-sat-08-23-1.qcir | SAT | 1.10 | 3.52 | 0.31x |
| ltl2dba_beta6.tlsf.qcir | SAT | 7.05 | 20.14 | 0.35x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.28 | 0.36x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 0.94 | 0.38x |

## M1-r2-default-s3 relative to M1-r2-ccmin3-s1 (136 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.93x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-default-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-082-20-t1.qcir | UNSAT | 9.47 | 1.16 | 8.19x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.04 | 2.56 | 7.03x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 7.95 | 4.55x |
| bt-2x4_13.ig.qcir | UNSAT | 0.88 | 0.22 | 4.00x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 1.56 | 3.23x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | SAT | 0.88 | 0.33 | 2.68x |
| 5.2-1.qcir | SAT | 45.71 | 23.21 | 1.97x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 1.71 | 1.88x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.61 | 0.34 | 1.81x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.57 | 0.32 | 1.80x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-default-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 48.82 | 0.03x |
| klieber2017q-080-20-t1.qcir | UNSAT | 8.77 | 39.34 | 0.22x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.53 | 48.46 | 0.26x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.34 | 0.30x |
| test_5_5_elly.pg-7.qcir | SAT | 0.42 | 1.26 | 0.33x |
| test_5_5_elly.pg-9.qcir | SAT | 3.37 | 8.65 | 0.39x |
| DW-sat-08-22-1.qcir | SAT | 1.56 | 3.93 | 0.40x |
| DW-sat-09-26-1.qcir | SAT | 3.87 | 9.57 | 0.40x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 1.86 | 0.42x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 32.29 | 0.45x |

## M1-r2-dl-s1 relative to M1-r2-ccmin3-s1 (131 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.79x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-dl-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.08 | 247.64x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.04 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.04 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.03 | 19.65x |
| klieber2017q-070-17-t1.qcir | UNSAT | 11.62 | 0.97 | 11.92x |
| klieber2017q-072-18-t1.qcir | UNSAT | 24.87 | 2.51 | 9.89x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 4.83 | 7.48x |
| DW-unsat-09-23-1.qcir | UNSAT | 19.89 | 2.66 | 7.47x |
| klieber2017q-100-25-t1.qcir | UNSAT | 56.68 | 9.21 | 6.15x |
| klieber2017q-068-17-t1.qcir | UNSAT | 35.74 | 6.24 | 5.73x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-dl-s1 s | speedup |
|---|---:|---:|---:|---:|
| hadw10-11.qcir | UNSAT | 1.71 | 49.92 | 0.03x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 10.46 | 0.04x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.74 | 14.04 | 0.05x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 56.39 | 0.06x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 9.86 | 0.06x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.62 | 10.12 | 0.06x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 51.35 | 0.06x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 18.37 | 0.07x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 5.18 | 0.07x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.15 | 1.96 | 0.08x |

## M1-r2-dl-s2 relative to M1-r2-ccmin3-s1 (132 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.74x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-dl-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.14 | 170.79x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.04 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.03 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.03 | 19.65x |
| DW-unsat-10-25-1.qcir | UNSAT | 51.30 | 7.10 | 7.22x |
| DW-unsat-09-23-1.qcir | UNSAT | 19.89 | 2.81 | 7.07x |
| DW-unsat-09-22-1.qcir | UNSAT | 19.23 | 3.06 | 6.27x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 6.09 | 5.94x |
| klieber2017q-086-21-t1.qcir | UNSAT | 57.69 | 10.17 | 5.67x |
| hadw5-7.qcir | UNSAT | 10.22 | 1.96 | 5.20x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-dl-s2 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.15 | 5.44 | 0.03x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 11.27 | 0.04x |
| jctc4-fail.qcir | UNSAT | 0.15 | 3.62 | 0.04x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.74 | 17.78 | 0.04x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.58 | 10.37 | 0.06x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.46 | 7.50 | 0.06x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 5.63 | 0.06x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 13.10 | 0.09x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | SAT | 0.50 | 4.93 | 0.10x |
| jctc13-fail.qcir | UNSAT | 0.05 | 0.97 | 0.10x |

## M1-r2-dl-s3 relative to M1-r2-ccmin3-s1 (126 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.79x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-dl-s3 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.04 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.04 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.03 | 19.65x |
| jctc6-pass.qcir | SAT | 1.81 | 0.05 | 18.12x |
| klieber2017q-086-21-t1.qcir | UNSAT | 57.69 | 6.50 | 8.88x |
| DW-unsat-09-22-1.qcir | UNSAT | 19.23 | 2.37 | 8.13x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 4.88 | 7.40x |
| klieber2017q-064-16-eq.qcir | SAT | 15.30 | 2.16 | 7.08x |
| test_5_5_domino.pg-13.qcir | SAT | 4.58 | 0.80 | 5.71x |
| hadw5-7.qcir | UNSAT | 10.22 | 1.97 | 5.20x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-dl-s3 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.58 | 12.78 | 0.05x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.46 | 9.61 | 0.05x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.74 | 13.69 | 0.05x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 59.80 | 0.05x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 6.65 | 0.06x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.62 | 9.41 | 0.07x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | SAT | 0.65 | 9.46 | 0.07x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.57 | 8.00 | 0.07x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 39.06 | 0.08x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.61 | 18.82 | 0.09x |

## M1-r2-mode1-s1 relative to M1-r2-ccmin3-s1 (112 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.78x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-mode1-s1 s | speedup |
|---|---:|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | SAT | 13.64 | 1.86 | 7.33x |
| hadw2-7.qcir | UNSAT | 16.46 | 4.74 | 3.47x |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 8.96 | 2.66 | 3.36x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 0.80 | 0.25 | 3.17x |
| hadw5-7.qcir | UNSAT | 10.22 | 3.52 | 2.90x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 0.23 | 2.65x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.61 | 0.72 | 2.23x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.48 | 0.26 | 1.87x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | SAT | 0.89 | 0.50 | 1.80x |
| 4.2.qcir | UNSAT | 1.60 | 0.95 | 1.69x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-mode1-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 4.13 | 0.02x |
| test_5_5_elly.pg-7.qcir | SAT | 0.42 | 10.46 | 0.04x |
| test_5_5_tic.pg-9.qcir | SAT | 0.63 | 10.07 | 0.06x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 34.50 | 0.09x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 7.04 | 0.11x |
| bt2nd-2x5_10.ig.qcir | SAT | 6.59 | 42.48 | 0.16x |
| jctc4-fail.qcir | UNSAT | 0.15 | 0.86 | 0.17x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 7.10 | 0.28x |
| connect-3x3_9_connect3.ig.qcir | UNSAT | 1.10 | 3.83 | 0.29x |
| klieber2017q-060-15-eq.qcir | SAT | 8.45 | 28.71 | 0.29x |

## M1-r2-mode2-s1 relative to M1-r2-ccmin3-s1 (118 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.79x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-mode2-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.21 | 120.21x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 0.52 | 27.93x |
| 5.2-1.qcir | SAT | 45.71 | 6.34 | 7.21x |
| hadw2-7.qcir | UNSAT | 16.46 | 2.36 | 6.97x |
| jctc2-pass.qcir | SAT | 3.27 | 0.76 | 4.30x |
| DW-sat-09-26-1.qcir | SAT | 3.87 | 0.96 | 4.03x |
| klieber2017q-072-18-t1.qcir | UNSAT | 24.87 | 6.39 | 3.89x |
| DW-sat-08-22-1.qcir | SAT | 1.56 | 0.40 | 3.88x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.47 | 2.92 | 3.24x |
| klieber2017q-100-25-t1.qcir | UNSAT | 56.68 | 17.98 | 3.15x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | M1-r2-mode2-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 3.17 | 0.03x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 21.86 | 0.04x |
| jctc4-fail.qcir | UNSAT | 0.15 | 2.26 | 0.07x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 43.32 | 0.07x |
| test_5_5_tic.pg-9.qcir | SAT | 0.63 | 6.64 | 0.09x |
| robot_grid6_1.tlsf.qcir | SAT | 2.52 | 25.12 | 0.10x |
| ltl2dba_beta6.tlsf.qcir | SAT | 7.05 | 57.46 | 0.12x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 9.51 | 0.15x |
| sc-ungrounded-1x2X2x2_2.qcir | UNSAT | 3.72 | 24.43 | 0.15x |
| finding_nemo_1.tlsf.qcir | SAT | 8.01 | 50.88 | 0.16x |

## baseline-c96-ccmin3-t60-s1 relative to M1-r2-ccmin3-s1 (137 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.91x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-ccmin3-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-076-19-t1.qcir | UNSAT | 29.55 | 3.72 | 7.94x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 3.98 | 3.73x |
| 5.2-1.qcir | SAT | 45.71 | 12.83 | 3.56x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 20.84 | 6.39 | 3.26x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.04 | 5.64 | 3.20x |
| jctc10-fail.qcir | UNSAT | 52.42 | 24.58 | 2.13x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 1.61 | 2.00x |
| DW-unsat-09-22-1.qcir | UNSAT | 19.23 | 9.82 | 1.96x |
| DW-unsat-09-23-1.qcir | UNSAT | 19.89 | 11.32 | 1.76x |
| klieber2017q-100-25-t1.qcir | UNSAT | 56.68 | 32.90 | 1.72x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-ccmin3-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 58.19 | 0.02x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 3.98 | 0.19x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.51 | 0.20x |
| jctc6-pass.qcir | SAT | 1.81 | 8.35 | 0.22x |
| ci.e#1.a#3.E#40.A#60.c#424.w#2.s#1.asp.qcir | UNSAT | 0.13 | 0.41 | 0.32x |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 8.96 | 26.47 | 0.34x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.63 | 1.46 | 0.43x |
| klieber2017q-070-17-eq.qcir | SAT | 15.55 | 35.92 | 0.43x |
| hadw10-11.qcir | UNSAT | 1.71 | 3.72 | 0.46x |
| test_5_5_elly.pg-7.qcir | SAT | 0.42 | 0.84 | 0.50x |

## baseline-c96-default-t60-s1 relative to M1-r2-ccmin3-s1 (138 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.90x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-default-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc10-fail.qcir | UNSAT | 52.42 | 5.08 | 10.32x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 2.77 | 5.24x |
| klieber2017q-080-20-t1.qcir | UNSAT | 8.77 | 2.72 | 3.23x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 4.78 | 3.11x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 20.84 | 6.94 | 3.00x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 0.25 | 2.44x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 14.34 | 6.19 | 2.32x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 17.82 | 8.30 | 2.15x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 38.52 | 18.78 | 2.05x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.04 | 9.01 | 2.00x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-default-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 49.71 | 0.03x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 4.73 | 0.16x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 12.63 | 0.26x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.47 | 34.99 | 0.27x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.46 | 1.46 | 0.31x |
| robot_grid6_1.tlsf.qcir | SAT | 2.52 | 7.19 | 0.35x |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 1.86 | 5.03 | 0.37x |
| klieber2017q-108-27-t1.qcir | UNSAT | 12.53 | 32.54 | 0.39x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.63 | 1.61 | 0.39x |
| klieber2017q-070-17-eq.qcir | SAT | 15.55 | 35.39 | 0.44x |

## baseline-c96-default-t60-s2 relative to M1-r2-ccmin3-s1 (140 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **1.01x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-default-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.27 | 93.10x |
| jctc10-fail.qcir | UNSAT | 52.42 | 7.35 | 7.13x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 2.87 | 5.18x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 0.68 | 4.80x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 17.82 | 4.23 | 4.22x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 38.52 | 9.61 | 4.01x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.53 | 3.77 | 3.32x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 0.22 | 2.78x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 13.23 | 2.73x |
| DW-sat-09-26-1.qcir | SAT | 3.87 | 1.56 | 2.48x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-default-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc6-pass.qcir | SAT | 1.81 | 22.40 | 0.08x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 4.73 | 0.16x |
| klieber2017q-080-20-t1.qcir | UNSAT | 8.77 | 36.19 | 0.24x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 57.37 | 0.25x |
| test_5_5_tippy.pg-9.qcir | SAT | 17.43 | 57.48 | 0.30x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 0.94 | 0.38x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 1.10 | 0.38x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.26 | 0.39x |
| ltl2dba_beta6.tlsf.qcir | SAT | 7.05 | 17.47 | 0.40x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 0.80 | 1.97 | 0.41x |

## baseline-c96-default-t60-s3 relative to M1-r2-ccmin3-s1 (135 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.85x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-default-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.04 | 2.41 | 7.47x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 1.71 | 2.94x |
| bt-2x4_13.ig.qcir | UNSAT | 0.88 | 0.34 | 2.63x |
| 5.2-1.qcir | SAT | 45.71 | 18.62 | 2.46x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | SAT | 0.88 | 0.36 | 2.45x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 6.64 | 2.23x |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | SAT | 13.44 | 6.59 | 2.04x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 0.80 | 0.41 | 1.97x |
| DW-unsat-09-22-1.qcir | UNSAT | 19.23 | 9.96 | 1.93x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.57 | 0.33 | 1.74x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-default-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 15.61 | 0.09x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 27.93 | 0.12x |
| klieber2017q-080-20-t1.qcir | UNSAT | 8.77 | 56.58 | 0.15x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.76 | 0.17x |
| klieber2017q-108-27-t1.qcir | UNSAT | 12.53 | 55.22 | 0.23x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 47.18 | 0.31x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.47 | 30.38 | 0.31x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.30 | 0.34x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 2.11 | 0.37x |
| test_5_5_elly.pg-9.qcir | SAT | 3.37 | 8.96 | 0.38x |

## baseline-c96-dl-t60-s1 relative to M1-r2-ccmin3-s1 (130 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.76x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-dl-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.09 | 247.64x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.04 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.04 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.03 | 19.65x |
| klieber2017q-100-25-t1.qcir | UNSAT | 56.68 | 4.33 | 13.10x |
| test_5_5_knobby.pg-9.qcir | SAT | 52.48 | 6.44 | 8.15x |
| DW-unsat-09-23-1.qcir | UNSAT | 19.89 | 3.12 | 6.38x |
| klieber2017q-086-21-t1.qcir | UNSAT | 57.69 | 10.87 | 5.31x |
| klieber2017q-068-17-t1.qcir | UNSAT | 35.74 | 8.06 | 4.43x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 8.97 | 4.03x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-dl-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 14.56 | 0.03x |
| hadw10-11.qcir | UNSAT | 1.71 | 51.68 | 0.03x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 10.77 | 0.06x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.74 | 12.68 | 0.06x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.62 | 9.16 | 0.07x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.61 | 23.60 | 0.07x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.15 | 2.26 | 0.07x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.58 | 8.40 | 0.07x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 15.40 | 0.08x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 41.42 | 0.08x |

## baseline-c96-dl-t60-s2 relative to M1-r2-ccmin3-s1 (131 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.76x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-dl-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.17 | 150.08x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.53 | 0.12 | 108.01x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.04 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.04 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.03 | 19.65x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 2.62 | 13.81x |
| klieber2017q-072-18-t1.qcir | UNSAT | 24.87 | 3.37 | 7.37x |
| DW-unsat-09-23-1.qcir | UNSAT | 19.89 | 2.71 | 7.33x |
| DW-unsat-09-22-1.qcir | UNSAT | 19.23 | 2.67 | 7.21x |
| DW-unsat-10-25-1.qcir | UNSAT | 51.30 | 7.40 | 6.93x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-dl-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.15 | 5.69 | 0.03x |
| jctc4-fail.qcir | UNSAT | 0.15 | 4.28 | 0.03x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.74 | 17.93 | 0.04x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 5.69 | 0.06x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 6.39 | 0.07x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.61 | 9.01 | 0.07x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.58 | 7.70 | 0.08x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.46 | 6.09 | 0.08x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 17.93 | 0.08x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 14.75 | 0.08x |

## baseline-c96-dl-t60-s3 relative to M1-r2-ccmin3-s1 (127 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.74x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-dl-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.04 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.04 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.03 | 19.65x |
| jctc6-pass.qcir | SAT | 1.81 | 0.06 | 18.12x |
| DW-unsat-09-22-1.qcir | UNSAT | 19.23 | 2.36 | 8.15x |
| klieber2017q-070-17-t1.qcir | UNSAT | 11.62 | 1.46 | 7.96x |
| hadw5-7.qcir | UNSAT | 10.22 | 1.31 | 7.80x |
| test_5_5_domino.pg-13.qcir | SAT | 4.58 | 0.59 | 7.76x |
| jctc8-pass.qcir | SAT | 24.76 | 3.52 | 7.04x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 6.24 | 5.79x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-dl-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| jctc4-fail.qcir | UNSAT | 0.15 | 25.24 | 0.01x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | SAT | 0.65 | 13.44 | 0.05x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.57 | 10.07 | 0.06x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.46 | 7.80 | 0.06x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 17.43 | 0.07x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 4.83 | 0.07x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 43.27 | 0.07x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | SAT | 0.46 | 5.99 | 0.08x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.74 | 9.41 | 0.08x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 5.13 | 0.08x |

## baseline-c96-mode1-t60-s1 relative to M1-r2-ccmin3-s1 (111 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.76x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-mode1-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 8.96 | 2.16 | 4.14x |
| hadw5-7.qcir | UNSAT | 10.22 | 3.37 | 3.03x |
| hadw2-7.qcir | UNSAT | 16.46 | 6.43 | 2.56x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 0.25 | 2.44x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.61 | 0.81 | 1.98x |
| klieber2017q-072-18-eq.qcir | SAT | 38.92 | 20.75 | 1.88x |
| 4.2.qcir | UNSAT | 1.60 | 0.91 | 1.76x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 14.34 | 8.16 | 1.76x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.48 | 0.28 | 1.73x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | SAT | 0.89 | 0.52 | 1.73x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-mode1-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 10.68 | 0.01x |
| test_5_5_tic.pg-9.qcir | SAT | 0.63 | 12.48 | 0.05x |
| test_5_5_elly.pg-9.qcir | SAT | 3.37 | 46.93 | 0.07x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 9.46 | 0.08x |
| jctc4-fail.qcir | UNSAT | 0.15 | 0.94 | 0.16x |
| 5-5-6-3-3-81-EdAu.qcir | SAT | 0.02 | 0.47 | 0.21x |
| jctc13-fail.qcir | UNSAT | 0.05 | 0.44 | 0.23x |
| bt2nd-2x5_10.ig.qcir | SAT | 6.59 | 27.96 | 0.24x |
| test_5_5_elly.pg-7.qcir | SAT | 0.42 | 1.61 | 0.26x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.63 | 2.16 | 0.29x |

## baseline-c96-mode2-t60-s1 relative to M1-r2-ccmin3-s1 (116 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.69x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-mode2-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc6-pass.qcir | SAT | 1.81 | 0.12 | 15.76x |
| 5.2-1.qcir | SAT | 45.71 | 5.74 | 7.97x |
| hadw2-7.qcir | UNSAT | 16.46 | 3.32 | 4.95x |
| DW-sat-08-22-1.qcir | SAT | 1.56 | 0.41 | 3.80x |
| DW-sat-09-26-1.qcir | SAT | 3.87 | 1.05 | 3.67x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 9.97 | 3.63x |
| jctc2-pass.qcir | SAT | 3.27 | 0.90 | 3.62x |
| eequery_query42_1344.qcir | UNSAT | 26.13 | 8.45 | 3.09x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 5.33 | 2.78x |
| klieber2017q-072-18-eq.qcir | SAT | 38.92 | 16.67 | 2.33x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-c96-mode2-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 22.55 | 0.03x |
| robot_grid6_1.tlsf.qcir | SAT | 2.52 | 51.09 | 0.05x |
| jctc4-fail.qcir | UNSAT | 0.15 | 2.72 | 0.05x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 1.61 | 0.06x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 47.74 | 0.07x |
| test_5_5_tic.pg-9.qcir | SAT | 0.63 | 8.35 | 0.08x |
| sc-ungrounded-1x2X2x2_2.qcir | UNSAT | 3.72 | 31.12 | 0.12x |
| test_5_5_fatty.pg-7.qcir | UNSAT | 0.44 | 3.37 | 0.13x |
| jctc13-fail.qcir | UNSAT | 0.05 | 0.70 | 0.14x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 13.49 | 0.15x |

## baseline-dl-t180 relative to M1-r2-ccmin3-s1 (135 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.64x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-dl-t180 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 6.29 | 0.10 | 62.91x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 5.03 | 0.06 | 50.34x |
| test_5_5_L.pg-7.qcir | UNSAT | 1.97 | 0.04 | 19.65x |
| jctc6-pass.qcir | SAT | 1.81 | 0.15 | 12.33x |
| reachqu_query64_1344.qcir | SAT | 3.22 | 0.48 | 6.70x |
| klieber2017q-074-18-t1.qcir | UNSAT | 36.16 | 5.77 | 6.26x |
| klieber2017q-100-25-t1.qcir | UNSAT | 56.68 | 10.88 | 5.21x |
| klieber2017q-068-17-t1.qcir | UNSAT | 35.74 | 8.63 | 4.14x |
| DW-unsat-10-25-1.qcir | UNSAT | 51.30 | 12.75 | 4.02x |
| hadw5-7.qcir | UNSAT | 10.22 | 2.65 | 3.85x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-dl-t180 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 1.86 | 71.63 | 0.03x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.42 | 14.73 | 0.03x |
| hadw10-11.qcir | UNSAT | 1.71 | 42.79 | 0.04x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.36 | 8.43 | 0.04x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.60 | 13.44 | 0.04x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 64.10 | 0.05x |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | SAT | 5.13 | 88.43 | 0.06x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.15 | 2.31 | 0.07x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.58 | 8.08 | 0.07x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 14.76 | 0.08x |

## baseline-t180 relative to M1-r2-ccmin3-s1 (145 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.86x**.

Top 10 speedups:

| instance | result | M1-r2-ccmin3-s1 s | baseline-t180 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 24.76 | 0.15 | 169.62x |
| jctc10-fail.qcir | UNSAT | 52.42 | 5.43 | 9.66x |
| jctc6-pass.qcir | SAT | 1.81 | 0.22 | 8.39x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 38.52 | 12.29 | 3.13x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 14.34 | 4.67 | 3.07x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 14.85 | 5.12 | 2.90x |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | SAT | 36.23 | 13.14 | 2.76x |
| bt-2x4_13.ig.qcir | UNSAT | 0.88 | 0.34 | 2.61x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.61 | 0.68 | 2.38x |
| jctc2-pass.qcir | SAT | 3.27 | 1.46 | 2.24x |

Top 10 regressions:

| instance | result | M1-r2-ccmin3-s1 s | baseline-t180 s | speedup |
|---|---:|---:|---:|---:|
| reachqu_query64_1344.qcir | SAT | 3.22 | 26.81 | 0.12x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 10.03 | 0.14x |
| test_5_5_domino.pg-15.qcir | SAT | 27.06 | 168.39 | 0.16x |
| CM-sat-04-01-06-3.qcir | SAT | 13.64 | 68.20 | 0.20x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.40 | 0.22x |
| klieber2017q-084-21-t1.qcir | UNSAT | 14.49 | 64.06 | 0.23x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.77 | 2.96 | 0.26x |
| test_5_5_elly.pg-9.qcir | SAT | 3.37 | 11.50 | 0.29x |
| klieber2017q-108-27-t1.qcir | UNSAT | 12.53 | 34.25 | 0.37x |
| klieber2017q-078-19-eq.qcir | SAT | 24.62 | 64.90 | 0.38x |

## Proof checking (Lean qlrup-check)

| run | checked | verified | other statuses | check s (sum) | check s (max) | proof MB (sum) | proof MB (max) |
|---|---:|---:|---:|---:|---:|---:|---:|
| baseline-t180 | 115 | 115 | - | 1422.8 | 251.6 | 3682.2 | 227.0 |

## Proof coverage

| run | solved | attempted | accepted | rejected | checker timeout | checker memout | too large | checker error | proof run unfinished | not attempted |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| M1-r2-ccmin3-s1 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| M1-r2-default-s1 | 140 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 140 |
| M1-r2-default-s2 | 144 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 144 |
| M1-r2-default-s3 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 143 |
| M1-r2-dl-s1 | 149 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 149 |
| M1-r2-dl-s2 | 151 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 151 |
| M1-r2-dl-s3 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| M1-r2-mode1-s1 | 114 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 114 |
| M1-r2-mode2-s1 | 134 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 134 |
| baseline-c96-ccmin3-t60-s1 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 142 |
| baseline-c96-default-t60-s1 | 141 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 141 |
| baseline-c96-default-t60-s2 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| baseline-c96-default-t60-s3 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 143 |
| baseline-c96-dl-t60-s1 | 150 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 150 |
| baseline-c96-dl-t60-s2 | 153 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 153 |
| baseline-c96-dl-t60-s3 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| baseline-c96-mode1-t60-s1 | 116 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 116 |
| baseline-c96-mode2-t60-s1 | 130 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 130 |
| baseline-dl-t180 | 168 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 168 |
| baseline-t180 | 167 | 115 | 115 | 0 | 0 | 0 | 0 | 0 | 0 | 52 |

- `M1-r2-ccmin3-s1`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-12-28-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir` ...
- `M1-r2-default-s1`, not attempted (proofs not requested) (140): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `M1-r2-default-s2`, not attempted (proofs not requested) (144): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `M1-r2-default-s3`, not attempted (proofs not requested) (143): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `M1-r2-dl-s1`, not attempted (proofs not requested) (149): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `M1-r2-dl-s2`, not attempted (proofs not requested) (151): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-sat-02-01-06-3.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `M1-r2-dl-s3`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir` ...
- `M1-r2-mode1-s1`, not attempted (proofs not requested) (114): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir` ...
- `M1-r2-mode2-s1`, not attempted (proofs not requested) (134): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-10-25-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `baseline-c96-ccmin3-t60-s1`, not attempted (proofs not requested) (142): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-12-28-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir` ...
- `baseline-c96-default-t60-s1`, not attempted (proofs not requested) (141): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `baseline-c96-default-t60-s2`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `baseline-c96-default-t60-s3`, not attempted (proofs not requested) (143): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir` ...
- `baseline-c96-dl-t60-s1`, not attempted (proofs not requested) (150): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `DWs-unsat-08-17-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir` ...
- `baseline-c96-dl-t60-s2`, not attempted (proofs not requested) (153): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `baseline-c96-dl-t60-s3`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir`, `ci.e#1.a#3.E#40.A#60.c#208.w#6.s#8.asp.qcir` ...
- `baseline-c96-mode1-t60-s1`, not attempted (proofs not requested) (116): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir` ...
- `baseline-c96-mode2-t60-s1`, not attempted (proofs not requested) (130): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-10-25-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `baseline-dl-t180`, not attempted (proofs not requested) (168): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `DWs-sat-10-23-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir` ...
- `baseline-t180`, not attempted (solved in more than 20 s) (52): `11.1.qcir`, `3.1.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `9.2.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `connect-5x5_9_connect3.ig.qcir`, `connect-6x6_9_connect3.ig.qcir`, `eequery_query42_1344.qcir`, `hadw2-7.qcir`, `hadw5-7.qcir`, `jctc14-unrolled-fail.qcir`, `klieber2017q-064-16-eq.qcir`, `klieber2017q-064-16-t1.qcir`, `klieber2017q-066-16-eq.qcir`, `klieber2017q-068-17-t1.qcir`, `klieber2017q-070-17-eq.qcir`, `klieber2017q-072-18-eq.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-074-18-eq.qcir`, `klieber2017q-074-18-t1.qcir`, `klieber2017q-076-19-eq.qcir`, `klieber2017q-076-19-t1.qcir`, `klieber2017q-078-19-eq.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-eq.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-100-25-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `mult9.sat.qcir`, `reachqu_query64_1344.qcir`, `test_5_5_domino.pg-15.qcir`, `test_5_5_el.pg-13.qcir`, `test_5_5_fatty.pg-9.qcir`, `test_5_5_knobby.pg-9.qcir`, `test_5_5_skinny.pg-9.qcir`, `test_5_5_snaky.pg-9.qcir`

