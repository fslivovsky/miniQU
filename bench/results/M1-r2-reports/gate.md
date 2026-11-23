# Gate: identical searches, new / reference

## default

default: pooled identical searches: n=51, geometric mean new/reference = 1.037, limit 1.04: PASS

Per seed: seed 1: 1.027 (n=40), seed 2: 1.042 (n=40), seed 3: 1.007 (n=37).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| CM | 1 | 1.035 | n < 3 |
| DW | 6 | 1.144 | FAIL |
| DWs | 1 | 0.965 | n < 3 |
| Lights | 1 | 1.126 | n < 3 |
| chess | 16 | 1.076 | PASS |
| collector | 1 | 0.943 | n < 3 |
| finding | 1 | 0.981 | n < 3 |
| hadw | 3 | 1.133 | FAIL |
| jctc | 4 | 1.038 | PASS |
| lift | 1 | 0.930 | n < 3 |
| ltl | 1 | 1.014 | n < 3 |
| numeric | 15 | 0.957 | PASS |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 3/3 runs, B 3/3 runs), `5.2-3.qcir` (A 3/3 runs, B 3/3 runs)
- ERROR/MISMATCH rows: none

## dl

dl: pooled identical searches: n=50, geometric mean new/reference = 1.001, limit 1.04: PASS

Per seed: seed 1: 1.007 (n=40), seed 2: 0.990 (n=42), seed 3: 0.995 (n=30).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| DW | 4 | 1.107 | FAIL |
| Lights | 1 | 1.221 | n < 3 |
| chess | 18 | 1.008 | PASS |
| collector | 1 | 1.018 | n < 3 |
| finding | 1 | 1.173 | n < 3 |
| hadw | 4 | 0.963 | PASS |
| jctc | 3 | 0.966 | PASS |
| lift | 1 | 0.968 | n < 3 |
| ltl | 1 | 1.016 | n < 3 |
| numeric | 14 | 0.957 | PASS |
| round | 1 | 1.018 | n < 3 |
| voter | 1 | 0.980 | n < 3 |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 3/3 runs, B 3/3 runs), `5.2-3.qcir` (A 3/3 runs, B 3/3 runs)
- ERROR/MISMATCH rows: none

## mode1

mode1: pooled identical searches: n=35, geometric mean new/reference = 1.063, limit 1.04: REPORT (above, to be explained)

Per seed: seed 1: 1.063 (n=35).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| DW | 5 | 1.260 | REPORT (above, to be explained) |
| chess | 11 | 1.119 | REPORT (above, to be explained) |
| collector | 1 | 1.016 | n < 3 |
| hadw | 2 | 1.235 | n < 3 |
| lift | 1 | 0.895 | n < 3 |
| ltl | 1 | 1.032 | n < 3 |
| numeric | 13 | 0.958 | PASS |
| round | 1 | 0.955 | n < 3 |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 1/1 runs, B 1/1 runs), `5.2-3.qcir` (A 1/1 runs, B 1/1 runs)
- ERROR/MISMATCH rows: none

## Summary

| configuration | kind | n | geometric mean | verdict |
|---|---:|---:|---:|---:|
| default DW | family | 6 | 1.144 | FAIL |
| default hadw | family | 3 | 1.133 | FAIL |
| dl DW | family | 4 | 1.107 | FAIL |
| mode1 | pooled | 35 | 1.063 | REPORT (above, to be explained) |
| mode1 DW | family | 5 | 1.260 | REPORT (above, to be explained) |
| mode1 chess | family | 11 | 1.119 | REPORT (above, to be explained) |

GATE: FAIL (3 lines)
