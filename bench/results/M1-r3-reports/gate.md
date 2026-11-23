# Gate: identical searches, new / reference

## default

default: pooled identical searches: n=51, geometric mean new/reference = 0.964, limit 1.04: PASS

Per seed: seed 1: 0.991 (n=41), seed 2: 0.965 (n=40), seed 3: 0.891 (n=37).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| CM | 1 | 0.859 | n < 3 |
| DW | 6 | 0.855 | PASS |
| DWs | 1 | 1.003 | n < 3 |
| Lights | 1 | 1.017 | n < 3 |
| chess | 16 | 0.975 | PASS |
| collector | 1 | 0.902 | n < 3 |
| finding | 1 | 0.926 | n < 3 |
| hadw | 3 | 0.921 | PASS |
| jctc | 4 | 1.330 | FAIL |
| lift | 1 | 0.906 | n < 3 |
| ltl | 1 | 0.930 | n < 3 |
| numeric | 15 | 0.941 | PASS |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 3/3 runs, B 3/3 runs), `5.2-3.qcir` (A 3/3 runs, B 0/3 runs)
- ERROR/MISMATCH rows: none

## dl

dl: pooled identical searches: n=51, geometric mean new/reference = 0.950, limit 1.04: PASS

Per seed: seed 1: 0.949 (n=41), seed 2: 0.938 (n=43), seed 3: 0.974 (n=31).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| DW | 4 | 0.932 | PASS |
| Lights | 2 | 1.078 | n < 3 |
| chess | 18 | 0.959 | PASS |
| collector | 1 | 0.882 | n < 3 |
| finding | 1 | 1.003 | n < 3 |
| hadw | 4 | 0.899 | PASS |
| jctc | 3 | 0.969 | PASS |
| lift | 1 | 0.897 | n < 3 |
| ltl | 1 | 0.893 | n < 3 |
| numeric | 14 | 0.952 | PASS |
| round | 1 | 0.915 | n < 3 |
| voter | 1 | 0.925 | n < 3 |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 3/3 runs, B 3/3 runs), `5.2-3.qcir` (A 3/3 runs, B 3/3 runs)
- ERROR/MISMATCH rows: none

## mode1

mode1: pooled identical searches: n=36, geometric mean new/reference = 0.990, limit 1.04: PASS

Per seed: seed 1: 0.990 (n=36).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| DW | 5 | 0.916 | PASS |
| chess | 11 | 1.044 | PASS |
| collector | 1 | 0.969 | n < 3 |
| hadw | 2 | 1.188 | n < 3 |
| lift | 1 | 0.886 | n < 3 |
| ltl | 1 | 1.010 | n < 3 |
| numeric | 14 | 0.967 | PASS |
| round | 1 | 0.895 | n < 3 |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 1/1 runs, B 1/1 runs), `5.2-3.qcir` (A 1/1 runs, B 0/1 runs)
- ERROR/MISMATCH rows: none

## Summary

| configuration | kind | n | geometric mean | verdict |
|---|---:|---:|---:|---:|
| default jctc | family | 4 | 1.330 | FAIL |

GATE: FAIL (1 lines)
