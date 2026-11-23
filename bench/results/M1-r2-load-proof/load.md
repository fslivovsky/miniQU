# Load measurement M1-r2-load-proof

- A (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final5`, sha256 dfbd0f64976b470e04e8a674e9731536b944d4087bbf27019af3987d1add8900, args `--seed=1`
- B (new-r2-proof): `/home/ec2-user/miniqu-work/r2t2/miniQU-final5`, sha256 dfbd0f64976b470e04e8a674e9731536b944d4087bbf27019af3987d1add8900, args `--seed=1 -proof=/dev/null -proof-binary`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T10:40:05), B (2026-11-23T10:40:34), A (2026-11-23T10:41:06), B (2026-11-23T10:41:35), A (2026-11-23T10:42:06), B (2026-11-23T10:42:36)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.57 | 1.75 | 1.115 | 1.52-1.70 | 1.67-1.88 | yes |
| DW-unsat-09-22-1.qcir | 6.58 | 7.36 | 1.117 | 6.35-6.98 | 7.03-7.58 | yes |
| jctc10-fail.qcir | 6.30 | 7.14 | 1.133 | 5.71-6.84 | 5.41-7.85 | yes |
| DW-sat-09-26-1.qcir | 2.20 | 2.56 | 1.165 | 2.02-2.49 | 2.36-2.70 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.42 | 10.18 | 1.082 | 8.94-9.86 | 9.85-10.88 | yes |
| 9.2.qcir | 10.59 | 11.39 | 1.076 | 9.97-11.17 | 11.02-12.35 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.53 | 12.50 | 1.085 | 10.86-12.11 | 11.97-13.26 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 7.80 | 8.54 | 1.094 | 7.55-8.05 | 8.41-8.79 | yes |
| 4.1.qcir | 6.59 | 7.15 | 1.084 | 6.48-6.86 | 6.97-7.32 | yes |
| 5.2-1.qcir | 28.04 | 30.55 | 1.090 | 27.25-29.01 | 29.41-31.23 | yes |
| hadw11-12.qcir | 5.63 | 5.98 | 1.063 | 5.47-5.83 | 5.85-6.25 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.87 | 11.48 | 1.056 | 10.28-11.38 | 10.45-12.11 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.096** |  |  |  |

