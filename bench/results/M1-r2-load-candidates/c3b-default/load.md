# Load measurement c3b-default

- A (miniQU-final): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 `
- B (miniQU-c3): `/home/ec2-user/miniqu-work/r2t2/miniQU-c3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T07:57:50), B (2026-11-23T07:58:19), A (2026-11-23T07:58:48), B (2026-11-23T07:59:17), A (2026-11-23T07:59:47), B (2026-11-23T08:00:16)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.54 | 1.58 | 1.026 | 1.49-1.60 | 1.52-1.72 | yes |
| DW-unsat-09-22-1.qcir | 6.58 | 6.75 | 1.026 | 6.36-6.96 | 6.43-7.00 | yes |
| jctc10-fail.qcir | 6.42 | 6.14 | 0.957 | 5.73-7.11 | 5.14-7.22 | yes |
| DW-sat-09-26-1.qcir | 2.16 | 2.22 | 1.028 | 1.98-2.38 | 2.06-2.43 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.35 | 9.32 | 0.997 | 8.85-9.88 | 8.77-9.92 | yes |
| 9.2.qcir | 10.63 | 10.63 | 1.000 | 10.03-11.42 | 9.99-11.46 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.42 | 11.37 | 0.996 | 10.78-12.60 | 10.77-12.12 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 7.78 | 7.80 | 1.002 | 7.56-8.05 | 7.52-8.16 | yes |
| 4.1.qcir | 6.49 | 6.63 | 1.022 | 6.41-6.65 | 6.35-6.73 | yes |
| 5.2-1.qcir | 27.92 | 28.08 | 1.006 | 27.02-28.79 | 27.18-28.85 | yes |
| hadw11-12.qcir | 5.47 | 5.60 | 1.023 | 5.30-5.69 | 5.43-5.72 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.63 | 10.73 | 1.009 | 10.08-11.06 | 9.92-11.24 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.007** |  |  |  |

