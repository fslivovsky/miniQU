# Load measurement c3-default

- A (miniQU-final): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 `
- B (miniQU-c3): `/home/ec2-user/miniqu-work/r2t2/miniQU-c3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T07:54:33), B (2026-11-23T07:55:02), A (2026-11-23T07:55:31), B (2026-11-23T07:56:00), A (2026-11-23T07:56:29), B (2026-11-23T07:56:59)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.55 | 1.57 | 1.009 | 1.49-1.61 | 1.52-1.67 | yes |
| DW-unsat-09-22-1.qcir | 6.56 | 6.69 | 1.020 | 6.34-6.93 | 6.39-6.96 | yes |
| jctc10-fail.qcir | 6.33 | 6.69 | 1.058 | 5.22-7.19 | 5.62-7.04 | yes |
| DW-sat-09-26-1.qcir | 2.21 | 2.23 | 1.007 | 1.95-2.36 | 1.97-2.37 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.31 | 9.47 | 1.017 | 8.80-9.97 | 8.95-10.00 | yes |
| 9.2.qcir | 10.53 | 10.47 | 0.994 | 10.00-11.59 | 10.03-11.36 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.43 | 11.42 | 0.999 | 10.77-12.07 | 10.79-12.14 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 7.75 | 7.75 | 1.000 | 7.47-8.15 | 7.62-8.08 | yes |
| 4.1.qcir | 6.54 | 6.61 | 1.010 | 6.28-6.64 | 6.45-6.85 | yes |
| 5.2-1.qcir | 28.40 | 28.02 | 0.986 | 27.02-28.85 | 27.21-28.82 | yes |
| hadw11-12.qcir | 5.45 | 5.60 | 1.027 | 5.32-5.68 | 5.43-5.69 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.56 | 10.71 | 1.014 | 9.91-11.19 | 10.06-11.38 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.012** |  |  |  |

