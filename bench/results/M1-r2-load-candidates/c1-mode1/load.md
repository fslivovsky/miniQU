# Load measurement c1-mode1

- A (miniQU-new): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 -mode=1`
- B (miniQU-c1): `/home/ec2-user/miniqu-work/r2t2/miniQU-c1`, sha256 022946a7e6d3a543b54b553a7e367b2fc2a38275d0370d4aa754530342d619fe, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T05:43:48), B (2026-11-23T05:44:49), A (2026-11-23T05:45:50), B (2026-11-23T05:46:50), A (2026-11-23T05:47:51), B (2026-11-23T05:48:51)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 2.36 | 1.68 | 0.713 | 1.46-2.97 | 1.45-2.76 | yes |
| DW-unsat-09-22-1.qcir | 10.02 | 9.93 | 0.991 | 8.03-11.48 | 7.82-11.65 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 7.30 | 7.25 | 0.993 | 6.37-7.94 | 6.61-7.83 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.71 | 27.89 | 1.006 | 26.26-28.98 | 26.99-29.63 | yes |
| 9.2.qcir | 15.26 | 15.32 | 1.004 | 14.84-15.91 | 15.06-15.97 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.51 | 2.69 | 1.068 | 2.32-2.95 | 2.43-2.88 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.34 | 11.38 | 1.003 | 10.08-13.13 | 10.13-12.06 | yes |
| 4.1.qcir | 6.50 | 6.60 | 1.016 | 6.39-6.70 | 6.48-6.81 | yes |
| 5.2-1.qcir | 19.66 | 19.67 | 1.001 | 18.70-20.46 | 19.00-20.22 | yes |
| hadw11-12.qcir | 8.23 | 8.15 | 0.990 | 7.86-8.75 | 7.74-8.82 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.26 | 10.24 | 0.998 | 9.94-12.51 | 9.76-10.51 | yes |
| **geometric mean** (n=11 identical searches) |  |  | **0.976** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

