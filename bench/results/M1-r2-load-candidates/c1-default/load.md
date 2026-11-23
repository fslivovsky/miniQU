# Load measurement c1-default

- A (miniQU-new): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 `
- B (miniQU-c1): `/home/ec2-user/miniqu-work/r2t2/miniQU-c1`, sha256 022946a7e6d3a543b54b553a7e367b2fc2a38275d0370d4aa754530342d619fe, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T05:49:52), B (2026-11-23T05:50:21), A (2026-11-23T05:50:51), B (2026-11-23T05:51:21), A (2026-11-23T05:51:50), B (2026-11-23T05:52:20)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 2.18 | 1.82 | 0.834 | 1.61-3.24 | 1.61-3.35 | yes |
| DW-unsat-09-22-1.qcir | 9.90 | 9.79 | 0.989 | 8.56-10.73 | 8.11-10.41 | yes |
| jctc10-fail.qcir | 8.30 | 7.86 | 0.947 | 7.04-9.20 | 6.11-8.83 | yes |
| DW-sat-09-26-1.qcir | 3.24 | 3.17 | 0.977 | 3.04-3.46 | 3.04-3.48 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.49 | 9.84 | 1.037 | 8.63-11.02 | 8.51-10.58 | yes |
| 9.2.qcir | 12.61 | 12.62 | 1.001 | 11.75-13.43 | 11.82-13.52 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.86 | 11.94 | 1.007 | 10.66-12.66 | 10.63-13.33 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 7.57 | 7.73 | 1.021 | 6.92-9.15 | 7.13-8.36 | yes |
| 4.1.qcir | 7.26 | 7.39 | 1.017 | 7.07-7.58 | 7.14-7.64 | yes |
| 5.2-1.qcir | 28.21 | 28.57 | 1.013 | 27.37-29.01 | 27.73-29.57 | yes |
| hadw11-12.qcir | 5.36 | 5.42 | 1.012 | 5.10-5.82 | 5.09-5.84 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.64 | 10.70 | 1.006 | 10.08-12.02 | 10.19-12.96 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.987** |  |  |  |

