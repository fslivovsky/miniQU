# Load measurement c3-mode1

- A (miniQU-final): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 -mode=1`
- B (miniQU-c3): `/home/ec2-user/miniqu-work/r2t2/miniQU-c3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T07:48:29), B (2026-11-23T07:49:30), A (2026-11-23T07:50:30), B (2026-11-23T07:51:31), A (2026-11-23T07:52:31), B (2026-11-23T07:53:32)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.42 | 1.35 | 0.949 | 1.34-1.53 | 1.30-1.46 | yes |
| DW-unsat-09-22-1.qcir | 7.14 | 6.69 | 0.937 | 6.57-7.76 | 6.46-7.25 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 4.33 | 4.18 | 0.965 | 3.79-5.02 | 3.75-4.72 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.08 | 25.77 | 0.952 | 26.17-27.39 | 25.64-26.32 | yes |
| 9.2.qcir | 12.84 | 12.08 | 0.941 | 12.58-13.20 | 11.89-12.27 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.79 | 2.68 | 0.961 | 2.67-2.94 | 2.54-2.88 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.43 | 11.07 | 0.968 | 10.78-11.64 | 10.80-11.29 | yes |
| 4.1.qcir | 5.96 | 5.61 | 0.941 | 5.73-6.30 | 5.36-5.79 | yes |
| 5.2-1.qcir | 19.35 | 17.96 | 0.928 | 18.67-19.83 | 17.36-18.37 | yes |
| hadw11-12.qcir | 8.20 | 7.64 | 0.932 | 7.96-8.37 | 7.50-7.90 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.63 | 10.13 | 0.953 | 9.85-12.77 | 9.33-10.30 | yes |
| **geometric mean** (n=11 identical searches) |  |  | **0.948** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

