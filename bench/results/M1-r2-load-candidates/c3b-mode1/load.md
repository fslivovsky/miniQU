# Load measurement c3b-mode1

- A (miniQU-final): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 -mode=1`
- B (miniQU-c3): `/home/ec2-user/miniqu-work/r2t2/miniQU-c3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T08:00:45), B (2026-11-23T08:01:46), A (2026-11-23T08:02:46), B (2026-11-23T08:03:47), A (2026-11-23T08:04:47), B (2026-11-23T08:05:48)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.44 | 1.37 | 0.948 | 1.36-1.58 | 1.28-1.45 | yes |
| DW-unsat-09-22-1.qcir | 7.16 | 6.76 | 0.943 | 6.73-7.94 | 6.13-7.14 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 4.52 | 4.25 | 0.940 | 3.89-5.24 | 3.63-4.76 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.17 | 25.84 | 0.951 | 26.88-27.46 | 25.56-26.34 | yes |
| 9.2.qcir | 13.05 | 11.99 | 0.919 | 12.55-13.36 | 11.78-12.29 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.81 | 2.67 | 0.952 | 2.66-2.96 | 2.52-2.85 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.53 | 11.05 | 0.958 | 11.09-11.77 | 10.92-11.34 | yes |
| 4.1.qcir | 5.99 | 5.64 | 0.942 | 5.77-6.19 | 5.52-5.77 | yes |
| 5.2-1.qcir | 19.31 | 18.06 | 0.935 | 18.70-19.68 | 17.48-18.43 | yes |
| hadw11-12.qcir | 8.12 | 7.63 | 0.940 | 7.95-8.89 | 7.49-7.76 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.57 | 10.21 | 0.966 | 9.66-11.05 | 9.65-10.49 | yes |
| **geometric mean** (n=11 identical searches) |  |  | **0.945** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

