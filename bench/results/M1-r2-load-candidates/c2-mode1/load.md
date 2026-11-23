# Load measurement c2-mode1

- A (miniQU-new): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 -mode=1`
- B (miniQU-c2): `/home/ec2-user/miniqu-work/r2t2/miniQU-c2`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T05:53:38), B (2026-11-23T05:54:38), A (2026-11-23T05:55:39), B (2026-11-23T05:56:39), A (2026-11-23T05:57:40), B (2026-11-23T05:58:41)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.85 | 1.42 | 0.768 | 1.48-2.92 | 1.34-1.55 | yes |
| DW-unsat-09-22-1.qcir | 10.00 | 7.09 | 0.709 | 7.94-11.43 | 6.66-7.81 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 7.14 | 4.39 | 0.615 | 6.20-7.86 | 3.93-5.22 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.59 | 27.11 | 0.983 | 26.49-28.26 | 26.51-27.47 | yes |
| 9.2.qcir | 15.54 | 12.87 | 0.828 | 14.67-15.85 | 12.65-13.14 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.53 | 2.78 | 1.098 | 2.21-2.88 | 2.67-2.96 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.42 | 11.56 | 1.012 | 9.90-13.08 | 11.05-11.79 | yes |
| 4.1.qcir | 6.57 | 6.01 | 0.915 | 6.42-6.79 | 5.80-6.26 | yes |
| 5.2-1.qcir | 19.54 | 19.22 | 0.984 | 18.87-20.52 | 18.55-19.74 | yes |
| hadw11-12.qcir | 8.30 | 8.20 | 0.988 | 7.97-8.84 | 8.00-8.33 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.27 | 10.59 | 1.031 | 9.69-12.42 | 9.80-10.67 | yes |
| **geometric mean** (n=11 identical searches) |  |  | **0.890** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

