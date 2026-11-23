# Load measurement c2-default

- A (miniQU-new): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 `
- B (miniQU-c2): `/home/ec2-user/miniqu-work/r2t2/miniQU-c2`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T05:59:41), B (2026-11-23T06:00:11), A (2026-11-23T06:00:40), B (2026-11-23T06:01:09), A (2026-11-23T06:01:38), B (2026-11-23T06:02:08)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.85 | 1.57 | 0.849 | 1.64-2.90 | 1.50-1.66 | yes |
| DW-unsat-09-22-1.qcir | 9.43 | 6.58 | 0.697 | 7.98-11.08 | 6.30-6.95 | yes |
| jctc10-fail.qcir | 7.56 | 6.42 | 0.849 | 7.22-9.06 | 5.55-6.99 | yes |
| DW-sat-09-26-1.qcir | 3.22 | 2.18 | 0.677 | 3.09-3.46 | 1.94-2.41 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.36 | 9.20 | 0.983 | 8.69-10.96 | 8.73-9.96 | yes |
| 9.2.qcir | 12.58 | 10.51 | 0.835 | 11.68-13.45 | 9.93-11.61 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.59 | 11.55 | 0.996 | 10.57-13.37 | 10.72-12.17 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.05 | 7.72 | 0.959 | 6.94-8.39 | 7.47-8.16 | yes |
| 4.1.qcir | 7.20 | 6.55 | 0.910 | 7.03-7.35 | 6.29-6.66 | yes |
| 5.2-1.qcir | 28.27 | 27.89 | 0.987 | 27.38-29.27 | 27.08-28.82 | yes |
| hadw11-12.qcir | 5.48 | 5.47 | 0.999 | 5.19-5.83 | 5.36-5.73 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.93 | 10.44 | 0.955 | 10.06-12.04 | 10.07-11.21 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.884** |  |  |  |

