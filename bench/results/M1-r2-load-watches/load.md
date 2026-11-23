# Load measurement M1-r2-load-watches

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 `
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T06:04:06), B (2026-11-23T06:04:40), A (2026-11-23T06:05:09), B (2026-11-23T06:05:42), A (2026-11-23T06:06:11), B (2026-11-23T06:06:44)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 2.05 | 1.57 | 0.764 | 1.90-3.02 | 1.49-1.61 | yes |
| DW-unsat-09-22-1.qcir | 8.99 | 6.62 | 0.737 | 8.24-10.65 | 6.33-6.98 | yes |
| jctc10-fail.qcir | 7.10 | 6.25 | 0.881 | 5.93-8.06 | 5.22-7.03 | yes |
| DW-sat-09-26-1.qcir | 3.92 | 2.17 | 0.552 | 3.59-4.09 | 1.96-2.38 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.91 | 9.29 | 0.937 | 8.92-11.06 | 8.73-9.79 | yes |
| 9.2.qcir | 13.85 | 10.74 | 0.775 | 12.62-15.19 | 10.02-11.42 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.57 | 11.47 | 0.912 | 11.15-13.28 | 10.68-12.02 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.30 | 7.77 | 0.936 | 7.34-9.77 | 7.51-7.98 | yes |
| 4.1.qcir | 8.22 | 6.53 | 0.794 | 8.00-8.35 | 6.37-6.80 | yes |
| 5.2-1.qcir | 31.68 | 27.90 | 0.881 | 30.77-32.81 | 27.12-28.86 | yes |
| hadw11-12.qcir | 6.28 | 5.46 | 0.871 | 6.00-6.88 | 5.35-5.69 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.25 | 10.57 | 0.863 | 11.49-13.73 | 10.14-11.11 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.818** |  |  |  |

