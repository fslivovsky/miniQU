# Load measurement M1-r2-load-layout

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 `
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T03:53:57), B (2026-11-23T03:54:30), A (2026-11-23T03:54:59), B (2026-11-23T03:55:32), A (2026-11-23T03:56:02), B (2026-11-23T03:56:35)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 2.15 | 2.07 | 0.965 | 1.88-3.46 | 1.59-2.78 | yes |
| DW-unsat-09-22-1.qcir | 9.91 | 9.61 | 0.970 | 8.35-10.84 | 8.32-10.49 | yes |
| jctc10-fail.qcir | 7.34 | 8.22 | 1.120 | 6.04-8.42 | 6.40-9.47 | yes |
| DW-sat-09-26-1.qcir | 3.92 | 3.20 | 0.816 | 3.14-4.11 | 2.99-3.55 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.85 | 9.60 | 0.975 | 8.53-10.64 | 8.55-10.20 | yes |
| 9.2.qcir | 13.81 | 12.60 | 0.912 | 12.52-15.19 | 11.69-13.27 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.53 | 11.87 | 0.948 | 11.38-13.83 | 10.62-12.58 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.00 | 7.98 | 0.997 | 7.31-8.91 | 6.90-8.58 | yes |
| 4.1.qcir | 8.20 | 7.30 | 0.891 | 8.03-8.46 | 6.99-7.61 | yes |
| 5.2-1.qcir | 31.69 | 28.51 | 0.900 | 30.70-32.86 | 27.47-29.26 | yes |
| hadw11-12.qcir | 6.30 | 5.44 | 0.864 | 6.00-6.77 | 5.07-6.35 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.33 | 10.87 | 0.882 | 11.47-13.53 | 10.12-11.29 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.934** |  |  |  |

