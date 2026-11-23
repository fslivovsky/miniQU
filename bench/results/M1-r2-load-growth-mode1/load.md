# Load measurement M1-r2-load-growth-mode1

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T08:41:27), B (2026-11-23T08:46:27), A (2026-11-23T08:51:28), B (2026-11-23T08:56:29), A (2026-11-23T09:01:29), B (2026-11-23T09:06:30)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.66 | 1.38 | 0.834 | 1.53-2.79 | 1.33-1.43 | yes |
| DW-unsat-09-22-1.qcir | 9.64 | 6.69 | 0.694 | 7.32-12.10 | 6.43-7.09 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 6.76 | 4.21 | 0.622 | 5.02-8.52 | 3.81-4.62 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 28.09 | 25.89 | 0.922 | 27.19-29.17 | 25.62-26.04 | different search |
| 9.2.qcir | 16.13 | 12.13 | 0.752 | 15.33-16.70 | 11.83-12.28 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.48 | 2.69 | 1.085 | 2.21-3.02 | 2.52-2.86 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.18 | 11.11 | 0.993 | 10.74-12.16 | 10.79-11.26 | different search |
| 4.1.qcir | 7.00 | 5.63 | 0.804 | 6.85-7.43 | 5.40-5.75 | yes |
| 5.2-1.qcir | 20.30 | 17.94 | 0.884 | 19.63-21.05 | 17.51-18.37 | yes |
| hadw11-12.qcir | 8.88 | 7.62 | 0.858 | 8.44-9.01 | 7.35-7.80 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.07 | 10.20 | 0.922 | 10.66-12.48 | 10.04-10.38 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **0.819** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

