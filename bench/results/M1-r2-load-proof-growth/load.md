# Load measurement M1-r2-load-proof-growth

- A (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1`
- B (new-r2-proof): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 -proof=/dev/null -proof-binary`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T09:11:47), B (2026-11-23T09:12:16), A (2026-11-23T09:12:48), B (2026-11-23T09:13:17), A (2026-11-23T09:13:49), B (2026-11-23T09:14:19)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.58 | 1.75 | 1.109 | 1.51-1.65 | 1.67-1.93 | yes |
| DW-unsat-09-22-1.qcir | 6.61 | 7.40 | 1.119 | 6.38-6.95 | 6.89-7.78 | yes |
| jctc10-fail.qcir | 6.65 | 7.20 | 1.082 | 5.81-6.89 | 5.29-7.78 | yes |
| DW-sat-09-26-1.qcir | 2.17 | 2.53 | 1.161 | 1.97-2.40 | 2.30-2.72 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.32 | 10.32 | 1.108 | 8.91-10.09 | 9.79-10.83 | yes |
| 9.2.qcir | 10.63 | 11.51 | 1.083 | 10.06-11.43 | 11.04-12.76 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.40 | 12.58 | 1.104 | 10.85-12.22 | 11.98-13.33 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 7.73 | 8.58 | 1.110 | 7.50-8.28 | 8.28-8.83 | yes |
| 4.1.qcir | 6.65 | 7.09 | 1.065 | 6.32-6.70 | 6.80-7.35 | yes |
| 5.2-1.qcir | 27.98 | 30.24 | 1.081 | 27.21-29.24 | 29.42-31.34 | yes |
| hadw11-12.qcir | 5.57 | 6.01 | 1.080 | 5.46-5.75 | 5.88-6.26 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.70 | 11.58 | 1.082 | 10.13-11.29 | 10.83-12.13 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.099** |  |  |  |

