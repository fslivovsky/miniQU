# Load measurement M1-r3-load-after-dl

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -dl`
- B (new): `/home/ec2-user/miniqu-work/build/bench-M1-r3-pre/miniQU`, sha256 006221175f2fdfcbae31daaf10e01bea0ca947523c15cb5c443ea0976a0d85ad, args `--seed=1 -dl`
- placement: L3 groups, cores kept busy (every core loops over its instance until every core has completed a run; timeout 60 s per run); 2 rounds
- group 0 on cores 0,1,2,3,4,5,6,7: 8 instances
- group 1 on cores 8,9,10,11,12,13,14,15: 8 instances
- group 2 on cores 16,17,18,19,20,21,22,23: 8 instances
- group 3 on cores 24,25,26,27,28,29,30,31: 8 instances
- group 4 on cores 32,33,34,35,36,37,38,39: 8 instances
- group 5 on cores 40,41,42,43,44,45,46,47: 8 instances
- order of the arms: A (2026-11-23T17:09:22), B (2026-11-23T17:10:24), A (2026-11-23T17:11:25), B (2026-11-23T17:12:27)

User CPU seconds, median over all completed runs and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| CM-unsat-07-01-06-2.qcir | - | - | - | - | - | unfinished |
| DW-sat-08-22-1.qcir | 10.44 | 9.72 | 0.931 | 8.58-13.72 | 8.74-11.31 | yes |
| DW-sat-08-23-1.qcir | 5.92 | 4.81 | 0.813 | 4.25-6.88 | 3.81-7.47 | different search |
| DW-sat-09-26-1.qcir | 41.38 | 38.18 | 0.923 | 40.10-42.66 | 37.50-38.87 | different search |
| DW-unsat-09-22-1.qcir | 7.17 | 3.71 | 0.517 | 5.05-9.04 | 3.07-4.68 | different search |
| DW-unsat-09-23-1.qcir | 2.67 | 2.58 | 0.967 | 2.42-2.93 | 2.25-3.02 | different search |
| DW-unsat-10-25-1.qcir | 13.88 | 17.95 | 1.293 | 12.32-14.69 | 17.75-18.68 | different search |
| DW-unsat-11-26-1.qcir | - | - | - | - | - | unfinished |
| 10.1.qcir | 3.71 | 3.58 | 0.967 | 3.58-3.80 | 3.44-3.65 | yes |
| 10.2.qcir | 1.89 | 1.60 | 0.844 | 1.81-2.00 | 1.50-1.67 | yes |
| 11.1.qcir | 30.69 | 29.97 | 0.976 | 30.69-30.69 | 29.59-30.28 | yes |
| 2.1.qcir | - | - | - | - | - | unfinished |
| 2.2.qcir | - | - | - | - | - | unfinished |
| 3.1.qcir | - | - | - | - | - | unfinished |
| 3.2.qcir | 1.41 | 1.18 | 0.833 | 1.32-1.52 | 1.12-1.26 | yes |
| 4.1.qcir | 6.69 | 6.90 | 1.032 | 6.45-6.99 | 6.70-7.13 | yes |
| 5.2-1.qcir | 17.03 | 18.07 | 1.061 | 16.82-17.37 | 17.47-18.33 | yes |
| 5.2-2.qcir | - | - | - | - | - | unfinished |
| 5.2-3.qcir | - | - | - | - | - | unfinished |
| 8.1.qcir | 4.35 | 4.36 | 1.003 | 4.25-4.55 | 4.18-4.53 | yes |
| 9.1.qcir | 2.31 | 1.87 | 0.812 | 2.18-2.40 | 1.68-1.97 | yes |
| 9.2.qcir | 19.75 | 19.06 | 0.965 | 19.38-19.92 | 18.77-20.08 | yes |
| 9.3.qcir | 3.25 | 3.14 | 0.967 | 3.15-3.42 | 3.04-3.27 | yes |
| CM-sat-04-01-06-3.qcir | 31.28 | 46.05 | 1.472 | 31.14-31.42 | 45.21-46.90 | different search |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 17.93 | 17.70 | 0.987 | 17.23-19.56 | 15.92-18.51 | yes |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 4.12 | 4.12 | 0.999 | 3.59-4.40 | 3.32-4.49 | yes |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 6.73 | 6.95 | 1.032 | 6.07-7.31 | 5.71-7.70 | yes |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 2.34 | 2.16 | 0.924 | 2.02-2.86 | 1.74-2.61 | yes |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 8.25 | 8.02 | 0.971 | 7.82-9.17 | 7.06-8.72 | different search |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 24.08 | 19.11 | 0.794 | 23.15-25.16 | 17.56-21.55 | different search |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 6.02 | 5.67 | 0.942 | 5.47-6.73 | 4.89-6.44 | yes |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 5.33 | 5.10 | 0.957 | 4.76-6.00 | 4.38-5.98 | yes |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | - | - | - | - | - | unfinished |
| ex92_7S700.qcir | - | - | - | - | - | unfinished |
| finan01-finan01_mov.qcir | - | - | - | - | - | unfinished |
| finan01_mov-finan01.qcir | - | - | - | - | - | unfinished |
| finding_nemo_1.tlsf.qcir | 7.12 | 6.70 | 0.941 | 6.66-7.50 | 6.25-7.40 | yes |
| genbuf10b4n.unsat.qcir | - | - | - | - | - | unfinished |
| genbuf9b4n.unsat.qcir | - | - | - | - | - | unfinished |
| hadw10-11.qcir | 41.33 | 34.85 | 0.843 | 41.20-41.46 | 34.69-35.01 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| **geometric mean** (n=19 identical searches) |  |  | **0.946** |  |  |  |

Per group (geometric mean of B / A over the identical searches of the group):

| group | first instance | chosen as | n | geometric mean B / A |
|---|---:|---:|---:|---:|
| 0 | CM-unsat-07-01-06-2.qcir | CM/DW (mandatory). Reviewer's L3 reproducer of round 2: DW-sat/unsat 08-22 ... 11-26 run 1.14-1.27 times slower in benchmark runs; 6 instances with identical searches at 2-52 s. | 1 | 0.931 |
| 1 | 10.1.qcir | numeric, the 4.1 region (10.1 ... 4.1): 6 instances with identical searches at 1.1-43 s, long numeric runs next to short ones. | 5 | 0.927 |
| 2 | 5.2-1.qcir | numeric, the 5.2-1 region (5.2-1 ... CM-sat-04-01-06-3): 4 instances with identical searches (8.1, 9.1, 9.2, 9.3) at 2-17 s. No third family has a window with three qualifying instances, so this is a second numeric window. | 5 | 0.958 |
| 3 | chess_solving_mate_in_2_1982_WCSC-6_02.qcir | chess mate_in_2 (1982 ... 2002): 3 instances with identical searches at 1.2-1.4 s, short runs that change often. | 6 | 0.973 |
| 4 | chess_solving_mate_in_3_2001_UKR-CH_06.qcir | chess mate_in_3 (2001_UKR-CH_06 ... 2014_FRA-CH_03): 6 instances with identical searches at 5-13 s, contains chess_solving_mate_in_3_2014_FRA-CH_03. | 0 | - |
| 5 | ex92_7S700.qcir | hadw10-11, hadw11-12 with ex, finan, finding_nemo and genbuf neighbours: 3 instances with identical searches (finding_nemo_1, hadw10-11, hadw11-12) at 3-12 s. | 2 | 0.891 |

Unfinished (timeout or unexpected exit code, excluded): CM-unsat-07-01-06-2.qcir, DW-unsat-11-26-1.qcir, 2.1.qcir, 2.2.qcir, 3.1.qcir, 5.2-2.qcir, 5.2-3.qcir, chess_solving_mate_in_3_2001_UKR-CH_06.qcir, chess_solving_mate_in_3_2003_UKR-CH_04.qcir, chess_solving_mate_in_3_2008_ISC-4B_07.qcir, chess_solving_mate_in_3_2010_UKR-CH_04.qcir, chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir, chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir, chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir, chess_solving_mate_in_3_2014_FRA-CH_03.qcir, ex92_7S700.qcir, finan01-finan01_mov.qcir, finan01_mov-finan01.qcir, genbuf10b4n.unsat.qcir, genbuf9b4n.unsat.qcir, hadw11-12.qcir

