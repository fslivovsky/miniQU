# Load measurement M1-r3-load-after

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 `
- B (new): `/home/ec2-user/miniqu-work/build/bench-M1-r3-pre/miniQU`, sha256 006221175f2fdfcbae31daaf10e01bea0ca947523c15cb5c443ea0976a0d85ad, args `--seed=1 `
- placement: L3 groups, cores kept busy (every core loops over its instance until every core has completed a run; timeout 60 s per run); 2 rounds
- group 0 on cores 0,1,2,3,4,5,6,7: 8 instances
- group 1 on cores 8,9,10,11,12,13,14,15: 8 instances
- group 2 on cores 16,17,18,19,20,21,22,23: 8 instances
- group 3 on cores 24,25,26,27,28,29,30,31: 8 instances
- group 4 on cores 32,33,34,35,36,37,38,39: 8 instances
- group 5 on cores 40,41,42,43,44,45,46,47: 8 instances
- order of the arms: A (2026-11-23T17:05:16), B (2026-11-23T17:06:17), A (2026-11-23T17:07:19), B (2026-11-23T17:08:21)

User CPU seconds, median over all completed runs and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| CM-unsat-07-01-06-2.qcir | - | - | - | - | - | unfinished |
| DW-sat-08-22-1.qcir | 2.03 | 1.96 | 0.968 | 1.88-3.41 | 1.82-3.05 | yes |
| DW-sat-08-23-1.qcir | 1.61 | 1.54 | 0.958 | 1.48-2.51 | 1.38-2.52 | yes |
| DW-sat-09-26-1.qcir | 3.87 | 3.62 | 0.937 | 3.58-4.07 | 2.85-3.92 | yes |
| DW-unsat-09-22-1.qcir | 16.64 | 17.49 | 1.051 | 14.83-18.26 | 15.70-17.89 | yes |
| DW-unsat-09-23-1.qcir | 28.66 | 29.73 | 1.037 | 26.65-31.16 | 28.15-30.87 | yes |
| DW-unsat-10-25-1.qcir | 51.26 | 53.42 | 1.042 | 48.50-54.03 | 51.74-55.10 | yes |
| DW-unsat-11-26-1.qcir | - | - | - | - | - | unfinished |
| 10.1.qcir | 2.01 | 1.76 | 0.875 | 1.90-2.15 | 1.63-1.84 | yes |
| 10.2.qcir | 1.46 | 1.11 | 0.765 | 1.36-1.59 | 1.03-1.19 | yes |
| 11.1.qcir | 28.48 | 28.83 | 1.012 | 28.22-28.76 | 28.67-28.89 | yes |
| 2.1.qcir | - | - | - | - | - | unfinished |
| 2.2.qcir | - | - | - | - | - | unfinished |
| 3.1.qcir | 43.40 | 43.89 | 1.011 | 43.21-43.59 | 43.78-43.99 | yes |
| 3.2.qcir | 1.01 | 0.76 | 0.755 | 0.93-1.10 | 0.67-0.83 | yes |
| 4.1.qcir | 8.33 | 9.10 | 1.092 | 8.07-8.46 | 9.00-9.59 | yes |
| 5.2-1.qcir | - | - | - | - | - | unfinished |
| 5.2-2.qcir | - | - | - | - | - | unfinished |
| 5.2-3.qcir | - | - | - | - | - | unfinished |
| 8.1.qcir | 3.75 | 3.84 | 1.024 | 3.65-3.90 | 3.67-3.96 | yes |
| 9.1.qcir | 2.19 | 1.77 | 0.810 | 2.09-2.33 | 1.68-1.90 | yes |
| 9.2.qcir | 17.11 | 17.73 | 1.036 | 16.72-17.93 | 17.45-18.27 | yes |
| 9.3.qcir | 2.40 | 2.42 | 1.010 | 2.24-2.48 | 2.29-2.67 | yes |
| CM-sat-04-01-06-3.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.39 | 1.31 | 0.947 | 1.30-1.67 | 1.26-1.61 | yes |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 0.57 | 0.53 | 0.931 | 0.51-0.65 | 0.47-0.61 | yes |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 0.63 | 0.58 | 0.924 | 0.57-0.77 | 0.53-0.72 | yes |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.54 | 1.49 | 0.969 | 1.46-1.97 | 1.41-1.91 | yes |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.62 | 0.55 | 0.890 | 0.52-0.76 | 0.48-0.76 | yes |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.28 | 1.21 | 0.945 | 1.18-1.58 | 1.15-1.58 | yes |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 0.25 | 0.21 | 0.820 | 0.22-0.30 | 0.17-0.25 | yes |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.58 | 0.52 | 0.904 | 0.52-0.70 | 0.48-0.64 | yes |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 7.16 | 7.14 | 0.998 | 6.57-8.36 | 6.79-8.51 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.77 | 10.35 | 1.059 | 8.83-10.55 | 9.43-11.38 | yes |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 4.17 | 5.50 | 1.320 | 3.52-4.35 | 5.05-5.94 | different search |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 4.81 | 4.77 | 0.993 | 4.35-5.68 | 4.46-5.57 | yes |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 11.77 | 16.30 | 1.385 | 10.47-13.11 | 16.23-16.51 | different search |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 14.89 | 13.47 | 0.905 | 12.87-16.41 | 12.84-16.83 | yes |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 6.73 | 6.41 | 0.953 | 5.75-7.36 | 6.01-7.67 | yes |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 16.03 | 14.34 | 0.895 | 13.74-17.28 | 13.39-17.94 | yes |
| ex92_7S700.qcir | - | - | - | - | - | unfinished |
| finan01-finan01_mov.qcir | - | - | - | - | - | unfinished |
| finan01_mov-finan01.qcir | - | - | - | - | - | unfinished |
| finding_nemo_1.tlsf.qcir | 14.87 | 13.05 | 0.878 | 13.71-15.73 | 12.57-15.33 | yes |
| genbuf10b4n.unsat.qcir | - | - | - | - | - | unfinished |
| genbuf9b4n.unsat.qcir | - | - | - | - | - | unfinished |
| hadw10-11.qcir | 3.42 | 3.18 | 0.930 | 3.23-3.80 | 2.96-3.36 | yes |
| hadw11-12.qcir | 5.39 | 5.17 | 0.959 | 5.09-5.71 | 4.80-5.49 | yes |
| **geometric mean** (n=33 identical searches) |  |  | **0.944** |  |  |  |

Per group (geometric mean of B / A over the identical searches of the group):

| group | first instance | chosen as | n | geometric mean B / A |
|---|---:|---:|---:|---:|
| 0 | CM-unsat-07-01-06-2.qcir | CM/DW (mandatory). Reviewer's L3 reproducer of round 2: DW-sat/unsat 08-22 ... 11-26 run 1.14-1.27 times slower in benchmark runs; 6 instances with identical searches at 2-52 s. | 6 | 0.998 |
| 1 | 10.1.qcir | numeric, the 4.1 region (10.1 ... 4.1): 6 instances with identical searches at 1.1-43 s, long numeric runs next to short ones. | 6 | 0.909 |
| 2 | 5.2-1.qcir | numeric, the 5.2-1 region (5.2-1 ... CM-sat-04-01-06-3): 4 instances with identical searches (8.1, 9.1, 9.2, 9.3) at 2-17 s. No third family has a window with three qualifying instances, so this is a second numeric window. | 4 | 0.965 |
| 3 | chess_solving_mate_in_2_1982_WCSC-6_02.qcir | chess mate_in_2 (1982 ... 2002): 3 instances with identical searches at 1.2-1.4 s, short runs that change often. | 8 | 0.915 |
| 4 | chess_solving_mate_in_3_2001_UKR-CH_06.qcir | chess mate_in_3 (2001_UKR-CH_06 ... 2014_FRA-CH_03): 6 instances with identical searches at 5-13 s, contains chess_solving_mate_in_3_2014_FRA-CH_03. | 6 | 0.965 |
| 5 | ex92_7S700.qcir | hadw10-11, hadw11-12 with ex, finan, finding_nemo and genbuf neighbours: 3 instances with identical searches (finding_nemo_1, hadw10-11, hadw11-12) at 3-12 s. | 3 | 0.922 |

Unfinished (timeout or unexpected exit code, excluded): CM-unsat-07-01-06-2.qcir, DW-unsat-11-26-1.qcir, 2.1.qcir, 2.2.qcir, 5.2-1.qcir, 5.2-2.qcir, 5.2-3.qcir, CM-sat-04-01-06-3.qcir, ex92_7S700.qcir, finan01-finan01_mov.qcir, finan01_mov-finan01.qcir, genbuf10b4n.unsat.qcir, genbuf9b4n.unsat.qcir

