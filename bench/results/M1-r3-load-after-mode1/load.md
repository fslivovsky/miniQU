# Load measurement M1-r3-load-after-mode1

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new): `/home/ec2-user/miniqu-work/build/bench-M1-r3-pre/miniQU`, sha256 006221175f2fdfcbae31daaf10e01bea0ca947523c15cb5c443ea0976a0d85ad, args `--seed=1 -mode=1`
- placement: L3 groups, cores kept busy (every core loops over its instance until every core has completed a run; timeout 60 s per run); 2 rounds
- group 0 on cores 0,1,2,3,4,5,6,7: 8 instances
- group 1 on cores 8,9,10,11,12,13,14,15: 8 instances
- group 2 on cores 16,17,18,19,20,21,22,23: 8 instances
- group 3 on cores 24,25,26,27,28,29,30,31: 8 instances
- group 4 on cores 32,33,34,35,36,37,38,39: 8 instances
- group 5 on cores 40,41,42,43,44,45,46,47: 8 instances
- order of the arms: A (2026-11-23T17:13:29), B (2026-11-23T17:14:31), A (2026-11-23T17:15:32), B (2026-11-23T17:16:34)

User CPU seconds, median over all completed runs and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| CM-unsat-07-01-06-2.qcir | - | - | - | - | - | unfinished |
| DW-sat-08-22-1.qcir | 1.70 | 1.62 | 0.951 | 1.55-2.53 | 1.53-2.69 | yes |
| DW-sat-08-23-1.qcir | 1.53 | 1.55 | 1.011 | 1.40-2.65 | 1.38-2.79 | yes |
| DW-sat-09-26-1.qcir | 8.14 | 8.18 | 1.004 | 6.45-8.57 | 7.35-8.47 | yes |
| DW-unsat-09-22-1.qcir | 11.75 | 15.61 | 1.329 | 8.81-17.26 | 13.28-17.24 | yes |
| DW-unsat-09-23-1.qcir | 18.22 | 20.41 | 1.120 | 14.34-19.13 | 17.03-20.79 | yes |
| DW-unsat-10-25-1.qcir | - | - | - | - | - | unfinished |
| DW-unsat-11-26-1.qcir | - | - | - | - | - | unfinished |
| 10.1.qcir | 2.02 | 1.79 | 0.883 | 1.92-2.11 | 1.68-1.87 | yes |
| 10.2.qcir | 1.48 | 1.14 | 0.768 | 1.40-1.56 | 1.06-1.22 | yes |
| 11.1.qcir | 33.03 | 35.48 | 1.074 | 33.01-33.05 | 35.41-35.55 | yes |
| 2.1.qcir | - | - | - | - | - | unfinished |
| 2.2.qcir | - | - | - | - | - | unfinished |
| 3.1.qcir | 43.28 | 45.72 | 1.056 | 43.14-43.43 | 45.67-45.77 | yes |
| 3.2.qcir | 1.02 | 0.78 | 0.766 | 0.95-1.10 | 0.70-0.84 | yes |
| 4.1.qcir | 7.17 | 8.08 | 1.128 | 7.05-7.64 | 7.84-8.42 | yes |
| 5.2-1.qcir | 27.91 | 30.93 | 1.108 | 27.43-28.89 | 30.50-31.36 | yes |
| 5.2-2.qcir | - | - | - | - | - | unfinished |
| 5.2-3.qcir | - | - | - | - | - | unfinished |
| 8.1.qcir | 3.94 | 4.26 | 1.081 | 3.83-4.09 | 4.17-4.55 | yes |
| 9.1.qcir | 1.97 | 1.58 | 0.802 | 1.88-2.12 | 1.47-1.68 | yes |
| 9.2.qcir | 19.05 | 20.43 | 1.072 | 18.79-19.44 | 20.39-20.61 | yes |
| 9.3.qcir | 2.40 | 2.49 | 1.038 | 2.29-2.52 | 2.40-2.56 | yes |
| CM-sat-04-01-06-3.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.36 | 1.36 | 1.001 | 1.27-1.75 | 1.30-1.75 | yes |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 0.58 | 0.56 | 0.951 | 0.51-0.71 | 0.51-0.66 | yes |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 0.73 | 0.70 | 0.967 | 0.60-0.89 | 0.64-0.88 | yes |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 0.77 | 0.75 | 0.982 | 0.68-0.98 | 0.71-0.96 | yes |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.53 | 0.50 | 0.936 | 0.45-0.66 | 0.43-0.65 | yes |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 0.71 | 0.68 | 0.963 | 0.66-0.93 | 0.61-0.86 | yes |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 0.27 | 0.23 | 0.846 | 0.22-0.31 | 0.18-0.29 | yes |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.64 | 0.61 | 0.953 | 0.59-0.81 | 0.57-0.76 | yes |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 14.47 | 17.40 | 1.203 | 13.81-16.37 | 15.26-18.81 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 44.50 | 44.53 | 1.001 | 42.72-46.29 | 43.50-45.56 | different search |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 5.25 | 5.91 | 1.127 | 4.69-5.57 | 5.64-6.41 | different search |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 2.84 | 2.93 | 1.032 | 2.53-3.24 | 2.74-3.56 | yes |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 17.39 | 18.32 | 1.053 | 15.96-19.61 | 17.62-21.82 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.35 | 2.46 | 1.047 | 2.06-2.85 | 2.24-3.00 | yes |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 8.53 | 8.91 | 1.044 | 8.05-9.80 | 8.57-9.26 | yes |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 18.11 | 18.41 | 1.017 | 16.23-19.37 | 17.66-19.62 | yes |
| ex92_7S700.qcir | - | - | - | - | - | unfinished |
| finan01-finan01_mov.qcir | - | - | - | - | - | unfinished |
| finan01_mov-finan01.qcir | - | - | - | - | - | unfinished |
| finding_nemo_1.tlsf.qcir | 11.20 | 9.98 | 0.892 | 10.81-12.55 | 9.71-10.43 | different search |
| genbuf10b4n.unsat.qcir | - | - | - | - | - | unfinished |
| genbuf9b4n.unsat.qcir | - | - | - | - | - | unfinished |
| hadw10-11.qcir | 1.70 | 1.77 | 1.042 | 1.58-1.90 | 1.58-1.94 | yes |
| hadw11-12.qcir | 7.70 | 7.05 | 0.915 | 7.37-8.08 | 6.82-7.77 | yes |
| **geometric mean** (n=32 identical searches) |  |  | **0.998** |  |  |  |

Per group (geometric mean of B / A over the identical searches of the group):

| group | first instance | chosen as | n | geometric mean B / A |
|---|---:|---:|---:|---:|
| 0 | CM-unsat-07-01-06-2.qcir | CM/DW (mandatory). Reviewer's L3 reproducer of round 2: DW-sat/unsat 08-22 ... 11-26 run 1.14-1.27 times slower in benchmark runs; 6 instances with identical searches at 2-52 s. | 5 | 1.075 |
| 1 | 10.1.qcir | numeric, the 4.1 region (10.1 ... 4.1): 6 instances with identical searches at 1.1-43 s, long numeric runs next to short ones. | 6 | 0.934 |
| 2 | 5.2-1.qcir | numeric, the 5.2-1 region (5.2-1 ... CM-sat-04-01-06-3): 4 instances with identical searches (8.1, 9.1, 9.2, 9.3) at 2-17 s. No third family has a window with three qualifying instances, so this is a second numeric window. | 5 | 1.014 |
| 3 | chess_solving_mate_in_2_1982_WCSC-6_02.qcir | chess mate_in_2 (1982 ... 2002): 3 instances with identical searches at 1.2-1.4 s, short runs that change often. | 8 | 0.949 |
| 4 | chess_solving_mate_in_3_2001_UKR-CH_06.qcir | chess mate_in_3 (2001_UKR-CH_06 ... 2014_FRA-CH_03): 6 instances with identical searches at 5-13 s, contains chess_solving_mate_in_3_2014_FRA-CH_03. | 6 | 1.064 |
| 5 | ex92_7S700.qcir | hadw10-11, hadw11-12 with ex, finan, finding_nemo and genbuf neighbours: 3 instances with identical searches (finding_nemo_1, hadw10-11, hadw11-12) at 3-12 s. | 2 | 0.977 |

Unfinished (timeout or unexpected exit code, excluded): CM-unsat-07-01-06-2.qcir, DW-unsat-10-25-1.qcir, DW-unsat-11-26-1.qcir, 2.1.qcir, 2.2.qcir, 5.2-2.qcir, 5.2-3.qcir, CM-sat-04-01-06-3.qcir, ex92_7S700.qcir, finan01-finan01_mov.qcir, finan01_mov-finan01.qcir, genbuf10b4n.unsat.qcir, genbuf9b4n.unsat.qcir

