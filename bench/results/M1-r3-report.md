# M1 round 3 benchmark report (head 46874d9, binary built as `build/bench-M1-r3`, source identical to b2018c1)

Machine: 96 cores, timed jobs on cores 48-95 (48 jobs, 8 GB, timeout 60 s, seeds 1-3 for default and `-dl`, seed 1 for
modes). Same-machine baselines `baseline-c96-<cfg>-t60-s*` (frozen c39005a binary) were reused: their `meta.json`
(jobs 48, cores 48-95, mem 8, timeout 60, 376 instances, same instance hash) matches. Run order: M1-r3-default-s1..s3,
dl-s1..s3, mode1, mode2, ccmin3, back to back (about 6 min each, nothing else running on the benchmark cores).
The M1-r2 results (same machine, same settings) were used as the previous accepted state. No proof-coverage run and no
per-technique ablation was made (no new technique in this milestone; the task listed only the five configurations).

## Interpretation

**Correctness: no discrepancy.** No wrong verdict, ERROR or MISMATCH in any of the 9 runs; verdicts agree with the
baseline runs of the same configuration, with M1-r2 and with `baseline-t180` (`all-runs-discrepancy-check.md`).
No proofs were involved in this stage, so no rejected proof.

**Speed against the baseline: equal or slightly better, within noise.** Paired PAR2 difference (new - baseline):
default +0.00 s [-0.77, +0.80], `-dl` -0.11 s [-0.82, +0.56], mode1 +0.20 s, mode2 -1.39 s [-3.05, +0.13],
ccmin3 -1.52 s [-3.44, +0.32]; all verdicts "no measurable difference", "B is not worse than A: yes" everywhere.
Solved (new vs baseline): default 142/145/143 vs 141/146/143; `-dl` 149/153/146 vs 150/153/146; mode1 115 vs 116;
mode2 135 vs 130; ccmin3 147 vs 142. The seed spread of one arm is 5 instances (default 141-146) and about 1.5-2 s PAR2
(default 77.9-79.3), so only the mode2 (+5) and ccmin3 (+5) solved-count gains are at the level of the noise band and
no difference in the tables exceeds it by a clear margin. Instances gained/lost in a majority of seeds, default:
gained `test_5_5_knobby.pg-9`, lost `klieber2017q-076-19-eq`, `klieber2017q-108-27-t1` (klieber instances near the
timeout swing between seeds in both directions: 14 wins, 6 losses, per-instance differences up to 60 s).
`2.1.qcir` hits the 8 GB memory limit in both arms (default, `-dl`, mode1); `5.2-3.qcir` hits it in the baseline
(3/3 default runs) and sometimes in the new binary (`-dl` 3/3); nothing is new in this respect.

**Engine speed (identical searches, same conflict counts): faster than the baseline, with one failing family line.**
Pooled geometric mean new/baseline CPU time: default **0.964** (n=51; seeds 0.991/0.965/0.891), `-dl` **0.950**
(n=51), mode1 **0.990** (n=36, report only). Families: DW 0.855, chess 0.975, hadw 0.921, numeric 0.941 (default);
mode1 chess 1.044 (n=11), DW 0.916. Against M1-r2 (same-machine): default 0.988/0.964/0.942 per seed (PAR2 -0.24 s,
paired verdict "better", 15 wins, 0 losses), `-dl` 0.979, mode1 0.962, mode2 0.969, ccmin3 0.989.
The mode-1 deficit of the previous round (DW 1.3-1.4, chess mate_in_3 1.06) is gone: DW 0.916, pooled 0.990, all
families with n >= 3 below 1.10 (decision D6 is therefore not triggered).

**Regression: family `jctc`, default, 1.330 (n=4) -> `gate.py` exits 1 (GATE: FAIL, 1 line).** The four identical-search
instances are `jctc2-pass` (2.05 -> 4.12 s, one seed), `jctc10-fail` (5.05 -> 11.79 s seed 1, 7.3 -> 8.7 s seed 2),
`jctc17-vals-0,2-pass` (1.04) and `jctc8-pass` (about 1.0). In `-dl` jctc is 0.969 and in M1-r2 the same instances were
2.61 s and 5.4/6.2 s, so against r2 they are slower too. No decision in STATUS.md covers this family line, so it is
reported as **not met**, not waved through. Evidence that it is not an engine slowdown: the instances run in the same
L3 group together (names sorted, jctc2/jctc4/.../jctc10 neighbours) and the benchmark-load effect on a few short jobs
is known (M1-r2/r3 load measurements). Diagnostic runs in isolation (3 repetitions each, otherwise idle machine, tags
`M1-r3-jctc-isol-base-rep*` and `M1-r3-jctc-isol-new-rep*`, same seed, equal searches): new/baseline CPU
`jctc10-fail` 4.35-4.36 vs 4.68 s (0.93), `jctc2-pass` 1.56-1.59 vs 1.76 s (0.89-0.90), `jctc8-pass` 14.72-14.89 vs
15.08-15.16 s (0.98). So the 1.33 appears only under the full 48-job load (single runs of 2-12 s with a variance this
large; the noise of one run of these instances between the same-binary rounds is a factor 1.2-2.3), and not in
isolation. This is a hypothesis from 3 + 3 isolated runs, not a proof; a load-run (`bench/load_measure.py`) with a
jctc window would settle it. The coordinator decides whether to accept it (n=4, all instances under 12 s) or to
investigate.

**Other regressions:** none beyond noise. Family tables show CM +10.4 s mean score (7 instances, 1 win/3 losses,
timeout-edge instances `CM-sat-04-01-06-4`, `CM-sat-04-01-07-3` swinging with the seed; gained `CM-sat-04-01-06-3` in
three configurations) and klieber +2.7 s (14 wins, 6 losses); neither exceeds the seed noise. Largest default
slowdowns: `klieber2017q-088-22-t1` +61 s, `klieber2017q-108-27-t1` +49 s, `klieber2017q-076-19-t1` +43 s (timeout-edge,
compensated by other klieber gains such as `-112-28-t1`, `-084-21-eq`).

## Gate of the round (ROADMAP M1, benchmark stage, as measured)

| line | value | met |
|---|---|---|
| no result discrepancy / error / rejected proof | none in 9 runs | met |
| paired PAR2: new not worse than baseline (default, `-dl`) | +0.00 s / -0.11 s, "no measurable difference", not worse: yes | met |
| `gate.py` pooled identical-search ratio, default, limit 1.04 | 0.964 | met |
| `gate.py` pooled, `-dl` | 0.950 | met |
| `gate.py` families n >= 3 below 1.10, default | jctc 1.330 (n=4) | **not met** |
| `gate.py` families n >= 3 below 1.10, `-dl` | max 0.969 | met |
| mode 1 reported (pooled <= ~1.03, no family n >= 3 above 1.10) | 0.990, max family 1.044 | met (closes D6) |
| memory-limit hits named | `2.1.qcir`, `5.2-3.qcir` (see `gate.md`) | listed |

Blocking items: the jctc family line (`GATE: FAIL (1 lines)`), not covered by any decision in STATUS.md. No other
blocking item.

## Reproduction

    B=baseline-c96; M=M1-r3
    python3 bench/compare.py --paired --out bench/results/M1-r3-reports/default-paired.md $B-default-t60-s{1,2,3} -- $M-default-s{1,2,3}   # likewise dl; mode1/mode2/ccmin3 with s1
    python3 bench/compare.py --paired --out bench/results/M1-r3-reports/default-vs-r2.md M1-r2-default-s{1,2,3} -- $M-default-s{1,2,3}   # likewise the others
    python3 bench/gate.py --pair default:$B-default-t60-s1,...:$M-default-s1,... --pair dl:... --report mode1:$B-mode1-t60-s1:$M-mode1-s1 --out bench/results/M1-r3-reports/gate.md

Run script: `/home/ec2-user/miniqu-work/logs/m1r3-bench.sh`. Full tables: `M1-r3-reports/` (per configuration against the
baseline `*-paired.md`, against M1-r2 `*-vs-r2.md`, `gate.md` verbatim below, `all-runs-discrepancy-check.md`).

## gate.py output (verbatim)

# Gate: identical searches, new / reference

## default

default: pooled identical searches: n=51, geometric mean new/reference = 0.964, limit 1.04: PASS

Per seed: seed 1: 0.991 (n=41), seed 2: 0.965 (n=40), seed 3: 0.891 (n=37).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| CM | 1 | 0.859 | n < 3 |
| DW | 6 | 0.855 | PASS |
| DWs | 1 | 1.003 | n < 3 |
| Lights | 1 | 1.017 | n < 3 |
| chess | 16 | 0.975 | PASS |
| collector | 1 | 0.902 | n < 3 |
| finding | 1 | 0.926 | n < 3 |
| hadw | 3 | 0.921 | PASS |
| jctc | 4 | 1.330 | FAIL |
| lift | 1 | 0.906 | n < 3 |
| ltl | 1 | 0.930 | n < 3 |
| numeric | 15 | 0.941 | PASS |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 3/3 runs, B 3/3 runs), `5.2-3.qcir` (A 3/3 runs, B 0/3 runs)
- ERROR/MISMATCH rows: none

## dl

dl: pooled identical searches: n=51, geometric mean new/reference = 0.950, limit 1.04: PASS

Per seed: seed 1: 0.949 (n=41), seed 2: 0.938 (n=43), seed 3: 0.974 (n=31).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| DW | 4 | 0.932 | PASS |
| Lights | 2 | 1.078 | n < 3 |
| chess | 18 | 0.959 | PASS |
| collector | 1 | 0.882 | n < 3 |
| finding | 1 | 1.003 | n < 3 |
| hadw | 4 | 0.899 | PASS |
| jctc | 3 | 0.969 | PASS |
| lift | 1 | 0.897 | n < 3 |
| ltl | 1 | 0.893 | n < 3 |
| numeric | 14 | 0.952 | PASS |
| round | 1 | 0.915 | n < 3 |
| voter | 1 | 0.925 | n < 3 |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 3/3 runs, B 3/3 runs), `5.2-3.qcir` (A 3/3 runs, B 3/3 runs)
- ERROR/MISMATCH rows: none

## mode1

mode1: pooled identical searches: n=36, geometric mean new/reference = 0.990, limit 1.04: PASS

Per seed: seed 1: 0.990 (n=36).

Per family (identical searches pooled over the seeds; gated if n >= 3, limit 1.10):

| family | n | geometric mean | verdict |
|---|---:|---:|---:|
| DW | 5 | 0.916 | PASS |
| chess | 11 | 1.044 | PASS |
| collector | 1 | 0.969 | n < 3 |
| hadw | 2 | 1.188 | n < 3 |
| lift | 1 | 0.886 | n < 3 |
| ltl | 1 | 1.010 | n < 3 |
| numeric | 14 | 0.967 | PASS |
| round | 1 | 0.895 | n < 3 |

- memory-limit hits (MEMOUT): `2.1.qcir` (A 1/1 runs, B 1/1 runs), `5.2-3.qcir` (A 1/1 runs, B 0/1 runs)
- ERROR/MISMATCH rows: none

## Summary

| configuration | kind | n | geometric mean | verdict |
|---|---:|---:|---:|---:|
| default jctc | family | 4 | 1.330 | FAIL |

GATE: FAIL (1 lines)

## Per-configuration reports

### default (new vs same-machine baseline)

#### Paired comparison: B (M1-r3-default-s1, M1-r3-default-s2, M1-r3-default-s3) against A (baseline-c96-default-t60-s1, baseline-c96-default-t60-s2, baseline-c96-default-t60-s3)

No result discrepancies, solver errors or proof problems.

##### Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-23T01:16:03 |
| B | `` | 46874d9 | 006221175f2f | 2026-11-23T20:12:40 |

Order in which the runs started:

- 2026-11-23T01:16:03 `baseline-c96-default-t60-s1`
- 2026-11-23T01:39:53 `baseline-c96-default-t60-s2`
- 2026-11-23T02:03:45 `baseline-c96-default-t60-s3`
- 2026-11-23T20:12:40 `M1-r3-default-s1`
- 2026-11-23T20:18:43 `M1-r3-default-s2`
- 2026-11-23T20:24:43 `M1-r3-default-s3`

##### Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.00 s**, 95% bootstrap interval [-0.77, +0.80] (10000 resamples).

Sign test: B wins on 36 instances, loses on 18, ties on 322; two-sided p = 0.0198 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

##### Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 41 | 0.991 | 18 | 23 |
| 2 | 40 | 0.965 | 20 | 20 |
| 3 | 37 | 0.891 | 13 | 24 |
| all (per instance) | 51 | 0.964 | 22 | 29 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.859 |  |
| DW | 6 | 0.855 |  |
| DWs | 1 | 1.003 |  |
| Lights | 1 | 1.017 |  |
| chess | 16 | 0.975 |  |
| collector | 1 | 0.902 |  |
| finding | 1 | 0.926 |  |
| hadw | 3 | 0.921 |  |
| jctc | 4 | 1.330 | > 1.10 |
| lift | 1 | 0.906 |  |
| ltl | 1 | 0.930 |  |
| numeric | 15 | 0.941 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 2.007 | 2.05 | 4.12 |
| jctc10-fail.qcir | 1.670 | 6.18 | 10.27 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.156 | 8.43 | 9.77 |
| 5.1-1.qcir | 1.153 | 40.74 | 47.06 |
| 5.2-1.qcir | 1.149 | 31.70 | 35.85 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 1.144 | 9.56 | 10.94 |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | 1.123 | 1.08 | 1.21 |
| 4.1.qcir | 1.094 | 6.67 | 7.27 |
| 9.2.qcir | 1.071 | 18.38 | 19.71 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.067 | 3.78 | 4.03 |
| DW-unsat-09-22-1.qcir | 1.063 | 15.38 | 15.84 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.061 | 1.13 | 1.19 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.060 | 1.26 | 1.32 |
| 11.1.qcir | 1.037 | 31.68 | 32.95 |
| jctc17-vals-0,2-pass.qcir | 1.036 | 12.14 | 12.58 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.577 | 2.93 | 1.69 |
| DW-sat-08-22-1.qcir | 0.691 | 2.54 | 1.71 |
| 3.2.qcir | 0.737 | 1.26 | 0.93 |
| DW-unsat-09-23-1.qcir | 0.749 | 26.02 | 21.93 |
| 9.1.qcir | 0.753 | 2.16 | 1.63 |

##### Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 83/59/142 | 79.7 |
| 2 | 86/60/146 | 77.9 | 86/59/145 | 78.0 |
| 3 | 85/58/143 | 79.1 | 83/60/143 | 78.7 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.9-79.3 |
| B | 142-145 | 78.0-79.7 |

##### Instances gained and lost in a majority of seeds

- gained by B (1): `test_5_5_knobby.pg-9.qcir`
- lost by B (2): `klieber2017q-076-19-eq.qcir`, `klieber2017q-108-27-t1.qcir`

##### Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.1 | 105.6 | +10.4 | 1 | 3 |
| DW | 7 | 31.8 | 30.8 | -1.0 | 2 | 0 |
| DWs | 13 | 117.3 | 117.3 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.8 | 80.4 | +0.6 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 100.8 | -0.4 | 0 | 0 |
| arbiter | 6 | 84.8 | 84.5 | -0.3 | 1 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.7 | 77.6 | -5.2 | 3 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.3 | 27.5 | +0.2 | 1 | 4 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 1 |
| collector | 1 | 4.4 | 4.0 | -0.4 | 0 | 0 |
| connect | 7 | 86.9 | 86.8 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 74.7 | 79.2 | +4.5 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.3 | 9.6 | -0.8 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.5 | 76.0 | -0.5 | 2 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.7 | 75.9 | +0.1 | 0 | 0 |
| klieber | 26 | 49.9 | 52.6 | +2.7 | 14 | 6 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.7 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.6 | 98.5 | -0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.3 | 111.9 | +0.7 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 32.1 | +0.3 | 2 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 88.9 | 88.1 | -0.8 | 0 | 0 |
| robot | 1 | 5.2 | 3.9 | -1.3 | 1 | 0 |
| round | 1 | 2.0 | 1.8 | -0.2 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 59.0 | 57.5 | -1.5 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 47.2 | 44.5 | -2.7 | 5 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

##### Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_knobby.pg-9.qcir | 90.6 | 41.5 | -49.1 |
| CM-sat-04-01-06-3.qcir | 90.4 | 58.6 | -31.8 |
| klieber2017q-112-28-t1.qcir | 120.0 | 89.9 | -30.1 |
| klieber2017q-084-21-eq.qcir | 120.0 | 92.3 | -27.7 |
| klieber2017q-100-25-t1.qcir | 93.7 | 71.2 | -22.4 |
| bt2nd-3x4_12.ig.qcir | 97.7 | 75.4 | -22.3 |
| Lights2_0f5381e9.tlsf.qcir | 61.6 | 40.8 | -20.8 |
| bt2nd-3x6_10.ig.qcir | 120.0 | 99.6 | -20.4 |
| bt-2x5_17.ig.qcir | 120.0 | 99.8 | -20.2 |
| klieber2017q-068-17-t1.qcir | 40.2 | 26.4 | -13.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-088-22-t1.qcir | 10.2 | 71.7 | +61.5 |
| klieber2017q-108-27-t1.qcir | 35.4 | 84.6 | +49.2 |
| klieber2017q-076-19-t1.qcir | 29.2 | 72.3 | +43.1 |
| klieber2017q-076-19-eq.qcir | 51.4 | 92.3 | +40.9 |
| CM-sat-04-01-06-4.qcir | 43.8 | 80.3 | +36.5 |
| CM-sat-04-01-07-3.qcir | 84.4 | 120.0 | +35.6 |
| CM-sat-07-01-06-3.qcir | 87.2 | 120.0 | +32.8 |
| Lights2_b02056d6.tlsf.qcir | 97.9 | 120.0 | +22.1 |
| klieber2017q-078-19-eq.qcir | 48.1 | 68.7 | +20.6 |
| eequery_query42_1344.qcir | 29.3 | 38.3 | +9.0 |

##### Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-1x3X3x2_1.qcir | 26 | 34 | 1.32x |
| bt-3x6_9.ig.qcir | 15 | 17 | 1.14x |
| sc-ungrounded-2x1X1x2_2.qcir | 47 | 53 | 1.13x |


### dl (new vs same-machine baseline)

#### Paired comparison: B (M1-r3-dl-s1, M1-r3-dl-s2, M1-r3-dl-s3) against A (baseline-c96-dl-t60-s1, baseline-c96-dl-t60-s2, baseline-c96-dl-t60-s3)

No result discrepancies, solver errors or proof problems.

##### Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-23T01:28:03 |
| B | `-dl` | 46874d9 | 006221175f2f | 2026-11-23T20:30:44 |

Order in which the runs started:

- 2026-11-23T01:28:03 `baseline-c96-dl-t60-s1`
- 2026-11-23T01:51:49 `baseline-c96-dl-t60-s2`
- 2026-11-23T02:15:46 `baseline-c96-dl-t60-s3`
- 2026-11-23T20:30:44 `M1-r3-dl-s1`
- 2026-11-23T20:36:39 `M1-r3-dl-s2`
- 2026-11-23T20:42:30 `M1-r3-dl-s3`

##### Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.11 s**, 95% bootstrap interval [-0.82, +0.56] (10000 resamples).

Sign test: B wins on 42 instances, loses on 24, ties on 310; two-sided p = 0.0356 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

##### Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 41 | 0.949 | 13 | 28 |
| 2 | 43 | 0.938 | 15 | 28 |
| 3 | 31 | 0.974 | 8 | 23 |
| all (per instance) | 51 | 0.950 | 16 | 35 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 4 | 0.932 |  |
| Lights | 2 | 1.078 |  |
| chess | 18 | 0.959 |  |
| collector | 1 | 0.882 |  |
| finding | 1 | 1.003 |  |
| hadw | 4 | 0.899 |  |
| jctc | 3 | 0.969 |  |
| lift | 1 | 0.897 |  |
| ltl | 1 | 0.893 |  |
| numeric | 14 | 0.952 |  |
| round | 1 | 0.915 |  |
| voter | 1 | 0.925 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc17-vals-0,2-pass.qcir | 1.205 | 11.54 | 15.42 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.183 | 15.03 | 17.78 |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 1.152 | 4.46 | 4.38 |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | 1.140 | 5.65 | 6.44 |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 1.123 | 3.30 | 3.80 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.111 | 10.94 | 12.15 |
| Lights2_b02056d6.tlsf.qcir | 1.095 | 24.76 | 26.34 |
| DW-sat-09-26-1.qcir | 1.079 | 14.46 | 15.60 |
| Lights2_0f5381e9.tlsf.qcir | 1.061 | 53.27 | 56.36 |
| 5.2-1.qcir | 1.054 | 35.44 | 37.03 |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 1.054 | 6.59 | 6.71 |
| hadw11-12.qcir | 1.051 | 51.69 | 54.32 |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 1.027 | 8.51 | 8.53 |
| 4.1.qcir | 1.010 | 12.63 | 12.84 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 1.009 | 5.67 | 6.97 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.747 | 4.42 | 3.27 |
| hadw10-11.qcir | 0.763 | 34.83 | 24.07 |
| DW-sat-08-23-1.qcir | 0.791 | 8.87 | 6.94 |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 0.792 | 5.56 | 4.29 |
| 9.1.qcir | 0.793 | 2.22 | 1.76 |

##### Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.4 | 85/64/149 | 76.5 |
| 2 | 86/67/153 | 75.7 | 88/65/153 | 75.6 |
| 3 | 84/62/146 | 77.7 | 83/63/146 | 77.4 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.7-77.7 |
| B | 146-153 | 75.6-77.4 |

##### Instances gained and lost in a majority of seeds

- gained by B (1): `CM-sat-04-01-06-3.qcir`
- lost by B (0): none

##### Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.2 | 88.4 | -8.8 | 2 | 2 |
| DW | 7 | 21.4 | 18.2 | -3.2 | 4 | 0 |
| DWs | 13 | 117.8 | 120.0 | +2.2 | 0 | 1 |
| JP | 6 | 109.9 | 112.8 | +2.9 | 0 | 1 |
| Lights | 2 | 50.2 | 52.0 | +1.8 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 104.0 | -3.7 | 1 | 1 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.2 | 91.3 | +4.1 | 1 | 1 |
| arbiter | 6 | 84.2 | 83.9 | -0.2 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.8 | 83.5 | +2.8 | 1 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.8 | 62.0 | +0.2 | 4 | 2 |
| ci | 30 | 88.6 | 88.6 | +0.0 | 1 | 1 |
| collector | 1 | 4.3 | 3.8 | -0.5 | 0 | 0 |
| connect | 7 | 88.4 | 87.7 | -0.8 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.5 | 70.1 | +0.7 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.8 | 7.8 | -0.1 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.7 | 78.0 | -0.6 | 4 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.4 | 38.2 | +0.8 | 3 | 2 |
| klieber | 26 | 17.3 | 16.1 | -1.2 | 11 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.2 | 98.8 | -0.3 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.1 | 111.6 | +0.5 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | -0.0 | 0 | 0 |
| numeric | 26 | 36.8 | 36.7 | -0.1 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 79.8 | +6.9 | 0 | 1 |
| robot | 1 | 4.4 | 3.2 | -1.2 | 1 | 0 |
| round | 1 | 1.4 | 1.3 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.7 | 56.1 | -0.6 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 37.3 | -0.8 | 4 | 2 |
| voter | 2 | 102.1 | 102.0 | -0.2 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

##### Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 90.4 | 23.1 | -67.3 |
| klieber2017q-084-21-eq.qcir | 68.4 | 26.7 | -41.7 |
| SR-sat-02-01-06-3.qcir | 120.0 | 89.1 | -30.9 |
| jctc10-fail.qcir | 120.0 | 89.3 | -30.7 |
| test_5_5_fatty.pg-9.qcir | 73.9 | 47.5 | -26.4 |
| CM-sat-07-01-07-3.qcir | 120.0 | 96.9 | -23.1 |
| jctc1-pass.qcir | 80.0 | 60.0 | -20.0 |
| DW-unsat-11-26-1.qcir | 72.9 | 55.5 | -17.3 |
| klieber2017q-086-21-t1.qcir | 18.6 | 9.5 | -9.1 |
| test_5_5_knobby.pg-9.qcir | 26.3 | 18.0 | -8.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc4-fail.qcir | 9.9 | 41.3 | +31.4 |
| bt2nd-3x6_10.ig.qcir | 90.8 | 120.0 | +29.2 |
| DWs-unsat-08-17-1.qcir | 91.7 | 120.0 | +28.3 |
| klieber2017q-088-22-eq.qcir | 62.7 | 90.8 | +28.2 |
| jctc14-unrolled-fail.qcir | 92.4 | 120.0 | +27.6 |
| CM-sat-04-01-06-4.qcir | 96.5 | 120.0 | +23.5 |
| amba2f9n.sat.qcir | 53.5 | 76.3 | +22.9 |
| JP-unsat-02-06-3.qcir | 59.4 | 76.6 | +17.2 |
| reachqu_query64_1344.qcir | 17.6 | 33.1 | +15.5 |
| SR-unsat-04-01-08-1.qcir | 58.3 | 70.8 | +12.5 |

##### Peak memory

5 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc6-pass.qcir | 64 | 120 | 1.88x |
| bt-3x6_9.ig.qcir | 14 | 20 | 1.42x |
| jctc13-fail.qcir | 17 | 23 | 1.40x |
| CM-sat-04-01-07-3.qcir | 480 | 574 | 1.20x |
| jctc8-pass.qcir | 49 | 56 | 1.14x |


### mode1 (new vs same-machine baseline)

#### Paired comparison: B (M1-r3-mode1-s1) against A (baseline-c96-mode1-t60-s1)

No result discrepancies, solver errors or proof problems.

##### Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | c39005a | 10ff614c6694 | 2026-11-23T02:27:56 |
| B | `-mode=1` | 46874d9 | 006221175f2f | 2026-11-23T20:48:28 |

Order in which the runs started:

- 2026-11-23T02:27:56 `baseline-c96-mode1-t60-s1`
- 2026-11-23T20:48:28 `M1-r3-mode1-s1`

##### Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.20 s**, 95% bootstrap interval [-1.19, +1.59] (10000 resamples).

Sign test: B wins on 20 instances, loses on 18, ties on 338; two-sided p = 0.8714 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

##### Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 36 | 0.990 | 21 | 15 |
| all (per instance) | 36 | 0.990 | 21 | 15 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 5 | 0.916 |  |
| chess | 11 | 1.044 |  |
| collector | 1 | 0.969 |  |
| hadw | 2 | 1.188 |  |
| lift | 1 | 0.886 |  |
| ltl | 1 | 1.010 |  |
| numeric | 14 | 0.967 |  |
| round | 1 | 0.895 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| hadw10-11.qcir | 1.300 | 1.45 | 1.89 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 1.215 | 15.68 | 19.05 |
| 5.1-1.qcir | 1.196 | 49.95 | 59.74 |
| 4.1.qcir | 1.171 | 7.24 | 8.48 |
| 5.2-1.qcir | 1.118 | 28.50 | 31.87 |
| 9.2.qcir | 1.103 | 19.19 | 21.16 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 1.089 | 10.41 | 11.34 |
| 11.1.qcir | 1.087 | 32.82 | 35.69 |
| hadw11-12.qcir | 1.086 | 8.53 | 9.26 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.084 | 2.12 | 2.29 |
| DW-sat-08-23-1.qcir | 1.080 | 1.70 | 1.83 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.079 | 18.27 | 19.72 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 1.076 | 14.63 | 15.73 |
| 8.1.qcir | 1.073 | 3.98 | 4.27 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 1.071 | 36.74 | 39.36 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 10.2.qcir | 0.749 | 1.64 | 1.23 |
| DW-unsat-09-22-1.qcir | 0.753 | 12.10 | 9.11 |
| 3.2.qcir | 0.753 | 1.16 | 0.87 |
| 9.1.qcir | 0.773 | 2.16 | 1.67 |
| 1.3.qcir | 0.832 | 7.78 | 6.47 |

##### Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 72/44/116 | 85.9 | 72/43/115 | 86.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 116-116 | 85.9-85.9 |
| B | 115-115 | 86.1-86.1 |

##### Instances gained and lost in a majority of seeds

- gained by B (4): `CM-sat-04-01-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `jctc8-pass.qcir`, `reachqu_query64_1344.qcir`
- lost by B (5): `Lights2_0f5381e9.tlsf.qcir`, `hadw6-8.qcir`, `klieber2017q-072-18-eq.qcir`, `reachqu_query60_1344.qcir`, `test_5_5_elly.pg-9.qcir`

##### Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 103.1 | -16.9 | 1 | 0 |
| DW | 7 | 40.2 | 39.7 | -0.5 | 1 | 0 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 89.7 | 87.6 | -2.1 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.4 | 101.7 | +0.3 | 0 | 0 |
| arbiter | 6 | 85.0 | 85.0 | -0.0 | 1 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.5 | 93.7 | +1.3 | 0 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.3 | 29.4 | +0.1 | 1 | 3 |
| ci | 30 | 100.1 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.5 | 3.4 | -0.1 | 0 | 0 |
| connect | 7 | 89.1 | 89.1 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 71.2 | 72.2 | +1.0 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 11.7 | 9.3 | -2.5 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.2 | 72.2 | +3.0 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.9 | 77.1 | -6.8 | 1 | 0 |
| klieber | 26 | 112.1 | 116.5 | +4.4 | 0 | 2 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.3 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.8 | 97.8 | +0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.3 | 110.8 | +0.5 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 31.3 | 32.0 | +0.7 | 2 | 4 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 83.3 | 91.7 | +8.4 | 1 | 1 |
| robot | 1 | 4.5 | 3.8 | -0.7 | 0 | 0 |
| round | 1 | 1.5 | 1.4 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 56.7 | -1.6 | 2 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 68.6 | 70.7 | +2.1 | 6 | 3 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

##### Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 120.0 | 1.9 | -118.1 |
| jctc8-pass.qcir | 120.0 | 31.8 | -88.2 |
| reachqu_query64_1344.qcir | 120.0 | 35.1 | -84.9 |
| Lights2_b02056d6.tlsf.qcir | 120.0 | 55.3 | -64.7 |
| sc-ungrounded-2x2X2x2_1.qcir | 26.4 | 14.5 | -11.8 |
| test_5_5_Z.pg-7.qcir | 14.7 | 6.4 | -8.3 |
| test_5_5_snaky.pg-7.qcir | 15.7 | 7.5 | -8.2 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 40.8 | 32.8 | -8.0 |
| test_5_5_domino.pg-11.qcir | 10.7 | 4.2 | -6.5 |
| hadw4-7.qcir | 59.9 | 55.1 | -4.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query60_1344.qcir | 9.8 | 120.0 | +110.2 |
| klieber2017q-072-18-eq.qcir | 20.7 | 120.0 | +99.3 |
| test_5_5_elly.pg-9.qcir | 46.9 | 120.0 | +73.1 |
| hadw6-8.qcir | 51.1 | 120.0 | +68.9 |
| Lights2_0f5381e9.tlsf.qcir | 59.5 | 120.0 | +60.5 |
| klieber2017q-060-15-eq.qcir | 13.3 | 29.2 | +15.9 |
| bt2nd-2x5_10.ig.qcir | 28.0 | 42.4 | +14.5 |
| 5.1-1.qcir | 50.0 | 59.8 | +9.8 |
| test_5_5_elly.pg-7.qcir | 1.6 | 10.7 | +9.1 |
| test_5_5_L.pg-7.qcir | 1.3 | 7.2 | +5.9 |

##### Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.


### mode2 (new vs same-machine baseline)

#### Paired comparison: B (M1-r3-mode2-s1) against A (baseline-c96-mode2-t60-s1)

No result discrepancies, solver errors or proof problems.

##### Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | c39005a | 10ff614c6694 | 2026-11-23T02:40:07 |
| B | `-mode=2` | 46874d9 | 006221175f2f | 2026-11-23T20:54:38 |

Order in which the runs started:

- 2026-11-23T02:40:07 `baseline-c96-mode2-t60-s1`
- 2026-11-23T20:54:38 `M1-r3-mode2-s1`

##### Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-1.39 s**, 95% bootstrap interval [-3.05, +0.13] (10000 resamples).

Sign test: B wins on 43 instances, loses on 18, ties on 315; two-sided p = 0.0019 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

##### Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 33 | 0.906 | 10 | 23 |
| all (per instance) | 33 | 0.906 | 10 | 23 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 3 | 0.900 |  |
| DWs | 2 | 0.750 |  |
| Lights | 1 | 1.034 |  |
| chess | 5 | 1.074 |  |
| collector | 1 | 0.996 |  |
| finding | 1 | 0.844 |  |
| hadw | 3 | 0.846 |  |
| jctc | 1 | 0.796 |  |
| lift | 1 | 0.742 |  |
| numeric | 14 | 0.904 |  |
| round | 1 | 0.850 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.242 | 1.26 | 1.56 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 1.149 | 1.04 | 1.20 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 1.073 | 8.11 | 8.70 |
| DW-unsat-09-23-1.qcir | 1.051 | 20.28 | 21.32 |
| 5.2-2.qcir | 1.037 | 49.98 | 51.80 |
| Lights2_b02056d6.tlsf.qcir | 1.034 | 26.78 | 27.69 |
| 9.3.qcir | 1.027 | 2.93 | 3.01 |
| 9.2.qcir | 1.022 | 23.36 | 23.86 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.018 | 4.18 | 4.25 |
| 8.1.qcir | 1.007 | 5.05 | 5.08 |
| 11.1.qcir | 0.997 | 52.26 | 52.12 |
| collector_v17.tlsf.qcir | 0.996 | 7.19 | 7.16 |
| 3.1.qcir | 0.986 | 48.70 | 48.03 |
| 5.2-1.qcir | 0.976 | 5.73 | 5.60 |
| DWs-sat-10-25-1.qcir | 0.948 | 2.92 | 2.77 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-unsat-08-18-1.qcir | 0.594 | 19.96 | 11.86 |
| 3.2.qcir | 0.733 | 1.16 | 0.85 |
| 10.2.qcir | 0.738 | 1.68 | 1.24 |
| lift_gr1+2.tlsf.qcir | 0.742 | 4.86 | 3.61 |
| 1.4.qcir | 0.790 | 7.47 | 5.90 |

##### Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 77/53/130 | 82.3 | 78/57/135 | 80.9 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 130-130 | 82.3-82.3 |
| B | 135-135 | 80.9-80.9 |

##### Instances gained and lost in a majority of seeds

- gained by B (7): `CM-sat-04-01-07-3.qcir`, `JP-unsat-02-06-3.qcir`, `hadw2-8.qcir`, `jctc8-pass.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-100-25-t1.qcir`, `ltl2dba_beta6.tlsf.qcir`
- lost by B (2): `CM-sat-04-01-06-4.qcir`, `jctc6-pass.qcir`

##### Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 108.8 | 103.2 | -5.6 | 1 | 1 |
| DW | 7 | 40.5 | 40.1 | -0.4 | 1 | 0 |
| DWs | 13 | 97.2 | 96.7 | -0.4 | 1 | 0 |
| JP | 6 | 120.0 | 108.7 | -11.3 | 1 | 0 |
| Lights | 2 | 73.4 | 73.9 | +0.4 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.6 | 97.3 | -0.2 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| arbiter | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.3 | 91.3 | -1.0 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 31.1 | 31.0 | -0.1 | 3 | 2 |
| ci | 30 | 88.4 | 88.8 | +0.4 | 3 | 1 |
| collector | 1 | 7.2 | 7.2 | -0.0 | 0 | 0 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.2 | 65.6 | +1.4 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 48.4 | 40.9 | -7.6 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 75.9 | 72.1 | -3.8 | 5 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.4 | 83.3 | -0.1 | 1 | 1 |
| klieber | 26 | 43.9 | 37.0 | -6.9 | 9 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.4 | 61.8 | -0.6 | 1 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | -0.1 | 0 | 0 |
| ltl | 5 | 120.0 | 106.9 | -13.1 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.8 | 0.7 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 31.6 | -0.2 | 3 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 57.2 | 54.9 | -2.3 | 1 | 0 |
| robot | 1 | 51.1 | 24.3 | -26.8 | 1 | 0 |
| round | 1 | 3.0 | 2.6 | -0.4 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 77.2 | 75.1 | -2.1 | 4 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 79.6 | 79.0 | -0.6 | 4 | 1 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

##### Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc8-pass.qcir | 120.0 | 0.2 | -119.8 |
| CM-sat-04-01-07-3.qcir | 120.0 | 2.3 | -117.7 |
| klieber2017q-072-18-t1.qcir | 120.0 | 6.5 | -113.5 |
| klieber2017q-100-25-t1.qcir | 120.0 | 18.1 | -101.9 |
| hadw2-8.qcir | 120.0 | 48.9 | -71.1 |
| JP-unsat-02-06-3.qcir | 120.0 | 52.4 | -67.6 |
| ltl2dba_beta6.tlsf.qcir | 120.0 | 54.4 | -65.6 |
| klieber2017q-112-28-t1.qcir | 49.7 | 16.4 | -33.3 |
| robot_grid6_1.tlsf.qcir | 51.1 | 24.3 | -26.8 |
| klieber2017q-088-22-t1.qcir | 34.2 | 7.7 | -26.5 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc6-pass.qcir | 0.1 | 120.0 | +119.9 |
| CM-sat-04-01-06-4.qcir | 41.7 | 120.0 | +78.3 |
| klieber2017q-066-16-eq.qcir | 15.8 | 50.4 | +34.7 |
| klieber2017q-074-18-t1.qcir | 10.0 | 37.0 | +27.0 |
| klieber2017q-068-17-t1.qcir | 23.4 | 47.5 | +24.1 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 1.5 | 20.2 | +18.8 |
| klieber2017q-072-18-eq.qcir | 16.7 | 33.6 | +17.0 |
| klieber2017q-060-15-eq.qcir | 8.2 | 18.4 | +10.2 |
| klieber2017q-078-19-eq.qcir | 28.1 | 37.7 | +9.6 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 7.6 | 15.3 | +7.7 |

##### Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 13 | 18 | 1.42x |
| sc-ungrounded-1x2X2x2_2.qcir | 56 | 77 | 1.36x |
| DWs-unsat-08-17-1.qcir | 182 | 218 | 1.20x |


### ccmin3 (new vs same-machine baseline)

#### Paired comparison: B (M1-r3-ccmin3-s1) against A (baseline-c96-ccmin3-t60-s1)

No result discrepancies, solver errors or proof problems.

##### Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-ccmin-mode=3` | c39005a | 10ff614c6694 | 2026-11-23T02:52:10 |
| B | `-ccmin-mode=3` | 46874d9 | 006221175f2f | 2026-11-23T21:00:38 |

Order in which the runs started:

- 2026-11-23T02:52:10 `baseline-c96-ccmin3-t60-s1`
- 2026-11-23T21:00:38 `M1-r3-ccmin3-s1`

##### Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-1.52 s**, 95% bootstrap interval [-3.44, +0.32] (10000 resamples).

Sign test: B wins on 42 instances, loses on 20, ties on 314; two-sided p = 0.0071 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

##### Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 4 | 0.818 | 0 | 4 |
| all (per instance) | 4 | 0.818 | 0 | 4 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DWs | 1 | 0.909 |  |
| numeric | 3 | 0.790 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-sat-12-28-1.qcir | 0.909 | 2.06 | 1.88 |
| 1.4.qcir | 0.857 | 8.81 | 7.55 |
| 10.2.qcir | 0.787 | 1.72 | 1.35 |
| 3.2.qcir | 0.732 | 1.17 | 0.85 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.732 | 1.17 | 0.85 |
| 10.2.qcir | 0.787 | 1.72 | 1.35 |
| 1.4.qcir | 0.857 | 8.81 | 7.55 |
| DWs-sat-12-28-1.qcir | 0.909 | 2.06 | 1.88 |

##### Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 87/55/142 | 79.0 | 87/60/147 | 77.5 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 142-142 | 79.0-79.0 |
| B | 147-147 | 77.5-77.5 |

##### Instances gained and lost in a majority of seeds

- gained by B (9): `CM-sat-04-01-06-3.qcir`, `DW-unsat-10-25-1.qcir`, `klieber2017q-080-20-t1.qcir`, `klieber2017q-082-20-t1.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `test_5_5_domino.pg-15.qcir`
- lost by B (4): `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `klieber2017q-100-25-t1.qcir`, `klieber2017q-112-28-t1.qcir`

##### Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 89.4 | 104.8 | +15.3 | 1 | 2 |
| DW | 7 | 38.2 | 31.2 | -7.0 | 1 | 2 |
| DWs | 13 | 110.9 | 110.9 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 58.8 | 55.2 | -3.5 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 88.7 | 87.6 | -1.1 | 0 | 0 |
| arbiter | 6 | 84.8 | 83.5 | -1.3 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 84.5 | 84.1 | -0.3 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 28.8 | 28.7 | -0.1 | 5 | 5 |
| ci | 30 | 100.2 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.7 | 2.6 | -1.1 | 1 | 0 |
| connect | 7 | 87.0 | 86.9 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 75.4 | 73.3 | -2.0 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 8.3 | 7.9 | -0.4 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.1 | 75.9 | -0.2 | 2 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 69.5 | 71.2 | +1.7 | 2 | 1 |
| klieber | 26 | 60.9 | 41.2 | -19.6 | 13 | 5 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.6 | -0.2 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.4 | 97.3 | -1.1 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.1 | 109.9 | -0.2 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 33.6 | 34.5 | +0.9 | 5 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 80.5 | 81.1 | +0.5 | 0 | 1 |
| robot | 1 | 3.3 | 2.6 | -0.8 | 0 | 0 |
| round | 1 | 1.6 | 1.9 | +0.3 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 57.1 | -1.1 | 2 | 1 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 45.5 | 41.7 | -3.8 | 4 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

##### Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-080-20-t1.qcir | 120.0 | 9.0 | -111.0 |
| klieber2017q-082-20-t1.qcir | 120.0 | 9.6 | -110.4 |
| klieber2017q-088-22-t1.qcir | 120.0 | 12.6 | -107.4 |
| klieber2017q-108-27-t1.qcir | 120.0 | 12.7 | -107.3 |
| CM-sat-04-01-06-3.qcir | 120.0 | 13.3 | -106.7 |
| klieber2017q-084-21-t1.qcir | 120.0 | 14.6 | -105.4 |
| test_5_5_domino.pg-15.qcir | 120.0 | 27.1 | -92.9 |
| DW-unsat-10-25-1.qcir | 120.0 | 58.7 | -61.3 |
| klieber2017q-086-21-t1.qcir | 120.0 | 59.1 | -60.9 |
| klieber2017q-078-19-t1.qcir | 58.2 | 1.4 | -56.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-4.qcir | 8.2 | 120.0 | +111.8 |
| CM-sat-04-01-07-3.qcir | 17.9 | 120.0 | +102.1 |
| klieber2017q-112-28-t1.qcir | 32.6 | 120.0 | +87.4 |
| klieber2017q-100-25-t1.qcir | 32.9 | 120.0 | +87.1 |
| jctc10-fail.qcir | 24.6 | 55.6 | +31.0 |
| 5.2-1.qcir | 12.8 | 42.1 | +29.3 |
| klieber2017q-076-19-t1.qcir | 3.7 | 29.7 | +25.9 |
| klieber2017q-076-19-eq.qcir | 35.2 | 53.3 | +18.1 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 6.4 | 24.0 | +17.6 |
| 3.1.qcir | 33.8 | 51.4 | +17.6 |

##### Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc10-fail.qcir | 72 | 149 | 2.08x |
| sc-ungrounded-2x1X1x2_2.qcir | 26 | 29 | 1.14x |
| hadw5-7.qcir | 32 | 36 | 1.11x |

