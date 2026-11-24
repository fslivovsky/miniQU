# M2-T11: jctc gap under `-dl`, 20 seeds, one switch per arm

Measurement only: no solver source, default, test or harness change. Question (STATUS J3): is the loss of the M2
default on `jctc8-pass` / `jctc2-pass` under `-dl` caused by one of the adopt items, or heavy-tail noise?

## Setup

- Binaries: M2 `bench-M2-r1/miniQU` (sha256 04531dfabcba651cda6181661ea7a9254ba34dfc49bd16e267b3516146887a8c),
  M1 `bench-M1-r3/miniQU` (006221175f2fdfcbae31daaf10e01bea0ca947523c15cb5c443ea0976a0d85ad), baseline
  (10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b). Seed: `--seed=S` for M1/M2,
  `-rnd-init -rnd-seed=S` for the baseline (the `--seed-args` of the `baseline-c96-*` runs).
- Instances: the 8 `jctc*-pass` files plus the `-fail` files some arm solved in a first pass (seeds 1-3, all 11 arms,
  both configurations): `jctc4-fail`, `jctc10-fail`, `jctc13-fail`, `jctc14-unrolled-fail` (`jctc5-fail` was
  solved by no arm). 12 instances x 20 seeds x 11 arms x 2 configurations = 5280 runs, 60 s wall each.
- Configurations: `dl` (`-dl`, main) and `plain` (no extra option, control). Arm options are listed in the tables.
- Machine: 48-core instance, `taskset -c 0-23`, 16 parallel jobs, interleaved arms; nothing else heavy ran
  (load average below 1 before the first-pass launch; one last job of the first pass may have overlapped the first
  seconds of the main run). Timings are wall times under 16 parallel jobs, only comparable inside this report.
- Exit codes: 10/20 solved, 124 time-out. No other exit code occurred; no verdict differed between arms,
  configurations or seeds.
- Median wall is over solved runs only; PAR2 counts a time-out as 120 s. Conflicts (`c stat conflicts`, `-verb=1`)
  are in `runs.csv` for the solved runs of arms 3-11.
- Paired test: over (instance, seed) pairs, count pairs where exactly one side timed out; exact two-sided sign
  test on these discordant pairs. 11 arms and several tables mean about 40 tests: a single p between 0.01 and 0.05
  is weak evidence.

## Errors

none

## Verdict agreement

no (instance, seed) has two different verdicts across arms and configurations

## Configuration `dl`: summary per arm

| arm | binary / options | time-outs | solved | PAR2 (s) | median wall of solved (s) |
|---:|---|---:|---:|---:|---:|
| 1 | M1 binary | 66 of 240 | 174 | 8710 | 0.61 |
| 2 | baseline | 61 of 240 | 179 | 8281 | 0.74 |
| 3 | M2 default | 70 of 240 | 170 | 9331 | 0.35 |
| 4 | M2 EQUIV string | 64 of 240 | 176 | 8469 | 0.54 |
| 5 | M2 --no-reusetrail | 67 of 240 | 173 | 8827 | 0.42 |
| 6 | M2 --no-rootsimp | 68 of 240 | 172 | 8932 | 0.58 |
| 7 | M2 --no-tiers --no-glueupdate | 80 of 240 | 160 | 10501 | 0.38 |
| 8 | M2 M1 trigger+target (tiers kept) | 72 of 240 | 168 | 9490 | 0.41 |
| 9 | M2 M1 reduce policy | 72 of 240 | 168 | 9501 | 0.40 |
| 10 | M2 --no-glueupdate | 70 of 240 | 170 | 9351 | 0.46 |
| 11 | M2 --no-reusetrail --no-rootsimp | 66 of 240 | 174 | 8819 | 0.50 |

### `dl`: time-outs of 20 per instance and arm

| instance | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| jctc1-pass | 6 | 6 | 3 | 4 | 5 | 4 | 5 | 5 | 5 | 4 | 2 |
| jctc10-fail | 18 | 19 | 19 | 18 | 19 | 18 | 20 | 19 | 19 | 19 | 20 |
| jctc13-fail | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| jctc14-unrolled-fail | 19 | 16 | 19 | 19 | 17 | 18 | 17 | 19 | 19 | 16 | 17 |
| jctc16-vals-0,2-pass | 2 | 2 | 3 | 2 | 2 | 1 | 0 | 3 | 3 | 2 | 1 |
| jctc17-vals-0,2-pass | 8 | 7 | 6 | 8 | 7 | 7 | 13 | 6 | 6 | 5 | 6 |
| jctc18-vals-0,2-pass | 4 | 4 | 5 | 4 | 5 | 5 | 8 | 7 | 7 | 8 | 5 |
| jctc2-pass | 0 | 0 | 4 | 0 | 2 | 2 | 3 | 1 | 1 | 1 | 4 |
| jctc4-fail | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| jctc6-pass | 2 | 3 | 2 | 2 | 2 | 2 | 2 | 3 | 4 | 5 | 3 |
| jctc8-pass | 3 | 2 | 6 | 3 | 5 | 7 | 7 | 5 | 4 | 6 | 5 |
| jctc9-pass | 3 | 2 | 3 | 3 | 3 | 4 | 5 | 4 | 4 | 4 | 3 |

## Configuration `plain`: summary per arm

| arm | binary / options | time-outs | solved | PAR2 (s) | median wall of solved (s) |
|---:|---|---:|---:|---:|---:|
| 1 | M1 binary | 140 of 240 | 100 | 17551 | 0.24 |
| 2 | baseline | 139 of 240 | 101 | 17584 | 0.28 |
| 3 | M2 default | 140 of 240 | 100 | 17231 | 0.21 |
| 4 | M2 EQUIV string | 137 of 240 | 103 | 17169 | 0.25 |
| 5 | M2 --no-reusetrail | 143 of 240 | 97 | 17792 | 0.31 |
| 6 | M2 --no-rootsimp | 141 of 240 | 99 | 17287 | 0.20 |
| 7 | M2 --no-tiers --no-glueupdate | 141 of 240 | 99 | 17417 | 0.27 |
| 8 | M2 M1 trigger+target (tiers kept) | 136 of 240 | 104 | 16753 | 0.26 |
| 9 | M2 M1 reduce policy | 137 of 240 | 103 | 16818 | 0.25 |
| 10 | M2 --no-glueupdate | 136 of 240 | 104 | 16795 | 0.23 |
| 11 | M2 --no-reusetrail --no-rootsimp | 145 of 240 | 95 | 18010 | 0.20 |

### `plain`: time-outs of 20 per instance and arm

| instance | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| jctc1-pass | 11 | 11 | 7 | 11 | 11 | 8 | 8 | 8 | 8 | 8 | 11 |
| jctc10-fail | 6 | 5 | 18 | 5 | 11 | 18 | 19 | 17 | 17 | 18 | 11 |
| jctc13-fail | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| jctc14-unrolled-fail | 15 | 15 | 20 | 14 | 11 | 20 | 20 | 19 | 19 | 20 | 13 |
| jctc16-vals-0,2-pass | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 | 13 |
| jctc17-vals-0,2-pass | 19 | 19 | 18 | 19 | 19 | 18 | 18 | 18 | 18 | 18 | 19 |
| jctc18-vals-0,2-pass | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20 | 20 |
| jctc2-pass | 16 | 16 | 14 | 15 | 17 | 14 | 15 | 14 | 15 | 13 | 17 |
| jctc4-fail | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| jctc6-pass | 10 | 10 | 8 | 10 | 9 | 8 | 7 | 7 | 7 | 7 | 9 |
| jctc8-pass | 14 | 14 | 8 | 14 | 15 | 8 | 9 | 9 | 9 | 8 | 15 |
| jctc9-pass | 16 | 16 | 14 | 16 | 17 | 14 | 12 | 11 | 11 | 11 | 17 |

## Paired comparison, `dl`, all instances (240 pairs)

Only-one-side time-outs: `arm` = pairs where only the arm timed out, `ref` = only the reference did. p = exact two-sided sign test on these discordant pairs.

| arm | vs 1 (M1): only arm / only ref | p | vs 3 (M2 default): only arm / only ref | p |
|---|---|---:|---|---:|
| 1 M1 binary | - | - | 13 / 17 | 0.5847 |
| 2 baseline | 7 / 12 | 0.3593 | 14 / 23 | 0.1877 |
| 3 M2 default | 17 / 13 | 0.5847 | - | - |
| 4 M2 EQUIV string | 0 / 2 | 0.5000 | 12 / 18 | 0.3616 |
| 5 M2 --no-reusetrail | 14 / 13 | 1.0000 | 12 / 15 | 0.7011 |
| 6 M2 --no-rootsimp | 17 / 15 | 0.8601 | 12 / 14 | 0.8450 |
| 7 M2 --no-tiers --no-glueupdate | 30 / 16 | 0.0541 | 26 / 16 | 0.1641 |
| 8 M2 M1 trigger+target (tiers kept) | 18 / 12 | 0.3616 | 13 / 11 | 0.8388 |
| 9 M2 M1 reduce policy | 17 / 11 | 0.3449 | 14 / 12 | 0.8450 |
| 10 M2 --no-glueupdate | 21 / 17 | 0.6271 | 17 / 17 | 1.0000 |
| 11 M2 --no-reusetrail --no-rootsimp | 17 / 17 | 1.0000 | 13 / 17 | 0.5847 |

## Paired comparison, `dl`, the 8 pass instances (160 pairs)

Only-one-side time-outs: `arm` = pairs where only the arm timed out, `ref` = only the reference did. p = exact two-sided sign test on these discordant pairs.

| arm | vs 1 (M1): only arm / only ref | p | vs 3 (M2 default): only arm / only ref | p |
|---|---|---:|---|---:|
| 1 M1 binary | - | - | 11 / 15 | 0.5572 |
| 2 baseline | 4 / 6 | 0.7539 | 12 / 18 | 0.3616 |
| 3 M2 default | 15 / 11 | 0.5572 | - | - |
| 4 M2 EQUIV string | 0 / 2 | 0.5000 | 10 / 16 | 0.3269 |
| 5 M2 --no-reusetrail | 11 / 8 | 0.6476 | 10 / 11 | 1.0000 |
| 6 M2 --no-rootsimp | 14 / 10 | 0.5413 | 10 / 10 | 1.0000 |
| 7 M2 --no-tiers --no-glueupdate | 27 / 12 | 0.0237 | 24 / 13 | 0.0989 |
| 8 M2 M1 trigger+target (tiers kept) | 16 / 10 | 0.3269 | 11 / 9 | 0.8238 |
| 9 M2 M1 reduce policy | 15 / 9 | 0.3075 | 12 / 10 | 0.8318 |
| 10 M2 --no-glueupdate | 18 / 11 | 0.2649 | 16 / 13 | 0.7111 |
| 11 M2 --no-reusetrail --no-rootsimp | 14 / 13 | 1.0000 | 11 / 14 | 0.6900 |

## Paired comparison, `plain`, all instances (240 pairs)

Only-one-side time-outs: `arm` = pairs where only the arm timed out, `ref` = only the reference did. p = exact two-sided sign test on these discordant pairs.

| arm | vs 1 (M1): only arm / only ref | p | vs 3 (M2 default): only arm / only ref | p |
|---|---|---:|---|---:|
| 1 M1 binary | - | - | 27 / 27 | 1.0000 |
| 2 baseline | 3 / 4 | 1.0000 | 27 / 28 | 1.0000 |
| 3 M2 default | 27 / 27 | 1.0000 | - | - |
| 4 M2 EQUIV string | 0 / 3 | 0.2500 | 26 / 29 | 0.7877 |
| 5 M2 --no-reusetrail | 12 / 9 | 0.6636 | 27 / 24 | 0.7798 |
| 6 M2 --no-rootsimp | 27 / 26 | 1.0000 | 3 / 2 | 1.0000 |
| 7 M2 --no-tiers --no-glueupdate | 25 / 24 | 1.0000 | 9 / 8 | 1.0000 |
| 8 M2 M1 trigger+target (tiers kept) | 25 / 29 | 0.6835 | 6 / 10 | 0.4545 |
| 9 M2 M1 reduce policy | 25 / 28 | 0.7838 | 7 / 10 | 0.6291 |
| 10 M2 --no-glueupdate | 25 / 29 | 0.6835 | 4 / 8 | 0.3877 |
| 11 M2 --no-reusetrail --no-rootsimp | 16 / 11 | 0.4421 | 27 / 22 | 0.5682 |

## Paired comparison, `plain`, the 8 pass instances (160 pairs)

Only-one-side time-outs: `arm` = pairs where only the arm timed out, `ref` = only the reference did. p = exact two-sided sign test on these discordant pairs.

| arm | vs 1 (M1): only arm / only ref | p | vs 3 (M2 default): only arm / only ref | p |
|---|---|---:|---|---:|
| 1 M1 binary | - | - | 27 / 10 | 0.0076 |
| 2 baseline | 0 / 0 | 1.0000 | 27 / 10 | 0.0076 |
| 3 M2 default | 10 / 27 | 0.0076 | - | - |
| 4 M2 EQUIV string | 0 / 1 | 1.0000 | 26 / 10 | 0.0113 |
| 5 M2 --no-reusetrail | 4 / 2 | 0.6875 | 27 / 8 | 0.0019 |
| 6 M2 --no-rootsimp | 10 / 26 | 0.0113 | 1 / 0 | 1.0000 |
| 7 M2 --no-tiers --no-glueupdate | 7 / 24 | 0.0033 | 7 / 7 | 1.0000 |
| 8 M2 M1 trigger+target (tiers kept) | 8 / 27 | 0.0019 | 4 / 6 | 0.7539 |
| 9 M2 M1 reduce policy | 8 / 26 | 0.0029 | 5 / 6 | 1.0000 |
| 10 M2 --no-glueupdate | 8 / 29 | 0.0008 | 2 / 6 | 0.2891 |
| 11 M2 --no-reusetrail --no-rootsimp | 4 / 2 | 0.6875 | 27 / 8 | 0.0019 |

## Attribution (`-dl`, all instances)

Arm 3 time-outs 70, arm 1 time-outs 66, excess 4; arm 3 vs arm 1 discordant 17 / 13, p = 0.5847.

**Outcome: no regression shown at 20 seeds** (arm 3 is not worse than arm 1 with p < 0.05).

## Reading

- Under `-dl` over all 12 instances, M2 default has 70 time-outs of 240 against 66 for M1 (excess 4); discordant
  pairs 17 / 13, p = 0.58. **No regression shown at 20 seeds**, so by the stated criterion no item is attributed
  and the single-switch table is not evaluated.
- The six-seed picture of J3 is reproduced exactly for arm 3 (seeds 1-6: `jctc8-pass` 3 time-outs, `jctc2-pass`
  3; M1: 0 and 0), the other 14 seeds add 3 and 1: over 20 seeds `jctc8-pass` is 6 against 3 (M1), `jctc2-pass` 4
  against 0, discordant 5 / 2 (p = 0.45) and 4 / 0 (p = 0.125). The effect on these two instances is a count of
  a few runs, not significant.
- Arm 7 (`--no-tiers --no-glueupdate`, schedule kept) is the worst arm under `-dl` (80 time-outs); against M1 it is
  borderline on all instances (30 / 16, p = 0.054) and nominal-significant on the pass instances (27 / 12,
  p = 0.024); against arm 3 it is not significant (26 / 16, p = 0.16). Not a finding for the default.
- Control `plain`, 8 pass instances: M2 default is better than M1 (10 / 27, p = 0.008), and the benefit disappears
  with `--no-reusetrail` (arm 5: 27 / 8 against arm 3), also in arm 11. Over all 12 instances the sign is
  neutral (27 / 27) because `jctc10-fail` and `jctc14-unrolled-fail` get worse in arms 3, 6, 7, 8, 9, 10 (`jctc10-fail`: 17 to 19 time-outs
  of 20 against 6 for M1 and 5 for the baseline; the EQUIV arm 4 has 5), i.e. in
  every arm that keeps trail reuse; arms 5 and 11 (reuse off) have 11. This is outside the question of the task and reported as observed.
- Time-outs at 60 s on this heavy-tailed family are counts, not speed-ups; no claim about speed is made.

The default decision is the coordinator's in M2 round 2 (J3).
