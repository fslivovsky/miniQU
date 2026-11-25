# miniQU rewrite: working list for the owner

State: branch `rewrite/cadical-style` (never pushed; it exists only in the clone on the development
machine, so push it or copy the repository first). What exists and what was verified is in
`REPORT.md`. This file is the list of what to do next, in four parts: (1) set-up on a fresh machine,
(2) the postponed tests, (3) the benchmark plan for the cluster, (4) open decisions and work not
started.

Run times below are measured values from `STATUS.md` (machine and job count given) or are marked
as estimates. Nothing in this file was run on the desktop or on a cluster.

## 1. Build and test on a fresh machine

### 1.1 Dependencies

| what | version used here | needed for |
|---|---|---|
| C++20 compiler | GCC 11.5; clang 15.0.7 for the `release-clang` preset | everything |
| CMake | 3.22 | build, `ctest` |
| zlib (headers) | system | gzipped QDIMACS |
| Python 3, standard library only | 3.9 | `tests/*.py`, `bench/*.py` |
| `clang-format` | 15.0.7 | ctest `format` (another version may format differently and fail that test only) |
| `taskset`, `prlimit` (util-linux), `timeout` (coreutils) | system | `bench/run.py`, `tests/regress.sh` |
| Lean 4 through `elan` | toolchain `leanprover/lean4:v4.33.0-rc1` (file `lean-toolchain` of the checker) | `qlrup-check` |

### 1.2 Directory layout the scripts expect

    ~/miniQU                  this repository
    ~/miniqu-work             work directory: build trees, baseline, proofs, logs (outside the repo)
    ~/qu-check                the Lean checker
    ~/benchmarks/qcir         the 376 .qcir files (from qcir.zip, 3.4 GB)

The CMake presets put the build trees in `../miniqu-work/build/<preset>` relative to the repository,
so the work directory must be a sibling of the repository. All other paths are absolute paths of
the development machine (`/home/ec2-user/...`); see 1.5.

### 1.3 Lean checker and frozen baseline

    # Lean checker: repository git@github.com:fslivovsky/qu-check.git, branch main, commit b6a85bd,
    # unchanged by this project. The formalization is a git submodule (SSH URL).
    git clone git@github.com:fslivovsky/qu-check.git ~/qu-check
    cd ~/qu-check && git checkout b6a85bd && git submodule update --init && lake build
    # binary: ~/qu-check/.lake/build/bin/qlrup-check [--stats] FORMULA.qcir PROOF

    # Baseline = this repository at commit c39005a (MiniSat layout), release build, never changed.
    cd ~/miniQU
    mkdir -p ~/miniqu-work/{logs,proofs,baseline}
    git worktree add ~/miniqu-work/baseline-src c39005a
    cmake -S ~/miniqu-work/baseline-src -B ~/miniqu-work/baseline-build -DCMAKE_BUILD_TYPE=Release
    make -C ~/miniqu-work/baseline-build -j6
    cp ~/miniqu-work/baseline-build/miniQU ~/miniqu-work/baseline/miniQU
    echo c39005a > ~/miniqu-work/baseline/GIT_HASH        # run.py records it as the git hash

The frozen binary of the development machine has sha256 `10ff614c6694...b71c25b` (GCC 11.5); a
rebuild with another compiler is a different binary with the same search. The baseline takes its
seed as `-rnd-init -rnd-seed=N` (`bench/run.py --seed-args "-rnd-init -rnd-seed={seed}"`). Its
`-cert` output in mode 1 is not a reference (REPORT 6.1).

`tests/m1_equiv.sh` compares with the accepted M1 binary. Its sources are commit `b2018c1`:

    git worktree add ~/miniqu-work/m1-src b2018c1
    cmake -S ~/miniqu-work/m1-src -B ~/miniqu-work/build/bench-M1-r3 -DCMAKE_BUILD_TYPE=Release
    cmake --build ~/miniqu-work/build/bench-M1-r3 -j6 --target miniQU

### 1.4 Build and unit tests

    cd ~/miniQU
    cmake --preset release && cmake --build --preset release -j6    # ../miniqu-work/build/release/miniQU, qlrup-trim
    ctest --preset release -j6                                      # expected: 46 of 46

Presets: `release`, `release-clang`, `debug` (assertions, `--log`), `asan` (address and undefined
behaviour sanitizers, assertions), `log`. The build must be free of warnings (it was, with GCC 11.5
and clang 15, for all four presets at M2-T8 and for release and debug at the last source commit).
`ctest` on the development machine at `95bfa16`: 46/46 in 22 s with 16 jobs. The ctest tests
`fuzz`, `run-regressions`, `run-regressions-elim` and `encoding-diff` need the baseline binary and
the Lean checker at the paths of 1.5.

### 1.5 Paths to change

Either make the old paths exist (no file is edited; this is the variant that was in use):

    sudo mkdir -p /home/ec2-user
    sudo ln -s ~/miniqu-work ~/qu-check ~/benchmarks /home/ec2-user/

or rewrite them in the scripts (tried on a copy: no occurrence is left in `bench/*.py`,
`bench/*.sh`, `tests/*.sh`, `tests/*.py`; the scripts were not run afterwards):

    grep -rl /home/ec2-user bench/*.py bench/*.sh tests/*.sh tests/*.py | xargs sed -i "s|/home/ec2-user|$HOME|g"

Where the paths are, and what overrides them without editing:

| file | path | override |
|---|---|---|
| `bench/run.py` | benchmark directory, checker, proof directory, log directory, `qlrup-trim` | `--bench-dir`, `--checker`, `--proof-dir`, `--log-dir`, `--trim` |
| `bench/load_measure.py` | benchmark directory | `--bench-dir` |
| `bench/l3lib.sh` (`l3.sh`, `cross.sh`, `nb.sh`) | baseline, benchmark directory | `BENCH_DIR`; baseline: edit, or pass `base=PATH` / `BASE` |
| `bench/header_measure.py` | work and benchmark directory | edit (one-off measurement of M1 round 2) |
| `tests/regress.sh` | baseline, checker, scratch | `-b`, `-c`, `REGRESS_WORK` |
| `tests/run_regressions.sh` | checker | `-c` |
| `tests/fuzz.sh` | none | `REFERENCE`, `PROOF_CHECKER`, `KEEP_DIR` |
| `tests/fuzz_qdimacs.sh`, `tests/fuzz_cert.sh` | baseline, keep directory | `BASELINE`, `KEEP_DIR` |
| `tests/check_cert.py` | baseline | `--reference` |
| `tests/encoding_diff.sh` | baseline, dump tool, scratch under the work directory | `BASELINE`, `ENCODING_DUMP`; scratch: edit |
| `tests/m1_equiv.sh` | benchmark directory, M1 binary, scratch | second argument = M1 binary; the rest: edit |
| `tests/corpus_stats.py` | baseline, checker, scratch | `--solver`, `--checker`, `--work` |
| `tests/test_regress_limits.sh` | scratch | `REGRESS_WORK` |
| `CMakeLists.txt` | none; ctest `fuzz` and `run-regressions*` call the scripts with their default baseline and checker | paths above |

Cores: `tests/regress.sh` pins itself to the lower half of the cores (`taskset -c 0-(nproc/2-1)`,
last line of the script) and `bench/run.py` uses the upper half by default. On the 6-core desktop
that is cores 0-2 for tests and 3 jobs on cores 3-5 for timed runs. For test runs that should use
all six cores, change the `taskset` in the last line of `tests/regress.sh`; for timed runs keep one
job per physical core and nothing else running.

`bench/results/*/meta.json` of the existing runs name binaries under `/home/ec2-user/miniqu-work`
that will not exist any more; the files are records, nothing reads those paths.

## 2. Postponed tests, most important first

`NEW=~/miniqu-work/build/release/miniQU`, `ASAN=~/miniqu-work/build/asan/miniQU`,
`DBG=~/miniqu-work/build/debug/miniQU`; commands from the repository root. Reference times are
from the gate of M2-T8 (48-core machine, 16 jobs, 43 matrix rows); the matrix has 67 rows now, so
"scaled" means multiplied by 67/43, and on the desktop with 6 jobs about 2.7 times that again.
Any wrong verdict, rejected proof, crash or sanitizer report is a blocking bug; solver and checker
time-outs are warnings unless a stress row exceeds its limit.

| # | test | command | time |
|---|---|---|---|
| 1 | build and unit tests, four presets | `for p in release debug asan release-clang; do cmake --preset $p && cmake --build --preset $p -j6; done; ctest --preset release; ctest --preset debug; ctest --preset asan` | minutes; `ctest` release 22 s with 16 jobs |
| 2 | **full matrix, release, original seed range, smoke set, Lean** (not run since M2-T8; never with the `elim*` and `vivify*` rows beyond seeds 1:50, and not at all after the B1 fix) | `tests/regress.sh -j 16 -s 1:300 -M all $NEW` | measured 2 h for 43 rows; scaled about 3 h; desktop about 8 h (estimate) |
| 3 | **certificates** in the area of the B1 fix, which no reviewer has seen | `for O in "" "-dl" "--elim --elimint=1" "--vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce" "--elim --elimint=1 --vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce" "--elim --elimint=1 --vivify --vivifyint=1 -dl" "--no-rootsimp"; do JOBS=12 tests/fuzz_cert.sh $NEW 1 1000 $O; done` | seeds 1:30 took about 1 minute with 11 jobs (M4-T3); 1:1000 about 35 minutes per option set (estimate) |
| 4 | **sanitizer matrix** (asan + ubsan, assertions) | `tests/regress.sh -S -j 16 -s 1:100 -t 240 -M all $ASAN` | measured 35 min for 43 rows; scaled about 55 min; the `elim-inp*` rows are slow with assertions (M3-T2: slowest instance 145 s in the debug build) |
| 5 | debug build on the rows of the new techniques, with the owner re-check of elimination; the run of M3-T3 was not clean on stress limits and was not repeated | see 2.3 | not measured; expect an hour or more |
| 6 | **QDIMACS fuzz**, release 1:300 and asan 1:100, eight option sets, plus vivification (elimination is not applied to QDIMACS) | see 2.1 | measured 17 min for the eight release sets |
| 7 | smoke set with proofs alone (it is part of 2; use this after a change that does not need the corpus) | `tests/regress.sh -F -j 16 -M all $NEW` | not measured separately |
| 8 | M1 equivalence with all off-switches (also shows that `--elim=0 --vivify=0` leave the M1 search alone; not run since M2-T8) | `tests/m1_equiv.sh $NEW ~/miniqu-work/build/bench-M1-r3/miniQU` | measured 12 min |
| 9 | **Lean coverage per technique on the benchmark set** | see 2.2 | timed phase about 376 x 60 s / jobs; proof phase open (M1: 117 proofs, 3.8 GB, slowest check 329 s) |
| 10 | proofs that were never checked because the checker timed out at 120 s: rows `mode1-dl` (18 at 1:300), `vivify-mode1-dl` (3 at 1:30), `noearly` (2) | `tests/regress.sh -S -j 16 -s 1:300 -M mode1-dl,vivify-mode1-dl,noearly $NEW` after raising `--check-timeout` (an option of `tests/regress.py`, default 120; `regress.sh` does not pass it on: add it to the last line of `regress.sh`) | not measured |
| 11 | completeness after elimination on the benchmark set: no "unknown" exit, counter `modelcubes` 0, with `--elim`, `--elim --elimbound=16` and `--elim -no-earlytseitin` | see 2.3 | about 376 x 60 s / jobs per run in the worst case |
| 12 | mode 1 certificates (known defect, inherited from the baseline) | `JOBS=12 tests/fuzz_cert.sh $NEW 100 400 -mode=1` reproduces it; fix or refuse `-cert -mode=1` | minutes |
| 13 | unit tests still missing: the elimination and vivification paths of the B1 fix (empty resolvent, empty vivified constraint); elimination paths the fuzz rows never reach (two contradicting unit resolvents, `elimlearnt.cube`, the dependency reset) | to be written (`test/unit/elim.cpp`, `vivify.cpp`, `search.cpp`); list in `reviews/handover.md` section 6 | |
| 14 | longer seed ranges for the new rows (the tasks used 1:30) and seeds nobody used | `tests/regress.sh -S -j 16 -s 8001:8300 -M all $NEW` | as 2 |

Expected warnings in 2 and 4, from the last full runs (STATUS M2-T8): solver time-outs in
`noearly` (34 of 150 at release; inherited, STATUS "Fidelity note"), `mode1-dl` 3, `mode2-dl` 2;
stress rows within their limits (`restart-dl` 6 of 150, limit 8; `restart-mode1-dl` 20, limit 25;
`ema-stress-dl` 4, limit 4). Limits and their reasons: STATUS D1, E3, "Owner decision: stress-row
timeouts on the sanitizer build", H7; row `elim-inp-gc` was changed to `--reduceint=10` at
hand-over.

### 2.1 QDIMACS fuzz

Solver options are separate arguments (a quoted string with blanks is rejected).

    STRESS="--reduceint=2 --tier1glue=0 --tier2glue=0 --gcfrac=0 --rootsimpdelay=0"
    VIV="--vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce"
    for OPT in "" "-dl" "-mode=1" "-mode=2"; do
      tests/fuzz_qdimacs.sh $NEW 1 300 $OPT
      tests/fuzz_qdimacs.sh $NEW 1 300 $OPT $STRESS
      tests/fuzz_qdimacs.sh $NEW 1 300 $OPT $VIV            # mode 2: vivification is not applied
      tests/fuzz_qdimacs.sh $NEW 1 300 $OPT $VIV $STRESS
      tests/fuzz_qdimacs.sh $ASAN 1 100 $OPT $STRESS
      tests/fuzz_qdimacs.sh $ASAN 1 100 $OPT $VIV $STRESS
      tests/fuzz_qdimacs.sh $DBG 1 100 --check $OPT $VIV    # internal checker; there is no Lean proof for QDIMACS
    done

### 2.2 Lean coverage per technique on the benchmark set

One run per configuration, seed 0; a proof is written and checked for every instance solved within
`--proof-max-solve-sec`. The reference is the M1 run `M1-r3-proofcov-default-s0` (117 of 117
attempted proofs accepted). `rejected`, `wrong_verdict` or `check_error` in the column
`proof_status` is a blocking bug (`run.py` then exits 1).

    for cfg in "default:" "dl:-dl" "mode1:-mode=1" "ccmin3:--ccminmode=3" \
               "elim:--elim" "elim-dl:--elim -dl" "vivify:--vivify" "vivify3:--vivify --vivifytier=3 --vivifyint=500" \
               "vivify-dl:--vivify -dl" "both:--elim --vivify" "both-mode1-dl:--elim --vivify -mode=1 -dl"; do
      python3 bench/run.py --solver $NEW --tag proofcov-${cfg%%:*}-t60-s0 --timeout 60 --args="${cfg#*:}" \
          --proof-check --proof-max-solve-sec 20 --proof-timeout 600
    done
    python3 bench/compare.py proofcov-default-t60-s0 proofcov-elim-t60-s0 proofcov-vivify-t60-s0 proofcov-both-t60-s0   # coverage table, discrepancies

Whether elimination or vivification steps are a large part of a proof is visible in the counters of
`stats.csv` (`eliminated.*`, `resolvents.*`, `vivified.*`) of the same run. Proof size and checking
time are the columns `proof_bytes` and `proof_check_sec`. The proof phase needs up to 32 GB per
checker process (`--proof-mem-gb`) and `--proof-jobs` processes (default 16): on the desktop set
`--proof-jobs 2 --proof-mem-gb 12` or what the memory allows.

### 2.3 Commands of tests 5 and 11

    # 5: debug build, rows of the new techniques, no proofs (-n), 240 s per run
    ROWS=$(grep -o '^elim[a-z0-9-]*\|^vivify[a-z0-9-]*' tests/matrix.txt | paste -sd,)
    tests/regress.sh -S -n -j 16 -s 1:30 -t 240 -M $ROWS $DBG

    # 11: completeness after elimination; both greps must print nothing
    i=0
    for A in "--elim" "--elim --elimbound=16" "--elim -no-earlytseitin"; do
      i=$((i+1))
      python3 bench/run.py --solver $NEW --tag elim-complete-$i-t60 --timeout 60 --args="$A"
      grep ',ERROR,' bench/results/elim-complete-$i-t60/results.csv
      grep ',modelcubes,' bench/results/elim-complete-$i-t60/stats.csv | grep -v ',0$'
    done

A run that ends with "unknown" exits with a code other than 10 or 20, which `run.py` records as
`ERROR` and keeps the log of (`--log-dir`).

## 3. Benchmark plan for the cluster

### 3.1 Rules (ROADMAP 0.3, `bench/README.md`)

- One run = one binary, one option string, one seed, all 376 instances; one tag per run. Seed 0 is
  the deterministic default (no seed option); seeds 1, 2, 3 randomise the initial scores. The same
  seed list for both arms of a comparison.
- Memory limit 8 GB per job, PAR2 with penalty 2 x time-out.
- Evidence is `bench/compare.py --paired A_TAGS -- B_TAGS` (PAR2 difference with bootstrap
  interval, sign test, instances gained and lost, identical searches, proof coverage). It refuses
  run sets whose `jobs`, `cores`, `mem_gb`, `timeout`, instance list or seed lists differ.
- Any discrepancy between two runs (SAT in one, UNSAT in another), `ERROR`, `MISMATCH` or rejected
  proof is a blocking bug. Check all runs together: `python3 bench/compare.py TAG1 TAG2 ...`
  prints discrepancies first; include the old `baseline-t180`, `baseline-dl-t180` and
  `baseline-t900` (verdicts only).
- Timings are comparable only between runs collected the same way on the same CPU model. On the
  development machine the placement of jobs on shared caches changed the CPU time of identical
  searches by 12-27% in one family (STATUS "M1 round 2/3: diagnosis of B1"). Therefore: statements
  about solved instances and PAR2 may come from job arrays; statements about engine speed
  (`gate.py`, section "Identical searches") need whole exclusive nodes with a fixed placement
  (3.3, per node), or must be read as noisy.

### 3.2 Configurations

Binaries: `BASE` (baseline, seed option `-rnd-init -rnd-seed={seed}`) and `NEW` (head of the
branch). Tags: `<bin>-<config>-t<timeout>-s<seed>`.

**Stage A, the final binary against the baseline** (the benchmark stage M2 never had; 900 s):

| config | options | binaries | seeds |
|---|---|---|---|
| default | (none) | BASE, NEW | 1, 2, 3 |
| dl | `-dl` | BASE, NEW | 1, 2, 3 |
| mode1 | `-mode=1` | BASE, NEW | 1 |
| mode1-dl | `-mode=1 -dl` | BASE, NEW | 1 |
| mode2 | `-mode=2` | BASE, NEW | 1 |
| mode2-dl | `-mode=2 -dl` | BASE, NEW | 1 |
| m1equiv, m1equiv-dl | the M1-equivalent string of REPORT 2.2, with and without `-dl` | NEW | 1, 2, 3 |

20 baseline and new runs plus 6 for the M1-equivalent string. `m1equiv` against `default` is the
total effect of M2; `m1equiv` against BASE repeats the M1 parity result at 900 s.

**Stage B, every feature on and off** (NEW only; each row is one option string added to the
reference; run each in `default` and with `-dl`, seeds 1, 2, 3; first at 300 s, then the
candidates for a default change and everything that looks worse at 900 s):

| group | reference | arms |
|---|---|---|
| M2 features that are on | default | `--no-tiers --no-glueupdate`; `--no-glueupdate`; `--reducetarget=50 --reducesize --reduceint=0` (M1 reduce policy); `--no-rootsimp`; `--no-reusetrail`; `--no-reusetrail --no-rootsimp` |
| M2 features that are off | default | `--recomputetier`; `--ccminmode=2`; `--ccminmode=3`; `--restartmode=1` |
| elimination | default | `--elim`; `--elim --no-eliminp` (preprocessing only); `--elim --no-elimpre` (inprocessing only); `--elim --no-elimcube`; `--elim --no-elimclause`; `--elim --no-elimsubsume --elimboundmax=0` (the plain technique); `--elim --elimbound=16` |
| vivification | default | `--vivify`; `--vivify --no-vivifycube`; `--vivify --no-vivifyclause`; `--vivify --vivifytier=3`; `--vivify --vivifytier=1`; `--vivify --no-vivifyonce` |
| both | default | `--elim --vivify` |
| modes | `-mode=1`, `-mode=1 -dl` (seed 1) | `--elim`; `--vivify`; `--elim --vivify`. Mode 2: neither technique is applied (notice at `--verb=1`), so mode 2 has no arm |
| gate placement | default | `-no-earlytseitin`; `-no-earlytseitin --elim` (elimination interacts with the placement: the rightmost condition) |

That is 26 arms and the reference in two configurations with three seeds (162 runs) plus 8 mode-1
runs (three arms and the reference, with and without `-dl`). Parameters to tune afterwards, one at a time, only for the techniques that survive:
`elimint`, `elimticks`, `elimocclim`, `elimclslim`, `elimboundmax`; `vivifyint`, `vivifyticks`;
`reduceint`, `reducetarget`, `tier1glue`, `tier2glue`, `restartint`, `restartmargin`.

**Decision rule used so far** (ROADMAP "M2 execution plan"; a starting point, the owner may set
another): an option that is off becomes a default only if its PAR2 is lower than the reference by
more than 2.0 s (the seed spread measured in M1 at 60 s) in one of `default` and `-dl` and not
higher by more than 2.0 s in the other, with no discrepancy. `compare.py --paired` prints the
difference with its interval and "better / worse / no measurable difference". The 2.0 s belong to
60 s runs; for 300 s and 900 s take the spread between the seeds of the reference instead (the
paired report prints PAR2 per seed).

**Proofs.** The coverage runs of 2.2 belong on the cluster too (per node: add the proof options to
`EXTRA`; the checker needs up to 32 GB per process). Proof overhead:
`--args="-proof-binary -proof={proof}"` as a timed run and `bench/overhead.py`.

**Cost** (estimate, from `baseline-t900`: about 195 of 376 instances reach the 900 s limit or the
memory limit): one 900 s run is about 50 core-hours, one 300 s run about 18, one 60 s run about 4.
Stage A about 1300 core-hours; stage B at 300 s about 3000 core-hours.

### 3.3 Running it

`bench/cluster/` has two Slurm templates; lines marked `ADAPT` are the ones to change for the
cluster or for another scheduler (resource request, task index variable, scratch directory, paths).
Paths are taken from the environment (`REPO`, `WORK`, `SOLVER`, `BENCH_DIR`, `RESULTS`, `TIMEOUT`,
`MEM_GB`, `SEED_ARGS`, `EXTRA`). Both call `bench/run.py`, which needs `python3`, `taskset` and
`prlimit` on the nodes and the solver binary on a shared file system (build it once on a node of
the type that runs the jobs; record its sha256, which `meta.json` stores).

**Per node** (`node.sbatch`; needed for engine-speed statements): one exclusive node runs a whole
run as on the development machine.

    mkdir -p slurm-logs
    sbatch bench/cluster/node.sbatch new-default-t900-s1 1 ""
    sbatch bench/cluster/node.sbatch new-dl-t900-s1 1 "-dl"
    SOLVER=$BASE SEED_ARGS="-rnd-init -rnd-seed={seed}" sbatch bench/cluster/node.sbatch base-default-t900-s1 1 ""

The result directory `$RESULTS/TAG` is complete; no merge. All runs of one comparison must use the
same node type and the same `JOBS`, `CORES`, `MEM_GB`, `TIMEOUT`. A run that hits the wall-time
limit of the job can be submitted again with the same tag: `run.py` skips the instances that have
a row.

**One job per instance** (`array.sbatch` and `merge.py`; for solved counts and PAR2):

    ls ~/benchmarks/qcir | grep '\.qcir$' | sort > bench/cluster/instances.txt     # 376 lines
    mkdir -p slurm-logs
    for s in 1 2 3; do
      sbatch --array=1-376 bench/cluster/array.sbatch new-default-t900-s$s $s ""
      sbatch --array=1-376 bench/cluster/array.sbatch new-elim-t900-s$s $s "--elim"
      SOLVER=$BASE SEED_ARGS="-rnd-init -rnd-seed={seed}" \
        sbatch --array=1-376 bench/cluster/array.sbatch base-default-t900-s$s $s ""
    done
    # when the arrays have ended:
    python3 bench/cluster/merge.py --results-dir $RESULTS --list bench/cluster/instances.txt \
        new-default-t900-s{1,2,3} new-elim-t900-s{1,2,3} base-default-t900-s{1,2,3}
    python3 bench/compare.py --results-dir $RESULTS --paired new-default-t900-s{1,2,3} -- new-elim-t900-s{1,2,3} \
        --out elim-vs-default.md

Each task writes `$RESULTS/TAG.parts/<index>/` with the three files of a one-instance run.
**`compare.py` cannot read the parts directly** (it reads one directory per tag and, in paired
mode, compares the hash of the instance list). `merge.py` writes `$RESULTS/TAG/` in the format of
an ordinary run: all rows sorted by instance, `stats.csv`, and a `meta.json` with `jobs` 1, `cores`
"array" and the instance hash that `run.py` would compute for the whole list. It stops if parts
differ in solver hash, options, seed, time-out or memory limit, if an instance occurs twice, or if
an instance of the list has no row (a failed task: submit those indices again with
`sbatch --array=17,203 ...` and merge again; `--allow-missing` merges anyway, and paired mode then
refuses the comparison with a complete run). Because `cores` is "array", paired mode also refuses
to compare an array run with a per-node run, which is intended.

Checked on the development machine (not under Slurm): `array.sbatch` was executed by hand with
`SLURM_ARRAY_TASK_ID` set for 6 instances and three tags (new default, new `-dl`, baseline with its
seed option); `merge.py` produced the three runs, `compare.py` printed the plain report and the
paired report with the "Identical searches" section, a missing part was reported by name, and
`--allow-missing` followed by `--paired` was refused with "instance list differs". `sbatch` itself,
the `#SBATCH` lines and `node.sbatch` were not executed (no Slurm on that machine).

Notes for arrays: `run.py` records `--mem-gb` as given, and paired mode compares the recorded
values literally, so always pass the limit the same way (the templates do). Request one core per
task and, if the cluster allows it, a single CPU model (`--constraint`); `meta.json` of the merged
run lists the hosts. For other tools: `gate.py` and `fidelity.py` read the merged directories like
any run; `load_measure.py` and `l3.sh` are for a single idle machine only.

## 4. Open decisions and work not started

Each item names where its history is.

| # | item | where | what is needed |
|---|---|---|---|
| 1 | **Defaults of the new features**: `--elim` and `--vivify` are off. | STATUS "Owner decision: wrap up in 24 hours" point 5; M3-T4 list item 5; M4-T3 list item 6; `reviews/handover.md` suggestions 4, 5 | stage B; before that, tests 2-5 and 9 of section 2. Sub-defaults that were never measured: `elimsubsume=1`, `elimboundmax=16` (the reviewer suggests 0 and `elimbound` until measured), `elimint=2000`, `vivifyint=2000`, `vivifyticks=2000000`, `vivifytier=2`, `vivifyonce=1` (with these two, the share of fuzz instances with vivified cubes fell from 87% to 20%, M4-T2) |
| 2 | **Defaults of M2 that have no evidence**: `--recomputetier`, `--ccminmode=2`, `--restartmode=1` with `-dl` were never screened; `--ccminmode=3` and `--restartmode=1` had one seed at 60 s. Trail reuse: more time-outs on `jctc10-fail` and `jctc14-unrolled-fail` without `-dl`, a gain on the pass instances. | STATUS M2-T7 open points; J12; "M3 plan and decision on M2-T11"; ROADMAP "M5+", first paragraph | stage B, group "M2 features" |
| 3 | **The M2 review that did not happen**, and with it the independent verification and the benchmark stage of M2. | STATUS "Owner decision: wrap up in 24 hours" point 1; "Coordinator decisions after M2 round 1" (J1-J13) | review of `git diff 0cff1d5..c8d00fd -- src test` (30 commits: `tier.cpp`, `simplify.cpp`, `minimize.cpp`, `restart.cpp`, `reduce.cpp`); tests 2, 4, 6, 8 of section 2; stage A |
| 4 | **The B1 fix is unreviewed** (`06c3ab6`: `certificate.cpp`, `found_empty` with the constraint before reduction, five call sites). | STATUS "Hand-over defects"; `reviews/handover.md` B1 | review; test 3 and 13 of section 2 |
| 5 | **Relaxing the rightmost condition** of elimination. Two different questions: (a) whether the condition may ignore learnt constraints (as built it does not; the owner's wording of 2026-11-24); (b) the dependency-based relaxation, which needs a written soundness argument and the owner's approval. The yield measurement that was to inform this (`bench/elim_yield.py`, both gate placements) was never written. On the 8 real files of M3-T3 the counter `elimblockedright` is 0 to 3029 per file against 690 to 29422 for `elimblockedbound`. | ROADMAP M3 "Left for later" items 1, 2; M3.0; M3.2; "M5+" item 3; STATUS "M3 plan", "Open for the owner" | owner decision; then the yield measurement, then the argument |
| 6 | **Proof gaps.** None in M1-M4 for QCIR input in modes 0 and 1. No proofs: mode 2 (checker extension needed), QDIMACS input (no format; a route through the dual encoding is ROADMAP "M5+" item 6). Proofs that exist but were not checked: test 10 of section 2. Coverage on the benchmark set exists only for the M1 binary. | ROADMAP "Summary: what QLRUP can express today", "M5+" items 6, 10, 11; REPORT 6.4, 6.8 | section 2.2; a checker extension is a decision of the owner (complete soundness proofs on a branch of `~/qu-check`) |
| 7 | **Certificates in mode 1** are invalid in the baseline and here. | STATUS "Hand-over defects", list item 1 | fix, or refuse `-cert -mode=1` |
| 8 | **The extras**: nothing started. Subsumption and strengthening of learnt constraints, failed-literal probing, equivalent literals, blocked constraints, pure literals, binary fast path, QDIMACS through the dual encoding, structural hashing of the circuit; for elimination: gate-aware elimination, backward subsumption, occurrence mode, effort relative to the search, decision variables, QDIMACS input; for vivification: irredundant constraints, decision reuse, effort shares per tier, glue recomputation. Deferred from M2: stable/focused switching, rephasing, arena order by decision order, reason-side bumping. | ROADMAP "M5+" table; M3 and M4 "Left for later"; STATUS H4; STATUS wrap-up point 6 | owner picks |
| 9 | **Profiling and parameter tuning** (the optimisation milestone): not started. The solver has `--profile=1..3` with scopes per technique (ARCH 9.3). Known cost questions: elimination rounds rebuild all occurrence lists and try every variable in every pass; the duplicate check among resolvents; vivification's uncounted work. | STATUS wrap-up point 6; M3-T2 list item 1; M3-T4 list items 2, 3; M4-T3 list items 2, 3; `reviews/handover.md` suggestions 1-3 | profiles of the slow real files of REPORT 6.7 first; then the tuning list of 3.2 |
| 10 | **900 s runs with ablations**: none exist for the new solver (longest run 60 s; `baseline-t900` is from the first machine). | STATUS wrap-up point 6; ROADMAP 0.3 | stages A and B |
| 11 | Review suggestions that are open: one shared epilogue for root strengthening, elimination and vivification (`replace_constraint`, `finish_root_round`); a notice at the default verbosity when `--elim` or `--vivify` does nothing (mode 2, QDIMACS), so that benchmark scripts do not measure a silent no-op; the dead dependency-reset path. | `reviews/handover.md` section 4 | small code tasks |
| 12 | Tooling: `tests/check_cert.py` and merged `free`/`exists` blocks; the hard-coded paths of 1.5; `regress.sh` has no option for the checker time limit; matrix rows `elim-clause-only`/`elim-cube-only` do not assert that the other counter is 0. | STATUS "Hand-over defects" item 2; M3-T3 list item 4 | small tasks |
| 13 | Decisions that are recorded and binding unless the owner changes them: stress rows and their limits (STATUS D1, E3, H7, "Owner decision: stress-row timeouts"), the watcher layout, the `jctc` noise decision (H1), no default change after M2-T11 (J3). | STATUS, the sections named | none |
