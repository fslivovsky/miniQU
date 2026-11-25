# Benchmark and regression tooling

Python 3 standard library only. All large artifacts live in
`/home/ec2-user/miniqu-work` (outside the repo); only small CSV/markdown results
are committed under `bench/results/TAG/`.

## Layout of /home/ec2-user/miniqu-work

| path | content |
|---|---|
| `baseline-src/` | git worktree of commit c39005a (frozen reference sources) |
| `baseline-build/` | CMake release build tree of the baseline |
| `baseline/miniQU`, `baseline/GIT_HASH` | the frozen reference binary. Never rebuild it from changed sources. |
| `proofs/` | temporary proof files (deleted after checking) |
| `logs/` | logs of failed runs, build logs |
| `regress/` | scratch space of tests/regress.sh |

Rebuild from scratch:

    cd /home/ec2-user/miniQU && git checkout rewrite/cadical-style   # created from c39005a
    mkdir -p /home/ec2-user/miniqu-work/{logs,proofs,baseline}
    git worktree add /home/ec2-user/miniqu-work/baseline-src c39005a   # detached
    cmake -S /home/ec2-user/miniqu-work/baseline-src -B /home/ec2-user/miniqu-work/baseline-build -DCMAKE_BUILD_TYPE=Release
    taskset -c 0-47 make -C /home/ec2-user/miniqu-work/baseline-build -j16
    cp /home/ec2-user/miniqu-work/baseline-build/miniQU /home/ec2-user/miniqu-work/baseline/miniQU
    echo c39005a > /home/ec2-user/miniqu-work/baseline/GIT_HASH
    # Lean checker (nothing of Mathlib is compiled, only downloaded)
    cd /home/ec2-user/qu-check && git submodule update --init && taskset -c 0-47 lake build
    # binary: /home/ec2-user/qu-check/.lake/build/bin/qlrup-check [--stats] FORMULA.qcir PROOF
    # (its own test.sh also works)

Benchmarks: `/home/ec2-user/benchmarks/qcir` (376 .qcir files, from ~/benchmarks/qcir.zip).

## Core convention

Timed benchmark jobs run on the upper half of the cores, one core per job (`taskset`); every
other heavy command (builds, fuzzing, proof checking) runs on the lower half
(`taskset -c 0-$((nproc/2-1))`) and uses at most ~16 parallel jobs. On 96 cores: timed jobs on
cores 48-95, everything else on 0-47. run.py's defaults and tests/regress.sh follow this, computed
from the number of cores of the machine; run.py exits before starting a job if a core of `--cores`
or `--proof-cores` does not exist or `--jobs` exceeds the cores given.

Timings are comparable only between runs on the same instance type with the same harness
settings (ROADMAP 0.3). The old results `baseline-t180`, `baseline-dl-t180` and `baseline-t900`
(64 jobs on the former 128-core machine) serve verdict checks only. A same-machine baseline run is
tagged `baseline-c<NPROC>-<config>-t<TIMEOUT>` (frozen baseline binary, identical jobs, cores,
memory limit, timeout and seeds as the run it is compared with) and is reused only if its
`meta.json` matches; otherwise it is run first.

## run.py

    python3 bench/run.py --solver PATH --tag TAG --timeout 300 [--args "-opt1 -opt2"] [--seed S]
        [--jobs N/2] [--cores N/2-(N-1)] [--mem-gb 8] [--instances GLOB|FILE.txt|NAMES...]
        [--proof-check [--proof-max-solve-sec 60] [--proof-timeout 3600] [--proof-mem-gb 32] [--proof-max-gb 8]]

Defaults are the fixed parameters of ROADMAP 0.3 for a machine of N cores: `--jobs N/2 --mem-gb 8
--cores N/2-(N-1)` (96 cores: `--jobs 48 --cores 48-95`).

* Each instance runs once, pinned to one core; wall time, CPU time and peak RSS
  are recorded. Timeout (wall) and memory limit (RSS) are enforced by killing
  the process group.
* Verdict: exit code 10 = SAT, 20 = UNSAT, cross-checked with the printed
  `SATISFIABLE`/`UNSATISFIABLE` line (disagreement gives result `MISMATCH`).
  Other results: `TIMEOUT`, `MEMOUT`, `TOOLARGE` (a `{proof}` file reached `--proof-max-gb`), `ERROR`.
* **Seeds.** `--seed S` is recorded in `meta.json` and replaces `{seed}` in `--args`.
  `--seed-args` (default `--seed={seed}`) is appended to the solver arguments only when `S > 0`, so
  seed 0 is the deterministic default and uses no seed argument. For the baseline use
  `--seed-args "-rnd-init -rnd-seed={seed}"`.
* **Counters.** Every solver is run with `-verb=1`; the statistics it prints go to `stats.csv`
  (`instance,counter,value`): the `c stat` lines of the new solver, and `conflicts`, `decisions`,
  `propagations`, `restarts` parsed from the baseline's statistics block. Runs killed by a limit
  have none.
* Output in `bench/results/TAG/`: `results.csv`
  (instance,family,result,exit,wall,cpu,rss_mb,proof_status,proof_check_sec,proof_bytes,proof_trim_bytes),
  `stats.csv` and `meta.json` (solver path, sha256 and git hash, args, seed, jobs, mem_gb, cores,
  timeout, hash of the instance list, proof limits, date, host, command line). Resumable: rerunning
  with the same tag skips instances already in the CSV; a run with different parameters under an
  existing tag is refused (delete the directory for a fresh run). Core dumps are disabled.
* `--proof-check`: after the timed phase, every instance solved in at most `--proof-max-solve-sec`
  (up to the timeout: every solved instance) is re-run with `-proof=FILE` (extra options
  `--proof-args`, default `-proof-binary`; time limit `--proof-solve-timeout`, default twice
  `--timeout`) and the proof is checked with qlrup-check (limits `--proof-timeout` seconds,
  `--proof-mem-gb`). If the checker runs out of time or memory the proof is trimmed with
  `qlrup-trim` and checked again; `proof_trim_bytes` is then set and the report counts it as
  "after trimming". A proof file above `--proof-max-gb` (default 8) is abandoned. Every proof is
  deleted after its check. `proof_status`: `ok`, `rejected`, `wrong_verdict`, `check_error`
  (bugs: run.py exits 1), `check_timeout`, `check_memout`, `too_large`, `solve_*` (the proof run did
  not finish or gave another result; coverage gaps), `n/a` when not attempted. The proof phase
  runs on `--proof-cores` (default: the lower half, `0-(N/2-1)`) with `--proof-jobs` (default 16) jobs, at most 6 when
  `--proof-timeout` is at least 3600.
* **Timed proof-on runs** (proof overhead): `--args "-proof-binary -proof={proof}"`; `{proof}` is
  replaced by a file in the work directory that is deleted after the run; `proof_bytes` is
  recorded, with `--trim-size` also the size after `qlrup-trim`. Cannot be combined with `--proof-check`.
* `--instances` takes globs relative to `--bench-dir`, paths, or a `.txt` list of names
  (lines starting with `#` are comments). Options whose value starts with `-` must be written
  `--args=-opt` (argparse); an option string with several words works as `--args "-dl -verb=1"`.

## compare.py

    python3 bench/compare.py TAG_A TAG_B [TAG_C ...] [--out FILE] [--cactus FILE.csv] [--top 10]
    python3 bench/compare.py --paired A_TAGS -- B_TAGS [--force] [--out FILE]

Plain mode: markdown report with result DISCREPANCIES and errors first (blocking bugs), solved
SAT/UNSAT/total, PAR2 (penalty 2x timeout), unique solves, per-family table, top
speedups/regressions relative to the first tag, proof statistics and coverage, and cactus data
(sorted solve times per tag) as CSV. Only instances present in every run are compared; a warning is
printed when the timeouts differ. Family = leading alphabetic prefix of the file name
(`chess`, `ci`, `klieber`, ...); names starting with a digit form `numeric`. Informational; no
acceptance statement may rest on it.

**Paired mode** is the evidence of ROADMAP 0.3. A and B are run sets: the same binary and
configuration over a list of seeds, one tag per seed. `compare.py` refuses (exit status 3) when
`jobs`, `mem_gb`, `cores`, `timeout` or the instance list differ between any two of the runs, or
when the seed lists of A and B differ; `--force` compares anyway and puts `# NOT COMPARABLE` at the
top. The report has: discrepancies, solver errors and rejected proofs first; the parameters; the
PAR2 difference `B - A` (instance score = mean PAR2 over the seeds) with its 95% bootstrap interval
(10000 resamples over instances, fixed generator seed, percentile method); the sign test with
margin `max(1 s, 10% of the smaller score)` and the two-sided binomial p-value; the verdict
(`better`, `worse` or `no measurable difference`) and the line "B is not worse than A: yes/no", all
as defined in ROADMAP 0.3; the section **Identical searches** (below); solved (SAT/UNSAT/total) and PAR2 per seed and the noise band; the
instances gained and lost in a majority of seeds, by name; a per-family table; the largest
differences; instances solved by both whose peak RSS in B exceeds A's by more than 10%; and the
proof coverage table (solved, attempted, accepted, rejected, checker timeout, checker memout, too
large, checker error, proof run unfinished, not attempted; every non-accepted instance by name).
`bench/test_compare.py` (run by ctest) tests this on synthetic CSVs.

The `## Parameters` section also lists every run of both sets with its tag and the `date` of its
`meta.json`, sorted by date ("Order in which the runs started"), so that the order of the arms is
visible. The section `## Identical searches` follows `## Result`. For each seed the A run and the B
run are paired; an instance qualifies if both solved it with the same result, both have a
`conflicts` counter in `stats.csv` and the counters are equal, and A's `cpu` exceeds 1 s. Both
arms then ran the same search, so the ratio `cpu_B / cpu_A` measures engine speed. The report has
a table per seed (n, geometric mean, number slower and faster) and a row with the instances pooled
over the seeds (geometric mean over the seeds of an instance first), a per-family table (marked
`> 1.10` for families of at least 3 instances above 1.10), and the 15 largest and 5 smallest
ratios. Without `stats.csv` it says `no instance with equal conflict counts`.

## cluster/ (Slurm templates, merge.py)

    sbatch bench/cluster/node.sbatch TAG SEED "SOLVER ARGS"                    # one run on one exclusive node
    sbatch --array=1-376 bench/cluster/array.sbatch TAG SEED "SOLVER ARGS"     # one job per instance
    python3 bench/cluster/merge.py [--results-dir DIR] [--list instances.txt] [--allow-missing] TAG [TAG ...]

`node.sbatch` calls `run.py` once for all instances; its result directory is an ordinary run.
`array.sbatch` calls `run.py` once per instance (one job on the core the scheduler assigned) and
writes `DIR/TAG.parts/<index>/`; `merge.py` joins the parts into `DIR/TAG/` (`results.csv`,
`stats.csv`, `meta.json` with `jobs` 1, `cores` "array" and the hash of the whole instance list), so
that `compare.py`, `compare.py --paired` and `gate.py` read it like any run. It refuses parts that
differ in solver hash, options, seed, time-out or memory limit, an instance in two parts, and
(without `--allow-missing`) an instance of `--list` without a row. Paths and limits come from the
environment (`REPO`, `WORK`, `SOLVER`, `BENCH_DIR`, `RESULTS`, `TIMEOUT`, `MEM_GB`, `SEED_ARGS`,
`EXTRA`); lines marked `ADAPT` are specific to the cluster or the scheduler. Tested by executing
`array.sbatch` by hand with `SLURM_ARRAY_TASK_ID` set, never under Slurm. Plan and examples:
`doc/rewrite/HANDOFF.md`, section 3.

## gate.py

    python3 bench/gate.py --pair default:BASE_TAGS:NEW_TAGS --pair dl:... --report mode1:... [--out FILE]
        [--confirm default:BASE_TAGS:NEW_TAGS ...] [--self NAME:TAGS_1:TAGS_2 ...]
        [--results-dir DIR] [--pooled-limit 1.04] [--family-limit 1.10] [--family-min 3] [--force]

Evaluates the identical-search gate (section **Identical searches** of `compare.py --paired`, the same
`paired.IdenticalSearches`) for every configuration, in the order given. A is the reference, B the
new binary; tags are comma separated, one per seed, and loaded and checked for comparability
exactly as `compare.py --paired` does (exit status 3 unless `--force`). Per configuration the output
has one line `pooled identical searches: n=..., geometric mean new/reference = X, limit L: PASS|FAIL`
with the per-seed values, the complete per-family table (verdict `PASS`, `FAIL` for n >= 3 and a
geometric mean above 1.10, or `n < 3` = not gated, value printed), the instances that hit the memory
limit (result string `MEMOUT`) with the number of runs per arm, and the number of `ERROR` /
`MISMATCH` rows. A `--report` configuration (mode 1 in M1) is evaluated the same way, but its lines
read `REPORT (above, to be explained)` and do not change the exit status. The last lines are a table
of all FAIL, NOISE and REPORT lines and `GATE: PASS` or `GATE: FAIL (k lines)`; exit status 0 or 1. The
default pooled limit 1.04 is the ROADMAP's "at most about 1.03" with the 1-2% resolution of three
seeds (review M1-r2, section 5). A configuration without any identical search is a FAIL. 
**Noise rule** (STATUS "M2 plan and decisions", H1). A family can fail by chance when an instance is bimodal under
the benchmark load. A failing gate ends with the hint to rerun the configuration back to back (same binaries, same
seeds, new tags) and to pass it as `--confirm NAME:BASE_TAGS:NEW_TAGS`, a second pair of the `--pair` of the same
NAME. Then a family that FAILs in the pair and is within the limit in the confirm pair reads
`NOISE (first X, repeat Y)` and does not fail the gate; one above the limit in both reads `FAIL (repeated)` and
does. The pooled line is never excused, a family that is missing in the confirm pair keeps its FAIL, and the full
output of the confirm pair is printed as `NAME (confirm)`. `--self NAME:TAGS_1:TAGS_2` takes two runs of the same
binary and prints their pooled and family ratios as information (no verdict): the spread of pure noise on this
machine, to compare a FAIL with. Command for a milestone round:

    python3 bench/gate.py \
      --pair default:baseline-c96-default-t60-s1,baseline-c96-default-t60-s2,baseline-c96-default-t60-s3:M1-r3-default-s1,M1-r3-default-s2,M1-r3-default-s3 \
      --pair dl:baseline-c96-dl-t60-s1,baseline-c96-dl-t60-s2,baseline-c96-dl-t60-s3:M1-r3-dl-s1,M1-r3-dl-s2,M1-r3-dl-s3 \
      --report mode1:baseline-c96-mode1-t60-s1:M1-r3-mode1-s1 --out bench/results/M1-r3-reports/gate.md

`bench/test_gate.py` (ctest `bench-gate`) tests it on synthetic result directories.

## Benchmark reports

1. The report contains the output of `gate.py` verbatim for default and `-dl` (`--pair`) and mode 1
   (`--report`), i.e. the per-family identical-search table of every configuration.
2. The report evaluates the gate of the round as written in ROADMAP.md line by line, each line with
   its measured value and `met` / `not met`.
3. "Blocking items: none" may only be written when `gate.py` exits 0 or every failing line is
   covered by a decision recorded in STATUS.md, which is then cited.
4. Instances that hit the memory limit are named (the memory-limit line of `gate.py`).
5. The order in which the arms ran and which runs were reused are stated.

## load_measure.py

    python3 bench/load_measure.py --a BIN --a-args "-rnd-init -rnd-seed=1" --b BIN --b-args "--seed=1" \
        --tag TAG [--a-name N] [--b-name N] [--instances bench/load-instances.txt] [--rounds 2] \
        [--cores 0-47] [--timeout 60] [--bench-dir DIR] [--force]

CPU time (user) of two binaries on **identical searches under the load of a benchmark run**.

*Placement.* `run.py` hands the name-sorted instances to the cores one by one, so the 8 cores that
share an L3 cache (the machine has 12 caches of 8 cores) run 8 neighbouring names, usually one
family, and a core takes the next job as soon as its job ends. `load_measure.py` reproduces
this: `bench/load-instances.txt` is a list of **groups**, blocks of at most 8 instance names
separated by blank lines (`#` comment lines above a block say why it was chosen). Group g runs
on the g-th L3 group of `--cores`, instance j of the group on the j-th core of that L3 group.
Every group must be a window of consecutive names of the sorted instance list (checked).
`--cores` must consist of whole L3 groups (read from sysfs; default: the lower half, six
groups); more file groups than L3 groups, more than 8 names in a group, or a group larger than
its L3 group is an error. L3 groups without a file group stay idle, and so do the remaining cores
of a group with fewer than 8 names (the report header says which). The shipped file has six
windows: the DW window (mandatory: CM-unsat-07-01-06-2 ... DW-unsat-11-26-1), two numeric ones
(4.1 and 5.2-1 regions), chess mate_in_2, chess mate_in_3 (with
chess_solving_mate_in_3_2014_FRA-CH_03) and hadw10-11/hadw11-12; each holds at least three
instances with identical searches and 1-60 s baseline CPU time in the round-2 benchmark runs.
No other family has such a window, hence two numeric windows.

*Rounds.* The arms run in **separate rounds** (A, B, A, B, ...): all processes alive at one
time are the same binary, because on an idle machine or with the two binaries interleaved a
binary with a larger cache footprint is hidden. In a round every core runs its instance in a
loop, restarting as soon as it ends, so that all cores stay busy; a single run is limited by
`--timeout`. The round ends when every core has completed at least one run (verdict or timeout);
the remaining processes are then killed and their unfinished runs discarded. Every completed run
is one CSV row; `copy` is the index of the run in the loop of its core.

The script refuses to start if another solver (a process named `miniQU`), `bench/run.py` or
`load_measure.py` is running, judged by the processes' argv, not by words in command lines
(`--force` overrides and is noted in the report); it must be the only heavy job on the machine.

Every solver runs with `-verb=1` appended to its arguments. Output in `bench/results/TAG/`:
`load.csv` (arm, round, instance, copy, core, result, user, sys, conflicts), `meta.json` (both
binaries with path, sha256 and arguments, cores, groups with their cores, rounds, timeout, date,
host, the order of the rounds with start times) and `load.md`: the placement ("L3 groups, cores
kept busy"), per instance the median user time of A and B over all completed runs and rounds,
the ratio B / A, the min-max of each arm and whether the conflict counts (from `c stat conflicts
N` or the baseline's `conflicts :` line) are equal in every run of both arms; then a table per
group (first instance, why it was chosen, n of identical searches, geometric mean of B / A).
Rows with different counts are marked `different search` and left out of the geometric means;
an instance with a timeout or another exit code than 10 / 20 is `unfinished` and also left out.
`bench/test_load_measure.py` (ctest) tests the bookkeeping with fake solvers and a fake sysfs tree.

Results with tags `M1-r2-load-*` were measured with the old placement (copies of the instances
spread over cores, families mixed inside an L3 group, a core idle once its instance was solved).
That placement reported the round-2 binary as faster where benchmark runs show it slower; those
results are **not evidence** about benchmark runs.

## l3.sh, cross.sh, nb.sh

Shell reproducers of the L3 effect on one cache (cores inside one L3 group, checked; exit 2
otherwise). Run them on the lower half of an idle machine and only while no `run.py` runs; they
kill only the process groups they started.

    # per-process user time of arms on the DW window, one process per core, arms one after the other
    taskset -c 0-47 bench/l3.sh [-c BASECORE=0] [-t SECONDS=40] [-r ROUNDS=2] [-a "EXTRA ARGS"] \
        [-i "INSTANCE NAMES"] OUT base=/home/ec2-user/miniqu-work/baseline/miniQU \
        r2=/home/ec2-user/miniqu-work/build/bench-M1-r2/miniQU
    # one target against loops of the DW neighbours with baseline or new binaries
    # (env NEW is required, BASE defaults to the frozen baseline, BASECORE=8)
    NEW=/path/to/miniQU taskset -c 0-47 bench/cross.sh DW-unsat-10-25-1
    # seven warmed-up copies of one instance as neighbours, the baseline as target
    # (env BASE, NEW unless specs are given, BASECORE=24)
    taskset -c 0-47 bench/nb.sh DW-unsat-10-25-1 20 DW-unsat-09-22-1 [name="binary args" ...]

There is no default for the binary under test (a build directory holds whatever was built last). All three
scripts print `sha256 ARM HASH PATH` for each arm's binary before they measure, so that the output says what was
measured. `l3.sh` appends one line `ROUND ARM INSTANCE USER SYS EXIT` per process to OUT (which must not
exist) and prints `l3_table.py OUT`: the mean user seconds of the first arm and, for every other
arm, its mean and the ratio to the first arm per instance, the geometric mean in the last row.
Instances with an exit status other than 10 or 20 in any run are left out (a timeout is only a
neighbour). An arm named `base*`, or whose binary is the frozen baseline, gets `-rnd-init
-rnd-seed=1`, every other arm `--seed=1`; `-a` arguments are appended for all arms.
`cross.sh` prints the user time of the target for all four combinations of target binary and
neighbour binary (is the new binary slower itself, or does it hurt its neighbours); `nb.sh`
prints the time of a baseline target next to neighbours of each given kind.

## fidelity.py and overhead.py

    python3 bench/fidelity.py TAG_BASELINE TAG_NEW [--min-time 1] [--out FILE]
    python3 bench/overhead.py TAG_WITHOUT_PROOF TAG_WITH_PROOF [--out FILE]

`fidelity.py` is the port-fidelity report of ROADMAP M1.9 from `stats.csv`: on the instances solved
by both, propagations and conflicts per CPU second (new / baseline, geometric mean, min, max; only
for instances above `--min-time` in both runs, because the new parser is faster and would otherwise
dominate the rate of short runs), the ratio of conflict counts (geometric mean, median, extremes)
and a histogram of its log2. `overhead.py` reports, for the instances solved by both, the total and
geometric-mean time ratio (instances above 1 s) of a `{proof}` run against the same run without a
proof, the proof bytes in total and per conflict, and the size after trimming.

## M1 gate commands

Tags are `m1-<new|base>-<config>-t<timeout>-s<seed>`. NEW and BASE are the release binary and
`/home/ec2-user/miniqu-work/baseline/miniQU`; results go to `bench/results/`. Start one run at a
time on the upper half of the cores (`pgrep -f bench/run.py` must be empty) and wait for it with
`timeout 540 tail --pid=PID -f /dev/null`.

    NEW=/home/ec2-user/miniqu-work/build/release/miniQU
    BASE=/home/ec2-user/miniqu-work/baseline/miniQU
    BSEED='-rnd-init -rnd-seed={seed}'

    # run sets: quick tier (60 s, seeds 1-5) and full tier (600 s, seeds 11-13), default and -dl
    for cfg in default dl; do
      opt=; [ $cfg = dl ] && opt=-dl
      for s in 1 2 3 4 5; do
        python3 bench/run.py --solver $NEW  --tag m1-new-$cfg-t60-s$s  --timeout 60 --seed $s --args="$opt"
        python3 bench/run.py --solver $BASE --tag m1-base-$cfg-t60-s$s --timeout 60 --seed $s --args="$opt" --seed-args "$BSEED"
      done
      for s in 11 12 13; do
        python3 bench/run.py --solver $NEW  --tag m1-new-$cfg-t600-s$s  --timeout 600 --seed $s --args="$opt"
        python3 bench/run.py --solver $BASE --tag m1-base-$cfg-t600-s$s --timeout 600 --seed $s --args="$opt" --seed-args "$BSEED"
      done
    done
    # modes 1 and 2, quick tier, seeds 1-3
    for mode in 1 2; do for s in 1 2 3; do
      python3 bench/run.py --solver $NEW  --tag m1-new-mode$mode-t60-s$s  --timeout 60 --seed $s --args="-mode=$mode"
      python3 bench/run.py --solver $BASE --tag m1-base-mode$mode-t60-s$s --timeout 60 --seed $s --args="-mode=$mode" --seed-args "$BSEED"
    done; done

    # proof coverage, seed 0: a proof for every solved instance, trim-and-retry, at most 6 jobs
    for cfg in default dl mode1; do
      case $cfg in default) opt=;; dl) opt=-dl;; mode1) opt=-mode=1;; esac
      python3 bench/run.py --solver $NEW --tag m1-new-$cfg-t60-s0 --timeout 60 --args="$opt" \
          --proof-check --proof-max-solve-sec 60 --proof-timeout 3600 --proof-mem-gb 32 --proof-max-gb 8
    done

    # proof overhead (the proof-free arm is the timed phase of the coverage run above)
    python3 bench/run.py --solver $NEW --tag m1-new-default-t60-s0-proof --timeout 60 \
        --args="-proof-binary -proof={proof}" --trim-size
    python3 bench/run.py --solver $NEW --tag m1-new-dl-t60-s0-proof --timeout 60 \
        --args="-dl -proof-binary -proof={proof}" --trim-size
    python3 bench/overhead.py m1-new-default-t60-s0 m1-new-default-t60-s0-proof
    python3 bench/overhead.py m1-new-dl-t60-s0 m1-new-dl-t60-s0-proof

    # reports
    python3 bench/compare.py --paired m1-base-default-t600-s{11,12,13} -- m1-new-default-t600-s{11,12,13} \
        --out bench/results/m1-gate/default-full.md
    python3 bench/compare.py --paired m1-base-dl-t600-s{11,12,13} -- m1-new-dl-t600-s{11,12,13} \
        --out bench/results/m1-gate/dl-full.md
    python3 bench/compare.py --paired m1-base-default-t60-s{1,2,3,4,5} -- m1-new-default-t60-s{1,2,3,4,5} \
        --out bench/results/m1-gate/default-quick.md       # and the same for dl, mode1 (s1-3), mode2 (s1-3)
    python3 bench/fidelity.py m1-base-default-t60-s1 m1-new-default-t60-s1 --out bench/results/m1-gate/fidelity-default.md

(The baseline's seed-0 coverage and overhead runs of P0.4 use the same commands with
`--solver $BASE`.) The fidelity report of the gate is specified for seed 0: run the two
seed-0 timed phases (`m1-new-default-t60-s0` and the same with `--solver $BASE`) and pass those.

    # QDIMACS fuzzing with the extreme collection options (release 1 300, asan 1 100), alone and combined with -dl, -mode=1 and -mode=2
    ASAN=/home/ec2-user/miniqu-work/build/asan/miniQU
    for OPT in '' -dl -mode=1 -mode=2; do
      tests/fuzz_qdimacs.sh $NEW 1 300 --reduceint=2 --tier1glue=0 --gcfrac=0 $OPT
      tests/fuzz_qdimacs.sh $ASAN 1 100 --reduceint=2 --tier1glue=0 --gcfrac=0 $OPT
    done
    # tests/regress.sh gates: release at the default 20 s timeout, asan with -t 240 (STATUS.md, "Coordinator decisions after M1 round 2", E3)
    tests/regress.sh -S -j 16 -s 1:300 -M all $NEW
    tests/regress.sh -S -j 16 -s 1:100 -M all -t 240 $ASAN

## smoke.txt

35 instances (33 names) that the baseline solves in under 3 s (mixed families, SAT and UNSAT).
`smoke-expected.csv` holds the verdicts (from the baseline, cross-checked by its
proofs). Reference results: `results/baseline-smoke` (with proof checking, all 33 proofs ok)
and `results/baseline-t5` (all 376 instances, 5 s timeout, used to choose the subset).

## tests/regress.sh

    tests/regress.sh [-s FIRST:LAST] [-j JOBS] [-n] [-S] [-F] SOLVER [-- OPTS [-- OPTS ...]]
    tests/regress.sh build/miniQU -- -no-luby -- -dl      # two configurations

Each `--` starts a configuration (a bare `SOLVER` tests default options only; with
a leading `--` the first configuration is the options after it). For every configuration:

1. tests/fuzz.sh: generators qcir_fuzz.py / qcir_gen.py; small instances are compared with the brute-force
   `tests/qcir_eval.py`, medium ones with the baseline binary (`-b`);
2. every correct fuzz instance is re-solved with proof logging and checked by the Lean checker
   (verdict must match; checker time-outs are counted as warnings only);
3. bench/smoke.txt through run.py with proof checking, compared with smoke-expected.csv.

Exit status 1 on any wrong answer, crash, rejected proof or disagreement; reproducing
commands are printed and failing instances saved in `/home/ec2-user/miniqu-work/regress/CONFIG/failed/`.
Solver timeouts only warn. `tests/fuzz.sh` can also be used alone
(`PROOF_CHECKER=... REFERENCE=baseline tests/fuzz.sh SOLVER FIRST LAST [opts]`).

## tests/check_cert.py and tests/fuzz_cert.sh

    tests/check_cert.py [--reference SOLVER] SOLVER FILE [solver options...]
    taskset -c 0-47 tests/fuzz_cert.sh SOLVER FIRST LAST [solver options...]

`check_cert.py` runs the solver with `-cert`, substitutes the `V` line into the formula (the
outermost block becomes existential and is fixed by a conjunct) and decides the result again with
`tests/qcir_eval.py` (small) or the baseline: a SAT formula with an outermost existential block must
stay SAT, an UNSAT formula with an outermost universal block must stay UNSAT; for the other
combinations only the shape of the line is checked (it must list exactly the variables of the
outermost block). `fuzz_cert.sh` runs it on the tiny and search tier of the corpus and on tiny and
large QDIMACS fuzz instances for every seed, and prints counts per status and the three smallest bad
instances with reproducing commands (see the script header for the statuses).
