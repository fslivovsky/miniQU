#!/bin/bash
# One benchmark run (one solver configuration, one seed) as a Slurm job array, one instance per task.
#
#   ls $BENCH_DIR | grep '\.qcir$' | sort > instances.txt            # once; 376 lines
#   sbatch --array=1-376 bench/cluster/array.sbatch TAG SEED "SOLVER ARGS"
#   python3 bench/cluster/merge.py --results-dir $RESULTS --list instances.txt TAG   # after the array ended
#
# Example, default configuration and -dl of the new solver and of the baseline, seed 1, 900 s:
#   sbatch --array=1-376 bench/cluster/array.sbatch new-default-t900-s1 1 ""
#   sbatch --array=1-376 bench/cluster/array.sbatch new-dl-t900-s1      1 "-dl"
#   SOLVER=$BASE SEED_ARGS="-rnd-init -rnd-seed={seed}" \
#     sbatch --array=1-376 bench/cluster/array.sbatch base-default-t900-s1 1 ""
#
# Each task calls bench/run.py for its instance with one job on the core Slurm gave it and writes
# $RESULTS/TAG.parts/<index>/ (results.csv, stats.csv, meta.json; logs of failed runs in
# $RESULTS/TAG.logs/). A task that is started again
# (requeue, or a second sbatch for the indices that failed) skips an instance that already has a row.
#
# Lines marked ADAPT depend on the cluster or the scheduler. For another scheduler only three
# things are needed: the resource request (one core, MEM_GB + 1 GB, TIMEOUT + slack), the task
# index (SLURM_ARRAY_TASK_ID here; PBS: PBS_ARRAY_INDEX, SGE: SGE_TASK_ID, LSF: LSB_JOBINDEX), and
# a node-local scratch directory.

#SBATCH --job-name=miniqu-bench
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=9G                  # ADAPT: MEM_GB + 1 GB (run.py enforces MEM_GB itself, by RSS)
#SBATCH --time=00:20:00           # ADAPT: TIMEOUT plus start-up, here for 900 s; proofs need much more
#SBATCH --output=slurm-logs/%x-%A_%a.out   # ADAPT: the directory must exist before sbatch
##SBATCH --partition=NAME         # ADAPT
##SBATCH --constraint=CPUMODEL    # ADAPT: one CPU model for all runs that are compared by time
##SBATCH --exclusive=user         # ADAPT: see the note on neighbours in doc/rewrite/HANDOFF.md

set -u
TAG=${1:?usage: array.sbatch TAG SEED "SOLVER ARGS"}
SEED=${2:?seed (0 = deterministic default, no seed option)}
ARGS=${3-}

# ADAPT: paths (all on a file system that every node sees, except SCRATCH).
REPO=${REPO:-$HOME/miniQU}
WORK=${WORK:-$HOME/miniqu-work}
SOLVER=${SOLVER:-$WORK/build/release/miniQU}
BENCH_DIR=${BENCH_DIR:-$HOME/benchmarks/qcir}
LIST=${LIST:-$REPO/bench/cluster/instances.txt}
RESULTS=${RESULTS:-$WORK/results}
SCRATCH=${SLURM_TMPDIR:-${TMPDIR:-/tmp}}         # ADAPT: node-local scratch
TIMEOUT=${TIMEOUT:-900}
MEM_GB=${MEM_GB:-8}
SEED_ARGS=${SEED_ARGS:---seed=\{seed\}}          # baseline: SEED_ARGS="-rnd-init -rnd-seed={seed}"
# Extra run.py options, for instance a proof run (needs --mem of PROOF_MEM + 1 GB and a long --time):
#   EXTRA="--proof-check --proof-max-solve-sec 900 --proof-timeout 3600 --proof-mem-gb 32 --checker PATH --trim PATH"
EXTRA=${EXTRA:-}

INDEX=${SLURM_ARRAY_TASK_ID:?not inside a job array}       # ADAPT: task index of the scheduler
INSTANCE=$(sed -n "${INDEX}p" "$LIST")
[ -n "$INSTANCE" ] || { echo "no line $INDEX in $LIST"; exit 2; }
# The core this task may use (run.py pins the solver with taskset, so it must be an allowed one).
CORE=$(python3 -c 'import os; print(min(os.sched_getaffinity(0)))')

mkdir -p "$RESULTS/$TAG.parts" "$SCRATCH/miniqu-$$"
# shellcheck disable=SC2086
python3 "$REPO/bench/run.py" --solver "$SOLVER" --args="$ARGS" --seed "$SEED" --seed-args="$SEED_ARGS" \
    --timeout "$TIMEOUT" --mem-gb "$MEM_GB" --jobs 1 --cores "$CORE" \
    --bench-dir "$BENCH_DIR" --instances "$BENCH_DIR/$INSTANCE" \
    --results-dir "$RESULTS/$TAG.parts" --tag "$(printf %04d "$INDEX")" \
    --log-dir "$RESULTS/$TAG.logs" \
    --proof-dir "$SCRATCH/miniqu-$$" --proof-cores "$CORE" --proof-jobs 1 $EXTRA
status=$?
rm -rf "$SCRATCH/miniqu-$$"
exit $status
