#!/bin/bash
# One benchmark run (one configuration, one seed, all instances) on one exclusive node, as on the
# development machine: run.py starts JOBS solvers, one per core. No merge step is needed; copy
# $RESULTS/TAG into bench/results/ (or pass --results-dir to compare.py).
#
#   sbatch bench/cluster/node.sbatch TAG SEED "SOLVER ARGS"
#
# Runs that are compared by time must use the same node type, JOBS, CORES, MEM_GB and TIMEOUT
# (compare.py --paired checks jobs, cores, mem_gb, timeout and the instance list).

#SBATCH --job-name=miniqu-node
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=06:00:00           # ADAPT: about 376 * TIMEOUT / JOBS seconds in the worst case, plus proofs
#SBATCH --output=slurm-logs/%x-%j.out      # ADAPT: the directory must exist before sbatch
##SBATCH --partition=NAME         # ADAPT
##SBATCH --constraint=CPUMODEL    # ADAPT

set -u
TAG=${1:?usage: node.sbatch TAG SEED "SOLVER ARGS"}
SEED=${2:?seed}
ARGS=${3-}

REPO=${REPO:-$HOME/miniQU}                        # ADAPT: paths
WORK=${WORK:-$HOME/miniqu-work}
SOLVER=${SOLVER:-$WORK/build/release/miniQU}
BENCH_DIR=${BENCH_DIR:-$HOME/benchmarks/qcir}
RESULTS=${RESULTS:-$WORK/results}
TIMEOUT=${TIMEOUT:-900}
MEM_GB=${MEM_GB:-8}                               # ADAPT: JOBS * MEM_GB must fit into the node
SEED_ARGS=${SEED_ARGS:---seed=\{seed\}}
N=$(nproc --all)
JOBS=${JOBS:-$((N / 2))}                          # ADAPT: one job per physical core of the upper half
CORES=${CORES:-$((N / 2))-$((N - 1))}             # (with SMT: list one hardware thread per core)
EXTRA=${EXTRA:-}

# shellcheck disable=SC2086
exec python3 "$REPO/bench/run.py" --solver "$SOLVER" --args="$ARGS" --seed "$SEED" --seed-args="$SEED_ARGS" \
    --timeout "$TIMEOUT" --mem-gb "$MEM_GB" --jobs "$JOBS" --cores "$CORES" \
    --bench-dir "$BENCH_DIR" --results-dir "$RESULTS" --tag "$TAG" --log-dir "$WORK/logs" \
    --proof-dir "$WORK/proofs" $EXTRA
