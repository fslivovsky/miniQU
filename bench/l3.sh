#!/bin/bash
# Per-process CPU time of several solver binaries on the eight instances of one L3 cache.
#
#   bench/l3.sh [-c BASECORE=0] [-t SECONDS=40] [-r ROUNDS=2] [-a "EXTRA SOLVER ARGS"]
#               [-i "INSTANCE NAMES"] OUT name=binary [name=binary ...]
#
# The default instances are the DW group: eight neighbouring names of the sorted instance list,
# which share one L3 cache in a benchmark run.  Per round and per arm (arms one after the other,
# never mixed) the instances start together on the cores BASECORE.., one per core, each under
# `timeout SECONDS`.  Appended to OUT: one line "ROUND ARM INSTANCE USER SYS EXIT" per process.
# An arm named base* or the frozen baseline binary gets `-rnd-init -rnd-seed=1`, every other arm
# `--seed=1`.  The sha256 of each arm's binary is printed first, the table (mean user seconds,
# ratios to the first arm) at the end.
# Exit 2 if the cores are not inside one L3 group or OUT exists.
# Run it on an idle machine (lower half of the cores, e.g. taskset -c 0-47) and only while no
# bench/run.py is running.
here=$(dirname "$(readlink -f "$0")")
. "$here/l3lib.sh"

base=0 secs=40 rounds=2 extra="" instances=$DW_GROUP
while getopts "c:t:r:a:i:" opt; do
  case $opt in
    c) base=$OPTARG ;; t) secs=$OPTARG ;; r) rounds=$OPTARG ;; a) extra=$OPTARG ;; i) instances=$OPTARG ;;
    *) exit 2 ;;
  esac
done
shift $((OPTIND - 1))
[ $# -ge 2 ] || { echo "usage: $0 [-c BASECORE] [-t SECONDS] [-r ROUNDS] [-a ARGS] [-i INSTANCES] OUT name=binary ..." >&2; exit 2; }
out=$1; shift
[ ! -e "$out" ] || { echo "$0: $out exists" >&2; exit 2; }
count=$(wc -w <<<"$instances")
require_one_l3 "$base" "$count"
for spec in "$@"; do print_sha "${spec%%=*}" "${spec#*=}"; done

for ((round = 1; round <= rounds; round++)); do
  for spec in "$@"; do
    arm=${spec%%=*} bin=${spec#*=}
    core=$base
    for name in $instances; do
      /usr/bin/time -q -f "$round $arm $name %U %S %x" -a -o "$out" \
        taskset -c $core timeout "$secs" "$bin" $(seed_args "$bin" "$arm") $extra "$BENCH_DIR/$name.qcir" >/dev/null 2>&1 &
      core=$((core + 1))
    done
    wait
  done
done
python3 "$here/l3_table.py" "$out"
