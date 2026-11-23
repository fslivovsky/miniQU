# Shared by l3.sh, cross.sh and nb.sh (sourced).

BASELINE=/home/ec2-user/miniqu-work/baseline/miniQU
NEW_DEFAULT=/home/ec2-user/miniqu-work/build/release/miniQU
BENCH_DIR=${BENCH_DIR:-/home/ec2-user/benchmarks/qcir}
# The instances of one L3 cache in a benchmark run (eight neighbouring names, see load-instances.txt).
DW_GROUP="CM-unsat-07-01-06-2 DW-sat-08-22-1 DW-sat-08-23-1 DW-sat-09-26-1 DW-unsat-09-22-1 DW-unsat-09-23-1 DW-unsat-10-25-1 DW-unsat-11-26-1"

# require_one_l3 FIRST COUNT: exit 2 unless cores FIRST .. FIRST+COUNT-1 exist and share one L3 cache.
require_one_l3() {
  local first=$1 count=$2 want have c
  for ((c = first; c < first + count; c++)); do
    have=$(cat /sys/devices/system/cpu/cpu$c/cache/index3/shared_cpu_list 2>/dev/null) || {
      echo "$0: cannot read the L3 group of core $c" >&2; exit 2; }
    [ -n "$want" ] || want=$have
    [ "$have" = "$want" ] || {
      echo "$0: cores $first-$((first + count - 1)) are not inside one L3 group (core $c: $have, core $first: $want)" >&2
      exit 2; }
  done
}

# seed_args BINARY ARM: the seed arguments; the frozen baseline has other option names.
seed_args() {
  case $2 in
    base*) echo "-rnd-init -rnd-seed=1" ;;
    *) [ "$(realpath "$1")" = "$(realpath "$BASELINE")" ] && echo "-rnd-init -rnd-seed=1" || echo "--seed=1" ;;
  esac
}

# loop_on_core CORE TIMEOUT COMMAND INSTANCE: start a neighbour that restarts its instance as soon as
# it ends, in its own process group (setsid), and print the pid of the group.  kill_groups kills
# exactly these groups and nothing else; timeout --foreground keeps the solver inside the group.
loop_on_core() {
  setsid bash -c 'while :; do taskset -c "$1" timeout --foreground "$2" $3 "$4" >/dev/null 2>&1; done' \
    _ "$1" "$2" "$3" "$4" >/dev/null 2>&1 &
  echo $!
}

kill_groups() {
  local p
  for p in "$@"; do kill -- -"$p" 2>/dev/null; done
  sleep 1 # the solvers die asynchronously
}
