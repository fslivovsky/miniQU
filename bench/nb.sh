#!/bin/bash
# Which neighbours hurt?  Seven warmed-up copies of one instance on seven cores of an L3 cache,
# then the baseline on the eighth core running a target instance.
#
#   bench/nb.sh NEIGHBOUR_INSTANCE WARMUP_SECONDS TARGET_INSTANCE [name="binary args" ...]
#   env: BASE=baseline binary (default: the frozen one), NEW=new binary (required without specs), BASECORE=24, T=60 (limit of a neighbour run), BENCH_DIR
#
# Without specs the two neighbours are base and new (the baseline with `-rnd-init -rnd-seed=1`,
# the new binary with `--seed=1`).  Per round (2) and spec it prints
# "neigh=INSTANCE(name) target=base user=SECONDS": the user time of the baseline target depends
# only on what the neighbours do to the shared cache.  The first lines are "sha256 ARM HASH PATH".  Exits 2 if the cores are not inside one
# L3 group; kills only the process groups it started.
here=$(dirname "$(readlink -f "$0")")
. "$here/l3lib.sh"

BASE=${BASE:-$BASELINE} BASECORE=${BASECORE:-24} T=${T:-60}
[ $# -ge 3 ] || { echo "usage: $0 NEIGHBOUR_INSTANCE WARMUP_SECONDS TARGET_INSTANCE [name=\"binary args\" ...]" >&2; exit 2; }
neighbour=$1 warmup=$2 target=$3
shift 3
[ $# -gt 0 ] || set -- "base=$BASE -rnd-init -rnd-seed=1" "new=${NEW:?set NEW or give the specs} --seed=1"
print_sha target "$BASE"
for spec in "$@"; do print_sha "${spec%%=*}" "$(cut -d' ' -f1 <<<"${spec#*=}")"; done
require_one_l3 "$BASECORE" 8

for round in 1 2; do for spec in "$@"; do
  name=${spec%%=*} cmd=${spec#*=}
  groups=""
  for k in 0 1 2 3 4 5 6; do
    groups="$groups $(loop_on_core $((BASECORE + k)) $T "$cmd" "$BENCH_DIR/$neighbour.qcir")"
  done
  sleep "$warmup"
  /usr/bin/time -f "neigh=$neighbour($name) target=base user=%U" \
    taskset -c $((BASECORE + 7)) $BASE -rnd-init -rnd-seed=1 "$BENCH_DIR/$target.qcir" 2>&1 >/dev/null | grep user=
  kill_groups $groups
done; done
