#!/bin/bash
# Does the neighbourhood matter?  One target instance on one core, the other seven instances of
# the DW group looping on the same L3 cache with baseline or new neighbours.
#
#   bench/cross.sh TARGET_INSTANCE          (e.g. DW-unsat-10-25-1)
#   env: BASE=baseline binary (default: the frozen one), NEW=new binary (required), BASECORE=8, T=40 (limit of a neighbour run),
#        BENCH_DIR
#
# For every round (2) and every pair (target binary x neighbour binary) it prints
# "sha256 ARM HASH PATH" for both binaries, then "TARGET target=base|new neighbours=base|new round=N user=SECONDS".  A target that is slower with
# new neighbours than with baseline neighbours suffers from their cache footprint; one that is
# slower with either neighbours as new than as base is slower itself.  Exits 2 if the cores are
# not inside one L3 group; kills only the process groups it started.
here=$(dirname "$(readlink -f "$0")")
. "$here/l3lib.sh"

BASE=${BASE:-$BASELINE} BASECORE=${BASECORE:-8} T=${T:-40}
NEW=${NEW:?set NEW to the binary under test}
target=${1:?usage: $0 TARGET_INSTANCE}
print_sha base "$BASE"
print_sha new "$NEW"
require_one_l3 "$BASECORE" 8
command_of() { if [ "$1" = base ]; then echo "$BASE -rnd-init -rnd-seed=1"; else echo "$NEW --seed=1"; fi; }

for round in 1 2; do for x in base new; do for y in base new; do
  core=$BASECORE groups=""
  for name in $DW_GROUP; do
    if [ "$name" = "$target" ]; then tcore=$core
    else groups="$groups $(loop_on_core $core $T "$(command_of $y)" "$BENCH_DIR/$name.qcir")"; fi
    core=$((core + 1))
  done
  sleep 2 # let the neighbours fill the cache
  /usr/bin/time -f "$target target=$x neighbours=$y round=$round user=%U" \
    taskset -c $tcore $(command_of $x) "$BENCH_DIR/$target.qcir" 2>&1 >/dev/null | grep target
  kill_groups $groups
done; done; done
