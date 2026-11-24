#!/bin/bash
# The M1-equivalence gate (doc/rewrite/STATUS.md, H5).
#
# Usage: tests/m1_equiv.sh NEW_BINARY [M1_BINARY]
#
# With the options in EQUIV below, the current solver has to make exactly
# the search of the accepted M1 solver (default
# /home/ec2-user/miniqu-work/build/bench-M1-r3/miniQU): the same verdict and
# the same counters of the 'c stat' block (conflicts, decisions,
# propagations, ticks, restarts, learned.*, reduced.*, reductions).  Every
# task that adds a feature with an off switch appends that switch to EQUIV
# and reruns this script; a difference is a bug in the new code, never a
# reason to edit the script.  Do not weaken it.
#
# Instances, each in the four modes '', -dl, -mode=1, -mode=2:
#  (a) every instance of bench/smoke.txt (directory /home/ec2-user/benchmarks/qcir);
#  (b) the search-tier instances of tests/corpus.py for seeds 1..40, and each
#      of them once more with STRESS appended on both sides, so that
#      reductions and garbage collections happen (the later option wins over
#      the '--reduceint=0' of EQUIV; the frozen M1 binary reads options in
#      order too).
# NEW is run with 'EQUIV MODE [STRESS]', M1 with 'MODE [STRESS]', both with
# -verb=1, a timeout of 60 s, under taskset on the lower half of the cores,
# at most 16 jobs in parallel.  A pair in which either side times out is
# skipped and counted.
#
# Output: every differing pair with both commands, then per mode the number
# of pairs compared and skipped.  Exit status 1 on any difference, on a mode
# with no pair compared, and on a failure to run.

# The M1-equivalent option string; one variable, extended by later tasks.
EQUIV="--no-tiers --no-glueupdate --reducetarget=50 --reducesize --reduceint=0 --no-recomputetier"
STRESS="--reduceint=2 --tier1glue=0 --gcfrac=0"
SEEDS=40
TIMEOUT=60
JOBS=16
INSTANCES=/home/ec2-user/benchmarks/qcir
STATS="conflicts decisions propagations ticks restarts learned.clause learned.cube reduced.clause reduced.cube reductions"

HERE=$(cd "$(dirname "$0")/.." && pwd)

# One pair: job file line "label|mode options|stress options|instance".
if [ "$1" = --job ]; then
    shift
    NEW=$1; M1=$2; RESULTS=$3; JOB=$4
    IFS='|' read -r label mode stress file <<<"$JOB"
    tag=$(echo "$JOB" | md5sum | cut -c1-16)
    new_opts="$EQUIV $mode $stress"; m1_opts="$mode $stress"
    run () { # binary options...
        local bin=$1; shift
        # shellcheck disable=SC2086
        timeout "$TIMEOUT" taskset -c "$CORES" "$bin" -verb=1 $* "$file" 2>&1
        echo "exit $?"
    }
    new_out=$(run "$NEW" $new_opts); m1_out=$(run "$M1" $m1_opts)
    new_exit=$(tail -n1 <<<"$new_out"); new_exit=${new_exit#exit }
    m1_exit=$(tail -n1 <<<"$m1_out"); m1_exit=${m1_exit#exit }
    if [ "$new_exit" = 124 ] || [ "$m1_exit" = 124 ]; then
        echo "SKIP|$label" > "$RESULTS/$tag"; exit 0
    fi
    diff_text=
    [ "$new_exit" = "$m1_exit" ] || diff_text+="  exit code: new $new_exit, M1 $m1_exit"$'\n'
    for name in $STATS; do
        a=$(grep -m1 "^c stat $name " <<<"$new_out" | cut -d' ' -f4)
        b=$(grep -m1 "^c stat $name " <<<"$m1_out" | cut -d' ' -f4)
        if [ -z "$a" ] || [ -z "$b" ]; then
            diff_text+="  $name missing: new '${a}', M1 '${b}'"$'\n'
        elif [ "$a" != "$b" ]; then
            diff_text+="  $name: new $a, M1 $b"$'\n'
        fi
    done
    if [ -z "$diff_text" ]; then
        echo "OK|$label" > "$RESULTS/$tag"
    else
        {
            echo "DIFF|$label"
            echo "instance $file"
            echo "$diff_text"
            echo "  new: $NEW -verb=1 $new_opts $file"
            echo "  M1:  $M1 -verb=1 $m1_opts $file"
        } > "$RESULTS/$tag"
    fi
    exit 0
fi

[ -n "$1" ] || { sed -n '2,/^$/p' "$0" | sed 's/^# \?//'; exit 2; }
NEW=$(realpath "$1"); M1=$(realpath "${2:-/home/ec2-user/miniqu-work/build/bench-M1-r3/miniQU}")
[ -x "$NEW" ] && [ -x "$M1" ] || { echo "m1_equiv.sh: binary not found" >&2; exit 2; }

CORES=0-$(($(nproc) / 2 - 1))
WORK=$(mktemp -d /home/ec2-user/miniqu-work/m1equiv.XXXXXX)
trap 'rm -rf "$WORK"' EXIT
mkdir "$WORK/results" "$WORK/instances"

# Generate the search-tier instances (fixed seeds).
for seed in $(seq 1 "$SEEDS"); do
    echo "$seed"
done | xargs -P "$JOBS" -I{} taskset -c "$CORES" python3 "$HERE/tests/corpus.py" \
    --tier search --seed {} --out "$WORK/instances/search-{}.qcir" >/dev/null || exit 2

MODES=("" "-dl" "-mode=1" "-mode=2")
{
    while read -r name; do
        case $name in ''|'#'*) continue ;; esac
        for mode in "${MODES[@]}"; do
            echo "smoke ${mode:-default}|$mode||$INSTANCES/$name"
        done
    done < "$HERE/bench/smoke.txt"
    for file in "$WORK"/instances/search-*.qcir; do
        for mode in "${MODES[@]}"; do
            echo "search ${mode:-default}|$mode||$file"
            echo "search ${mode:-default} stress|$mode|$STRESS|$file"
        done
    done
} > "$WORK/jobs"

export EQUIV TIMEOUT STATS CORES
tr '\n' '\0' < "$WORK/jobs" |
    xargs -0 -P "$JOBS" -I{} "$0" --job "$NEW" "$M1" "$WORK/results" {}

status=0
cat "$WORK"/results/* | grep -v '^OK|' | grep -v '^SKIP|' | sed 's/^DIFF|.*$/DIFFERENCE:/'
grep -qh '^DIFF|' "$WORK"/results/* && status=1
for set in "smoke default" "smoke -dl" "smoke -mode=1" "smoke -mode=2" \
           "search default" "search -dl" "search -mode=1" "search -mode=2" \
           "search default stress" "search -dl stress" \
           "search -mode=1 stress" "search -mode=2 stress"; do
    ok=$(cat "$WORK"/results/* | grep -c "^OK|$set\$")
    skipped=$(cat "$WORK"/results/* | grep -c "^SKIP|$set\$")
    differing=$(cat "$WORK"/results/* | grep -c "^DIFF|$set\$")
    printf '%-24s compared %3d (identical %3d, different %d), skipped %d\n' \
        "$set" $((ok + differing)) "$ok" "$differing" "$skipped"
    [ $((ok + differing)) -gt 0 ] || { echo "no pair compared for '$set'"; status=1; }
done
[ $status = 0 ] && echo "M1 EQUIVALENCE PASSED" || echo "M1 EQUIVALENCE FAILED"
exit $status
