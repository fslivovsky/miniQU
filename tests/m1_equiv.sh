#!/bin/bash
# The M1-equivalence gate (doc/rewrite/STATUS.md, H5), and the gate that
# a proof does not change the search (M2-T5).
#
# Usage: tests/m1_equiv.sh NEW_BINARY [M1_BINARY]
#
# With the options in EQUIV below, the current solver has to make exactly
# the search of the accepted M1 solver (default
# /home/ec2-user/miniqu-work/build/bench-M1-r3/miniQU): the same verdict and
# the same counters of the 'c stat' block (conflicts, decisions,
# propagations, ticks, restarts, learned.*, reduced.*, reductions, minimized;
# the M1 binary prints 'c stat minimized' too).  Every task that adds a feature with an off switch appends that switch to EQUIV
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
# NEW is run with 'EQUIV MODE [STRESS]', M1 with 'MODE [STRESS]'.
#
# Second pass, minimisation: the same instances in the modes '' and -dl,
# NEW with 'EQUIV --ccminmode=K MODE [STRESS]', M1 with
# '-ccminmode=K MODE [STRESS]', K = 2, 3 (the later option wins over the
# '--ccminmode=0' of EQUIV).  M1 minimised only without a proof, and none
# is written here.  Not in -mode=1: there the M1 binary loses a secondary
# asserting literal after minimisation and runs on in undefined behaviour
# (internal errors, crashes, wrong verdicts), which M2-T5 fixed by learning
# such a constraint unminimised (doc/rewrite/STATUS.md, M2-T5).
#
# Third pass, proofs: the same instances in the modes '', -dl and -mode=1,
# NEW with default options plus '--ccminmode=K MODE [STRESS]' (K = 0..3),
# once without and once with '-proof=FILE -proof-binary'; writing a proof
# must not change the search.
#
# Every run uses -verb=1, a timeout of 60 s, taskset on the lower half of
# the cores, at most 16 jobs in parallel.  A pair in which either side
# times out is skipped and counted.
#
# Output: every differing pair with both commands, then per set of jobs the
# number of pairs compared and skipped.  Exit status 1 on any difference, on a mode
# with no pair compared, and on a failure to run.

# The M1-equivalent option string; one variable, extended by later tasks.
EQUIV="--no-tiers --no-glueupdate --reducetarget=50 --reducesize --reduceint=0 --no-recomputetier --no-rootsimp --ccminmode=0 --restartmode=0 --no-reusetrail"
STRESS="--reduceint=2 --tier1glue=0 --gcfrac=0"
SEEDS=40
TIMEOUT=60
JOBS=16
INSTANCES=/home/ec2-user/benchmarks/qcir
STATS="conflicts decisions propagations ticks restarts learned.clause learned.cube reduced.clause reduced.cube reductions minimized"

HERE=$(cd "$(dirname "$0")/.." && pwd)

# One pair: job file line "label|pass|options of NEW|other options|instance";
# pass "m1" runs the other side with M1, pass "proof" with NEW and a proof.
if [ "$1" = --job ]; then
    shift
    NEW=$1; M1=$2; RESULTS=$3; JOB=$4
    IFS='|' read -r label pass new_opts m1_opts file <<<"$JOB"
    tag=$(echo "$JOB" | md5sum | cut -c1-16)
    other=$M1
    if [ "$pass" = proof ]; then
        other=$NEW; m1_opts="$m1_opts -proof=$RESULTS/$tag.proof -proof-binary"
    fi
    run () { # binary options...
        local bin=$1; shift
        # shellcheck disable=SC2086
        timeout "$TIMEOUT" taskset -c "$CORES" "$bin" -verb=1 $* "$file" 2>&1
        echo "exit $?"
    }
    new_out=$(run "$NEW" $new_opts); m1_out=$(run "$other" $m1_opts)
    rm -f "$RESULTS/$tag.proof"
    new_exit=$(tail -n1 <<<"$new_out"); new_exit=${new_exit#exit }
    m1_exit=$(tail -n1 <<<"$m1_out"); m1_exit=${m1_exit#exit }
    if [ "$new_exit" = 124 ] || [ "$m1_exit" = 124 ]; then
        echo "SKIP|$label" > "$RESULTS/$tag"; exit 0
    fi
    diff_text=
    [ "$new_exit" = "$m1_exit" ] || diff_text+="  exit code: new $new_exit, other $m1_exit"$'\n'
    for name in $STATS; do
        a=$(grep -m1 "^c stat $name " <<<"$new_out" | cut -d' ' -f4)
        b=$(grep -m1 "^c stat $name " <<<"$m1_out" | cut -d' ' -f4)
        if [ -z "$a" ] || [ -z "$b" ]; then
            diff_text+="  $name missing: new '${a}', other '${b}'"$'\n'
        elif [ "$a" != "$b" ]; then
            diff_text+="  $name: new $a, other $b"$'\n'
        fi
    done
    if [ -z "$diff_text" ]; then
        echo "OK|$label" > "$RESULTS/$tag"
    else
        {
            echo "DIFF|$label"
            echo "instance $file"
            echo "$diff_text"
            echo "  new:   $NEW -verb=1 $new_opts $file"
            echo "  other: $other -verb=1 $m1_opts $file"
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

# Every instance, plain and (generated ones) with STRESS: "set|stress|file".
{
    while read -r name; do
        case $name in ''|'#'*) continue ;; esac
        echo "smoke||$INSTANCES/$name"
    done < "$HERE/bench/smoke.txt"
    for file in "$WORK"/instances/search-*.qcir; do
        echo "search||$file"
        echo "search|stress|$file"
    done
} > "$WORK/instances.txt"

{
    while IFS='|' read -r set stressed file; do
        stress=${stressed:+$STRESS}
        for mode in "" "-dl" "-mode=1" "-mode=2"; do
            name="$set ${mode:-default}${stressed:+ stress}"
            echo "$name|m1|$EQUIV $mode $stress|$mode $stress|$file"
            [ "$mode" = -mode=2 ] && continue
            [ "$mode" = -mode=1 ] || for k in 2 3; do
                echo "ccmin$k $name|m1|$EQUIV --ccminmode=$k $mode $stress|-ccminmode=$k $mode $stress|$file"
            done
            for k in 0 1 2 3; do
                opts="--ccminmode=$k $mode $stress"
                echo "proof ccmin$k $name|proof|$opts|$opts|$file"
            done
        done
    done < "$WORK/instances.txt"
} > "$WORK/jobs"

export TIMEOUT STATS CORES
tr '\n' '\0' < "$WORK/jobs" |
    xargs -0 -P "$JOBS" -I{} "$0" --job "$NEW" "$M1" "$WORK/results" {}

status=0
cat "$WORK"/results/* | grep -v '^OK|' | grep -v '^SKIP|' | sed 's/^DIFF|.*$/DIFFERENCE:/'
grep -qh '^DIFF|' "$WORK"/results/* && status=1
cut -d'|' -f1 "$WORK/jobs" | sort -u > "$WORK/sets"
while read -r set; do
    ok=$(cat "$WORK"/results/* | grep -c "^OK|$set\$")
    skipped=$(cat "$WORK"/results/* | grep -c "^SKIP|$set\$")
    differing=$(cat "$WORK"/results/* | grep -c "^DIFF|$set\$")
    printf '%-34s compared %3d (identical %3d, different %d), skipped %d\n' \
        "$set" $((ok + differing)) "$ok" "$differing" "$skipped"
    [ $((ok + differing)) -gt 0 ] || { echo "no pair compared for '$set'"; status=1; }
done < "$WORK/sets"
[ $status = 0 ] && echo "M1 EQUIVALENCE PASSED" || echo "M1 EQUIVALENCE FAILED"
exit $status
