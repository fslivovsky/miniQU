#!/bin/bash
# Fake new-interface solver for validating tests/regress.sh: runs the frozen
# baseline, drops or renames the options the baseline does not know, and prints
# "c stat NAME VALUE" lines for every counter named in tests/matrix.txt.
# conflicts, restarts and dependencies are the baseline's real values, every
# other counter is 1 (0 for all counters if STAT_ZERO is set).
BASELINE=${BASELINE:-/home/ec2-user/miniqu-work/baseline/miniQU}
MATRIX=$(dirname "$0")/../matrix.txt

args=()
for arg in "$@"; do
    case $arg in
        --reduceint=*|--tier1glue=*|--gcfrac=*|--depreset=*) ;;       # no equivalent in the baseline
        -ccminmode=*) args+=("-ccmin-mode=${arg#-ccminmode=}") ;;
        -legacyanalyze) args+=(-legacy-analyze) ;;
        -no-earlytseitin) args+=(-no-early-tseitin) ;;
        --no-luby|--rfirst=*|--rinc=*) args+=("${arg#-}") ;;          # the baseline spells these with one dash
        *) args+=("$arg") ;;
    esac
done

out=$("$BASELINE" "${args[@]}" -verb=1 2>&1)
code=$?
echo "$out" | grep -E '^(UN)?SATISFIABLE$'

real() {  # real NAME: the value of a statistics line "NAME : VALUE" of the baseline
    echo "$out" | sed -n "s/^$1 *: *\([0-9]*\).*/\1/p" | head -1
}
for counter in $(sed 's/#.*//' "$MATRIX" | awk -F'|' 'NF == 5 {print $4}' | tr ' ' '\n' | sort -u); do
    case $counter in
        conflicts|restarts|dependencies) value=$(real "$counter") ;;
        *) value=1 ;;
    esac
    echo "c stat $counter $([ -n "$STAT_ZERO" ] && echo 0 || echo "${value:-0}")"
done
exit $code
