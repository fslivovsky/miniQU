#!/bin/bash
# Checks a QLRUP proof with the Lean kernel in the loop: the result is a Lean theorem about the
# formula, obtained by running the verified checker on the proof as it is read (see
# QlrupChecker/Command.lean).
#
# Usage: qlrup-theorem.sh [--keep] FORMULA.qcir PROOF [true|false]
#
# The last argument is the result the proof is supposed to establish. If it is missing, it is
# determined by checking the proof once with the stand-alone checker (qlrup-check).
#
# Prints "s VERIFIED TRUE" or "s VERIFIED FALSE" followed by the axioms the theorem depends on,
# or "s NOT VERIFIED". Exit code 0 if verified, 1 if not, 2 on usage or build errors.
# With --keep, the generated Lean file is kept and its path printed.

set -u
DIR=$(cd "$(dirname "$0")" && pwd)
KEEP=0
if [ "${1:-}" = "--keep" ]; then KEEP=1; shift; fi
if [ $# -lt 2 ] || [ $# -gt 3 ]; then
    echo "usage: $0 [--keep] FORMULA.qcir PROOF [true|false]" >&2
    exit 2
fi
FORMULA=$(realpath "$1") || exit 2
PROOF=$(realpath "$2") || exit 2
EXPECT=${3:-}

cd "$DIR" || exit 2
lake build QlrupChecker qlrup-check > /dev/null 2>&1 || { echo "error: lake build failed" >&2; exit 2; }

if [ -z "$EXPECT" ]; then
    case "$(.lake/build/bin/qlrup-check "$FORMULA" "$PROOF")" in
        "s VERIFIED TRUE")  EXPECT=true ;;
        "s VERIFIED FALSE") EXPECT=false ;;
        *) echo "s NOT VERIFIED"; exit 1 ;;
    esac
fi
case "$EXPECT" in
    true|false) ;;
    *) echo "error: expected result must be 'true' or 'false'" >&2; exit 2 ;;
esac

TMP=$(mktemp -d)
[ $KEEP = 1 ] || trap 'rm -rf "$TMP"' EXIT
# The paths are written as Lean string literals.
esc() { printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'; }
cat > "$TMP/Check.lean" <<LEAN
import QlrupChecker.Command
qlrup_$EXPECT result "$(esc "$FORMULA")" "$(esc "$PROOF")"
#print axioms result
LEAN

OUT=$(lake lean "$TMP/Check.lean" 2>&1)
STATUS=$?
[ $KEEP = 1 ] && echo "c Lean file: $TMP/Check.lean"
AXIOMS=$(printf '%s\n' "$OUT" | grep "^'result' depends on axioms")
if [ $STATUS -eq 0 ] && [ -n "$AXIOMS" ] && ! printf '%s' "$AXIOMS" | grep -q sorryAx; then
    if [ "$EXPECT" = true ]; then echo "s VERIFIED TRUE"; else echo "s VERIFIED FALSE"; fi
    echo "c $AXIOMS"
    exit 0
fi
echo "s NOT VERIFIED"
printf '%s\n' "$OUT" | grep -v "^✔\|^ℹ\|^⚠\|^info: " | head -5 | sed 's/^/c /' | cut -c1-300
exit 1
