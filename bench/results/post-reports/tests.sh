#!/bin/bash
# Postponed tests of HANDOFF.md section 2 (items 1, 2, 3, 4, 6, 8, 11), lower half of the cores.
cd ~/miniQU; O=~/miniqu-work/post; B=~/miniqu-work/build
NEW=$B/release/miniQU; ASAN=$B/asan/miniQU
step() { n=$1; shift; echo "=== $n start $(date -u +%H:%M)" >> $O/tests.summary; "$@" > $O/$n.log 2>&1; echo "=== $n rc=$? end $(date -u +%H:%M)" >> $O/tests.summary; }
step ctest bash -c 'for p in release debug asan; do taskset -c 0-23 ctest --preset $p -j 20 2>&1 | tail -3; done'
step m1equiv tests/m1_equiv.sh $NEW $B/bench-M1-r3/miniQU
step matrix-release tests/regress.sh -j 22 -s 1:300 -M all $NEW
step matrix-asan tests/regress.sh -S -j 22 -s 1:100 -t 240 -M all $ASAN
i=0
for OPT in "" "-dl" "--elim --elimint=1" "--vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce" "--elim --elimint=1 --vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce" "--elim --elimint=1 --vivify --vivifyint=1 -dl" "--no-rootsimp"; do
  i=$((i+1)); JOBS=22 KEEP_DIR=$O/cert-keep-$i step cert-$i taskset -c 0-23 tests/fuzz_cert.sh $NEW 1 300 $OPT
done
STRESS="--reduceint=2 --tier1glue=0 --tier2glue=0 --gcfrac=0 --rootsimpdelay=0"
VIV="--vivify --vivifyint=1 --vivifytier=3 --no-vivifyonce"
i=0
for OPT in "" "-dl" "-mode=1" "-mode=2"; do
  i=$((i+1))
  step qdimacs-$i-plain taskset -c 0-23 tests/fuzz_qdimacs.sh $NEW 1 300 $OPT
  step qdimacs-$i-stress taskset -c 0-23 tests/fuzz_qdimacs.sh $NEW 1 300 $OPT $STRESS
  step qdimacs-$i-viv taskset -c 0-23 tests/fuzz_qdimacs.sh $NEW 1 300 $OPT $VIV $STRESS
  step qdimacs-$i-asan taskset -c 0-23 tests/fuzz_qdimacs.sh $ASAN 1 100 $OPT $VIV $STRESS
done
i=0
for A in "--elim" "--elim --elimbound=16" "--elim -no-earlytseitin"; do
  i=$((i+1))
  step complete-$i python3 bench/run.py --solver $NEW --tag post-elim-complete-$i-t60 --timeout 60 --args="$A" --cores 0-23 --jobs 22
done
echo ALLDONE >> $O/tests.summary
