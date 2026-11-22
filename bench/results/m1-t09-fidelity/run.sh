#!/bin/bash
# Fidelity spot check of M1-T09: conflicts, exit codes and learnt literals of
# the new release binary vs the baseline on search seeds 151..200, for mode 2,
# ccminmode 3 and the default (ccminmode 0, for the learnt-size comparison).
# Columns: seed, new options, conflicts and exit code of both, the baseline's
# 'conflict literals' total and '% deleted', the new learned/learnedlits sums
# and 'minimized'.
D=/home/ec2-user/miniqu-work/fidelity-t08
R=${R:-/home/ec2-user/miniqu-work/t09/miniQU-R3}
B=/home/ec2-user/miniqu-work/baseline/miniQU
one() {
  s=$1; f=$D/s$s.qcir
  for pair in "-mode=2|-mode=2" "-ccminmode=3|-ccmin-mode=3" "-ccminmode=0|-ccmin-mode=0"; do
    opt=${pair%|*}; bopt=${pair#*|}
    rb=$(timeout 60 $B $bopt $f 2>&1); eb=$?
    cb=$(echo "$rb" | awk '/^conflicts /{print $3}')
    lb=$(echo "$rb" | awk '/^conflict literals/{print $4}')
    db=$(echo "$rb" | awk '/^conflict literals/{gsub(/\(/,"",$5); print $5}')
    rr=$(timeout 60 $R $opt -verb=1 $f 2>&1); er=$?
    stat() { echo "$rr" | awk -v n="$1" '$1=="c" && $2=="stat" && $3==n {print $4}'; }
    cr=$(stat conflicts)
    ln=$(( $(stat learned.clause) + $(stat learned.cube) ))
    ll=$(( $(stat learnedlits.clause) + $(stat learnedlits.cube) ))
    echo "$s,$opt,$cb,$cr,$eb,$er,$lb,$db,$ln,$ll,$(stat minimized)"
  done
}
export -f one; export D R B
echo "seed,options,conflicts_baseline,conflicts_new,exit_baseline,exit_new,litstotal_baseline,deleted_pct_baseline,learned_new,learnedlits_new,minimized_new"
seq 151 200 | taskset -c 0-63 xargs -P 16 -I{} bash -c 'one {}' | sort -t, -k1,1n -k2,2
