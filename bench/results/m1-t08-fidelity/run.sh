#!/bin/bash
# Fidelity spot check: conflicts and exit codes of R vs baseline, search seeds 151..200.
D=/home/ec2-user/miniqu-work/fidelity-t08
R=/home/ec2-user/miniqu-work/build/release/miniQU
B=/home/ec2-user/miniqu-work/baseline/miniQU
one() {
  s=$1; f=$D/s$s.qcir
  for opt in -dl -mode=1; do
    rb=$(timeout 60 $B $opt $f 2>&1); eb=$?; cb=$(echo "$rb" | awk '/^conflicts /{print $3}')
    rr=$(timeout 60 $R $opt -verb=1 $f 2>&1); er=$?; cr=$(echo "$rr" | awk '/^c stat conflicts /{print $4}')
    echo "$s,$opt,$cb,$cr,$eb,$er"
  done
}
export -f one; export D R B
seq 151 200 | taskset -c 0-63 xargs -P 16 -I{} bash -c 'one {}' | sort -n > $D/out2.csv
