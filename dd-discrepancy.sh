#!/bin/bash

# the single argument to this script is a QDIMACS file
ARG=$1

python2 ../qcir-conv/qcir-conv.py $ARG > $ARG.qcir

# TO DO: call the buggy solver here
./build/debug/bin/miniQU $ARG.qcir #$ARG
RES1=$?

# TO DO: call some reference solver here which is supposed to work correctly
../qute/qute $ARG
RES2=$?

# the script returns non-zero if the solvers disagree or if either one terminated abnormally
#if [[ ( $RES1 == 20 && $RES2 != 20 ) || ( $RES1 != 10 && $RES1 != 20 ) ]]
if (( $RES1 != $RES2 ))
then 
    exit 1
else
    exit 0  
fi
