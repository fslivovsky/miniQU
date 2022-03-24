#!/bin/bash

# the single argument to this script is a QDIMACS file
ARG=$1

# TO DO: call the buggy solver here
./build/debug/bin/miniQU -dl $ARG 2> $ARG.qlin
RES1=$?

# TO DO: call some reference solver here which is supposed to work correctly
depqbf $ARG
RES2=$?

# the script returns non-zero if the solvers disagree or if either one terminated abnormally
if [[ $RES1 != $RES2 ]]
then
    exit 1
else
    ./tracing/QLIN2QRP.py $ARG.qlin $ARG.qrp
    if [[ $RES1 -eq 10 ]]
    then
	qrpcheck $ARG.qrp -f $ARG
	exit $?
    else
	qrpcheck $ARG.qrp
	exit $?
    fi
fi
