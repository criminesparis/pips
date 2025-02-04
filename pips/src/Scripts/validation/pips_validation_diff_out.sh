#!/bin/bash
#
# $Id: pips_validation_diff_out.sh 19685 2011-06-06 11:56:21Z coelho $
#
# show diffs between test and out files
# usage: $0 path/to/test

test=$1
out=${test%/test}/out
test -f $test || { echo "[$0] missing file: $test"; exit 11; }
test -f $out  || { echo "[$0] missing file: $out"; exit 12; }
diff $test $out
exit $?
