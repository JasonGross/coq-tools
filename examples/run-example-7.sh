#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_7"
PS4='$ '
set -x
python ../../find-bug.py --no-minimize-before-inlining A-dash.v bug_A.v || exit $?
grep Section bug_A.v
ERR=$?
if [ $ERR -ne 0 ]
then
    exit 0
else
    echo "There should be no Section remaining"
    cat bug_A.v
    exit 1
fi
