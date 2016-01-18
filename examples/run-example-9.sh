#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_9"
PS4='$ '
set -x
#python ../../find-bug.py example_9.v bug_9.v --minimize-before-inlining || exit $?
EXPECTED='^(\* File reduced by coq-bug-finder from original input, then from 30 lines to 7 lines, then from 43 lines to 6 lines, then from 40 lines to 6 lines, then from 36 lines to 10 lines, then from 24 lines to 10 lines \*)$'
LINES="$(grep -c "$EXPECTED" bug_9.v)"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    cat bug_9.v
    exit 1
fi
exit 0
