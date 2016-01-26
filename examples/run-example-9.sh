#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_9"
PS4='$ '
set -x
python ../../find-bug.py example_9.v bug_9.v || exit $?
EXPECTED='^(\* File reduced by coq-bug-finder from original input, then from [0-9]+ lines to [0-9]+ lines, then from [0-9]+ lines to [0-9]+ lines \*)$'
LINES="$(grep -c "$EXPECTED" bug_9.v)"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    cat bug_9.v
    exit 1
fi
exit 0
