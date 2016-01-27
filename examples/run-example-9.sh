#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_9"
PS4='$ '
set -x
EXPECTED_ERROR="Error: The command has not failed!"
ACTUAL_PRE="$(echo "y" | python ../../find-bug.py example_9.v bug_9.v 2>&1)"
if [ "$(echo "$ACTUAL_PRE" | grep -c "$EXPECTED_ERROR")" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED_ERROR"
    echo
    echo
    echo
    echo "Actual:"
    echo "$ACTUAL_PRE"
    exit 1
fi
python ../../find-bug.py example_9.v bug_9.v || exit $?
EXPECTED='^(\* File reduced by coq-bug-finder from original input, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines \*)$'
LINES="$(grep -c "$EXPECTED" bug_9.v)"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    cat bug_9.v
    exit 1
fi
exit 0
