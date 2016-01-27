#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_11"
PS4='$ '
set -x
EXPECTED_ERROR="The reference φ was not found in the current environment."
ACTUAL_PRE="$(echo "y" | python ../../find-bug.py example_11.v bug_11.v 2>&1)"
if [ "$(echo "$ACTUAL_PRE" | grep -c "$EXPECTED_ERROR")" -lt 1 ]
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

python ../../find-bug.py example_11.v bug_11.v || exit $?
