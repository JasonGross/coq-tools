#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_11"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# check that the regex doesn't split the unicode characters in φ
EXPECTED_ERROR="Error\\:\\ The\\ reference\\ \\φ\\ was\\ not\\ found\\ in\\ the\\ current\\ environment\\."
ACTUAL_PRE="$((echo "y"; echo "y") | ${PYTHON} ../../find-bug.py example_11.v bug_11.v 2>&1)"
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

${PYTHON} ../../find-bug.py example_11.v bug_11.v || exit $?
