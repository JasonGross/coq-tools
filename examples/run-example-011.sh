#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# check that the regex doesn't split the unicode characters in φ
EXPECTED_ERROR="Error:\\ The\\ reference\\ \\φ\\ was\\ not\\ found\\ in\\ the\\ current\\ environment\\."
ACTUAL_PRE="$((echo "y"; echo "y") | find_bug example_${N}.v bug_${N}.v 2>&1)"
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

find_bug example_${N}.v bug_${N}.v || exit $?
