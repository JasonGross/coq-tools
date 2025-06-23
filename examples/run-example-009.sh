#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}" || exit $?
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
rm -f *.vo *.v.d bug*.v *.glob
EXPECTED_ERROR="Error: The command has not failed"
ACTUAL_PRE="$(echo "y" | find_bug example_${N}.v bug_${N}.v 2>&1)"
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
EXPECTED='^(\* File reduced by coq-bug-minimizer from original input\(, then from [0-9]\+ lines to [0-9]\+ lines\)\+ \*)$'
LINES="$(grep -c "$EXPECTED" bug_${N}.v)"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    cat bug_${N}.v
    exit 1
fi
exit 0
