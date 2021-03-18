#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_09"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
rm -f *.vo *.v.d bug*.v *.glob
EXPECTED_ERROR="Error: The command has not failed"
ACTUAL_PRE="$(echo "y" | ${PYTHON} ../../find-bug.py example_09.v bug_09.v 2>&1)"
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
${PYTHON} ../../find-bug.py example_09.v bug_09.v || exit $?
EXPECTED='^(\* File reduced by coq-bug-finder from original input, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines \*)$'
LINES="$(grep -c "$EXPECTED" bug_09.v)"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    cat bug_09.v
    exit 1
fi
exit 0
