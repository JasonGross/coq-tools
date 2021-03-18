#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_10"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
rm -f *.vo *.glob *.d .*.d */*.vo */*.glob */*.d */.*.d
EXPECTED_ERROR="A.a exists"
ACTUAL_PRE="$(echo "y" | ${PYTHON} ../../find-bug.py example_10.v bug_10.v -Q . Top 2>&1)"
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

${PYTHON} ../../find-bug.py example_10.v bug_10.v -Q . Top || exit $?
EXPECTED='(\* File reduced by coq-bug-finder from original input, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines\(, then from [0-9]\+ lines to [0-9]\+ lines\)\? \*)'
LINES="$(grep -c "$EXPECTED" bug_10.v)"
ACTUAL="$(cat bug_10.v | grep -v '^$' | tr '\n' '\1')"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    echo "Got:"
    cat "$EXAMPLE_OUTPUT" | grep -v '^$'
    ${PYTHON} "$DIR/prefix-grep.py" "$ACTUAL" "$EXPECTED"
    exit 1
fi
exit 0
