#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_08"
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
rm -f *.vo *.glob
python2 ../../find-bug.py example_08.v bug_08_3.v --coqc-is-coqtop "$@" || exit $?
LINES="$(cat bug_08_3.v | grep -v '^$' | wc -l)"
if [ "$LINES" -ne 10 ]
then
    echo "Expected 10 lines"
    cat bug_08_3.v
    exit 1
fi
exit 0
