#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_08"
PS4='$ '
set -x
python ../../find-bug.py example_08.v bug_08.v --coqc-is-coqtop "$@" || exit $?
LINES="$(cat bug_08.v | wc -l)"
if [ "$LINES" -ne 11 ]
then
    echo "Expected 11 lines"
    cat bug_08.v
    exit 1
fi
exit 0
