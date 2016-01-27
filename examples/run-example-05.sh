#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_05"
PS4='$ '
set -x
python ../../find-bug.py B.v bug_B.v --no-minimize-before-inlining -R . "" "$@" || exit $?
