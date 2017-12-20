#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_04"
PS4='$ '
set -x
python2 ../../absolutize-imports.py A.v -R . Example4 "$@" > A_abs.v || exit $?
python2 ../../absolutize-imports.py B.v -R . Example4 "$@" > B_abs.v || exit $?
