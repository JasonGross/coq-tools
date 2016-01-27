#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_4"
PS4='$ '
set -x
python ../../absolutize-imports.py A.v -R . Example4 "$@" > A_abs.v || exit $?
python ../../absolutize-imports.py B.v -R . Example4 "$@" > B_abs.v || exit $?
