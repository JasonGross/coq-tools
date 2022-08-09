#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
${PYTHON} ../../absolutize-imports.py A.v -R . Example4 "$@" > A_abs.v || exit $?
${PYTHON} ../../absolutize-imports.py B.v -R . Example4 "$@" > B_abs.v || exit $?
