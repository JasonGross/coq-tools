#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR"
cd "example_${N}"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
${PYTHON} ../../find-bug.py C.v ../example_${N}_output.v --no-minimize-before-inlining "$@" -l - ../example_${N}_log.log || exit $?
