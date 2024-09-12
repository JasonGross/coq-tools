#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR" || exit $?
cd "example_${N}" || exit $?
. "$DIR/init-settings.sh"
PS4='$ '
set -x
find_bug C.v ../example_${N}_output.v --no-minimize-before-inlining "$@" -l - ../example_${N}_log.log || exit $?
