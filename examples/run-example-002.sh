#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}" || exit $?
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# --fast-merge-imports
find_bug --no-minimize-before-inlining example.v example_${N}_output.v "$@" -l - example_${N}_log.log || exit $?
