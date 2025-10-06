#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}" || exit $?
. "$DIR/init-settings.sh"
EXTRA_ARGS=("--faster-skip-repeat-edit-suffixes" "--no-try-all-inlining-and-minimization-again-at-end" "--no-minimize-before-inlining" "$@")
PS4='$ '
set -x
# --fast-merge-imports
find_bug example.v example_${N}_output.v "${EXTRA_ARGS[@]}" -l - example_${N}_log.log || exit $?
