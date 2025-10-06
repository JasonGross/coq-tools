#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}" || exit $?
. "$DIR/init-settings.sh"
EXTRA_ARGS=("--faster-skip-repeat-edit-suffixes" "--no-try-all-inlining-and-minimization-again-at-end" "$@")
PS4='$ '
set -x
find_bug B.v bug_B.v --no-minimize-before-inlining -R . "" "${EXTRA_ARGS[@]}" || exit $?
