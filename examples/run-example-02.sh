#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_02"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# --fast-merge-imports
${PYTHON} ../../find-bug.py --no-minimize-before-inlining example.v example_02_output.v "$@" -l - example_02_log.log || exit $?
