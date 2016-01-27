#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/.."
PS4='$ '
set -x
# Use absolute paths because --directory messes with relative paths
# --fast-merge-imports
python ./find-bug.py --no-minimize-before-inlining --directory="$(readlink -f ./examples/example_02)" "$(readlink -f ./examples/example_02/example.v)" "$(readlink -f ./examples/example_02_output.v)" "$@" -l - "$(readlink -f ./examples/example_02_log.log)" || exit $?
