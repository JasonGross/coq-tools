#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/.."
PS4='$ '
set -x
# --fast-merge-imports
python ./find-bug.py --no-minimize-before-inlining "$(readlink -f ./examples/example_02/example.v)" "$(readlink -f ./examples/example_02_output.v)" "$@" -l - "$(readlink -f ./examples/example_02_log.log)" || exit $?
