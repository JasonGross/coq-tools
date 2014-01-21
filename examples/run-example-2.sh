#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/.."
PS4='$ '
set -x
# Use absolute paths because --directory messes with relative paths
# --fast-merge-imports
python ./find-bug.py --strip-newlines 2 --directory="$(readlink -f ./examples/example_2)" "$(readlink -f ./examples/example_2/example.v)" "$(readlink -f ./examples/example_2_output.v)" "$@" -l - "$(readlink -f ./examples/example_2_log.log)"
