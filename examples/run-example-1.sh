#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/.."
PS4='$ '
set -x
# Use absolute paths because --directory messes with relative paths
python ./find-bug.py --directory="$(readlink -f ./examples/example_1)" "$(readlink -f ./examples/example_1/C.v)" "$(readlink -f ./examples/example_1_output.v)" "$@" -l - "$(readlink -f ./examples/example_1_log.log)"
