#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
cd "example_01"
PS4='$ '
set -x
# Use absolute paths because --directory messes with relative paths
python ../../find-bug.py C.v ../example_01_output.v --no-minimize-before-inlining "$@" -l - ../example_01_log.log || exit $?
