#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
cd "example_1"
PS4='$ '
set -x
# Use absolute paths because --directory messes with relative paths
python ../../find-bug.py C.v ../example_1_output.v "$@" -l - ../example_1_log.log
