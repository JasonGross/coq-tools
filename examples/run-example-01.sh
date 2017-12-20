#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
cd "example_01"
PS4='$ '
set -x
python2 ../../find-bug.py C.v ../example_01_output.v --no-minimize-before-inlining "$@" -l - ../example_01_log.log || exit $?
