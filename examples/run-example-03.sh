#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_03"
PS4='$ '
set -x
python2 ../../find-bug.py test_bullets.v ../example_03_output.v --no-minimize-before-inlining "$@" -l - ../example_03_log.log || exit $?
