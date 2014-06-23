#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_3"
PS4='$ '
set -x
python ../../find-bug.py test_bullets.v ../example_3_output.v "$@" -l - ../example_3_log.log

