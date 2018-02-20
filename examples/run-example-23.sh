#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
cd "example_23"
PS4='$ '
set -x
python2 ../../find-bug.py -f _CoqProject A.v bug.v || exit $?
