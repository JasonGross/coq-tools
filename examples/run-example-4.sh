#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_4"
PS4='$ '
set -x
python ../../absolutize-imports.py A.v --topname Example4 "$@" > A_abs.v
python ../../absolutize-imports.py B.v --topname Example4 "$@" > B_abs.v
