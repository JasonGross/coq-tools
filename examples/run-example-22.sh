#!/bin/bash

# test that some mostly untested files at least run

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/"
FIND_BUG_PY="$(cd "$DIR/.." && pwd)/find-bug.py"
MINIMIZE_REQUIRES_PY="$(cd "$DIR/.." && pwd)/minimize-requires.py"

# Set up bash to be verbose about displaying the commands run
PS4='$ '
set -x

python2 ${MINIMIZE_REQUIRES_PY} -h || exit $?
exit 0
