#!/bin/bash

# test that some mostly untested files at least run

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/"
FIND_BUG_PY="$(cd "$DIR/.." && pwd)/find-bug.py"
MINIMIZE_REQUIRES_PY="$(cd "$DIR/.." && pwd)/minimize-requires.py"

# Initialize common settings like the version of python
. "$DIR/init-settings.sh"

# Set up bash to be verbose about displaying the commands run
PS4='$ '
set -x

${PYTHON} ${MINIMIZE_REQUIRES_PY} -h || exit $?
touch ex22.v
${PYTHON} ${MINIMIZE_REQUIRES_PY} --arg=-nois ex22.v || exit $?
rm -f ex22.v
exit 0
