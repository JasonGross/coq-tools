#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
${PYTHON} run-example-08.py || exit $?
