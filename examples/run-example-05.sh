#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_05"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
${PYTHON} ../../find-bug.py B.v bug_B.v --no-minimize-before-inlining -R . "" "$@" || exit $?
