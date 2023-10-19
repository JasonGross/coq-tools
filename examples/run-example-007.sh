#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
find_bug --no-minimize-before-inlining A-dash.v bug_A.v || exit $?
grep Section bug_A.v
ERR=$?
if [ $ERR -ne 0 ]
then
    exit 0
else
    echo "There should be no Section remaining"
    cat bug_A.v
    exit 1
fi
