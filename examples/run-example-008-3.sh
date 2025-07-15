#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_008" || exit $?
. "$DIR/init-settings.sh"
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
rm -f *.vo *.glob *.d .*.d
find_bug example_008.v bug_008_3.v --coqc-is-coqtop "$@" || exit $?
LINES="$(cat bug_008_3.v | "$GREP" -v '^$' | wc -l)"
if [ "$LINES" -ne 9 ]
then
    echo "Expected 9 lines"
    cat bug_008_3.v
    exit 1
fi
exit 0
