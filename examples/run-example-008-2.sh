#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_008" || exit $?
. "$DIR/init-settings.sh"
EXTRA_ARGS=("--faster-skip-repeat-edit-suffixes" "--no-try-all-inlining-and-minimization-again-at-end" "$@")
PS4='$ '
set -x
# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"
rm -f *.vo *.glob *.d .*.d
find_bug example_008.v bug_008_2.v "${EXTRA_ARGS[@]}" || exit $?
LINES="$(cat bug_008_2.v | "$GREP" -v '^$' | wc -l)"
if [ "$LINES" -ne 9 ]
then
    echo "Expected 9 lines"
    cat bug_008_2.v
    exit 1
fi
exit 0
