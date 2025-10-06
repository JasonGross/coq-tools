#!/usr/bin/env bash
###################################################################
## This is a template file for new examples.  It explains how to ##
## check for various things.                                     ##
##                                                               ##
## An example script should exit with code 0 if the test passes, ##
## and with some other code if the test fails.                   ##
###################################################################

##########################################################
# Various options that must be updated for each example
N="${0##*-}"; N="${N%.sh}"
EXAMPLE_DIRECTORY="example_$N"
EXAMPLE_INPUT="A/example_$N.v"
EXAMPLE_OUTPUT="B/bug_$N.v"
EXTRA_ARGS=("--faster-skip-repeat-edit-suffixes" --nonpassing-R Foo1 Foo --passing-R Foo2 Foo -R A Top --passing-coqc=coqc --no-deps "$@")
##########################################################

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/$EXAMPLE_DIRECTORY" || exit $?

# Initialize common settings like the version of python
. "$DIR/init-settings.sh"

# Set up bash to be verbose about displaying the commands run
PS4='$ '
set -x

# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"

#####################################################################
# Run the bug minimizer on this example; error if it fails to run
# correctly.  Make sure you update the arguments, etc.
for dir in Foo1 Foo2; do
    pushd $dir >/dev/null
    for f in A.v B.v; do
        ${COQBIN}coqc -q -R . Foo $f || exit $?
    done
    popd >/dev/null
done

mkdir -p "$(dirname "${EXAMPLE_OUTPUT}")"
find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" || exit $?

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
{ EXPECTED=$(cat); } <<EOF
(\* -\*- mode: coq; coq-prog-args: ([^)]*) -\*- \*)
(\* File reduced by coq-bug-minimizer from original input\(, then from [0-9]\+ lines to [0-9]\+ lines\)\+ \*)
(\* coqc version [^\*]*\*)
Require Foo\.A\.

Export Foo\.A\.
Fail Check x\.

EOF

EXPECTED_ONE_LINE="$(strip_for_grep "$EXPECTED")"
ACTUAL="$(strip_for_grep "$(cat "$EXAMPLE_OUTPUT")")"
if ! grep_contains "$ACTUAL" "$EXPECTED_ONE_LINE"
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    echo "Got:"
    cat "$EXAMPLE_OUTPUT" | "$GREP" -v '^$'
    PREFIX_GREP="$(relpath "$DIR/prefix-grep.py" "$PWD")"
    ${PYTHON} "$PREFIX_GREP" "$ACTUAL" "$EXPECTED_ONE_LINE"
    exit 1
fi
exit 0
