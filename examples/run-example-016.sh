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
EXAMPLE_INPUT="example_$N.v"
EXAMPLE_OUTPUT="bug_$N.v"
ARGS=(--nonpassing-coqc-args=-R --nonpassing-coqc-args=Baz --nonpassing-coqc-args=Qux --passing-coqc="${COQBIN}coqc" --passing-coqc-args=-R --passing-coqc-args=Bar --passing-coqc-args=Qux --no-deps "$@")
##########################################################

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/$EXAMPLE_DIRECTORY"

# Initialize common settings like the version of python
. "$DIR/init-settings.sh"

# Set up bash to be verbose about displaying the commands run
PS4='$ '
set -x

######################################################################
# Create the output file (to normalize the number of "yes"es needed),
# and run the script only up to the request for the regular
# expression; then test that the output is as expected.
#
# If you don't need to test the output of the initial requests, feel
# free to remove this section.
#
# Note that the -top argument only appears in Coq >= 8.4
EXPECTED_ERROR=$(cat <<EOF
File "/tmp/tmp[A-Za-z0-9_/]\+\.v", line 1[0-9], characters 6-\(7\|13\):
Error:\(
\| \)The term "X" has type "\(Set ->\|forall _ : Set,\) Set" while it is expected to have type
EOF
)
# pre-build the files to normalize the output for the run we're testing
"${COQBIN}coqc" -nois -R Bar Qux Bar/A.v -q
"${COQBIN}coqc" -nois -R Baz Qux Baz/A.v -q
# account for a super-make called with -B
export MAKEFLAGS="" # B -- VERBOSE=1 V=1
export MFLAGS="" # -B
echo "y" | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${ARGS[@]}" 2>/dev/null >/dev/null
# kludge: create the .glob file so we don't run the makefile
touch "${EXAMPLE_OUTPUT%%.v}.glob"
ACTUAL_PRE="$( (echo "y"; echo "y") | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${ARGS[@]}" 2>&1)"
ACTUAL_PRE_ONE_LINE="$(echo "$ACTUAL_PRE" | tr '\n' '\1')"
TEST_FOR="$(echo "$EXPECTED_ERROR" | tr '\n' '\1')"
if [ "$(echo "$ACTUAL_PRE_ONE_LINE" | grep -c "$TEST_FOR")" -lt 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED_ERROR"
    echo
    echo
    echo
    echo "Actual:"
    echo "$ACTUAL_PRE"
    ${PYTHON} ../prefix-grep.py "$ACTUAL_PRE_ONE_LINE" "$TEST_FOR"
    exit 1
fi
#########################################################################################################


#####################################################################
# Run the bug minimizer on this example; error if it fails to run
# correctly.  Make sure you update the arguments, etc.
find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${ARGS[@]}" || exit $?

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
EXPECTED=$(cat <<EOF
(\* -\*- mode: coq; coq-prog-args: ([^)]*) -\*- \*)
(\* File reduced by coq-bug-minimizer from original input, then from [0-9]\+ lines to [0-9]\+ lines\(, then from [0-9]\+ lines to [0-9]\+ lines\)\? \*)
(\* coqc version [^\*]*\*)

Require Qux\.A\.
Import Qux\.A\.
Check X : Set\.

EOF
)

EXPECTED_ONE_LINE="$(echo "$EXPECTED" | grep -v '^$' | tr '\n' '\1')"
ACTUAL="$(cat "$EXAMPLE_OUTPUT" | grep -v '^$' | tr '\n' '\1')"
LINES="$(echo "$ACTUAL" | grep -c "$EXPECTED_ONE_LINE")"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    echo "Got:"
    cat "$EXAMPLE_OUTPUT" | grep -v '^$'
    ${PYTHON} ../prefix-grep.py "$ACTUAL" "$EXPECTED_ONE_LINE"
    exit 1
fi
exit 0
