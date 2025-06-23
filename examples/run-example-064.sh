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
EXTRA_ARGS=("$@")
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

# pre-build the files to normalize the output for the run we're testing
find "$DIR/$EXAMPLE_DIRECTORY" \( -name "*.vo" -o -name "*.glob" \) -delete
inline_imports "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" || exit $?


# kludge: create the .glob file so we don't run the makefile
# touch "${EXAMPLE_OUTPUT%%.v}.glob"

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
{ EXPECTED=$(cat); } <<EOF
Module Top_DOT_A\.
Module Top\.
Module A\.
Axiom A : Set\.
End A\.

End Top\.

End Top_DOT_A\.

Module Top_DOT_B\.
Module Top\.
Module B\.
Import Top_DOT_A\.
Import Top_DOT_A\.Top\.
Axiom B : Set\.
End B\.

End Top\.

End Top_DOT_B\.

Module Top_DOT_example_064\.
Module Top\.
Module example_064\.
Import Top_DOT_A\.
Import Top_DOT_B\.
Import Top_DOT_B\.Top\.
Import Top_DOT_A\.Top\.
Axiom C : Set\.
End example_064\.

End Top\.

End Top_DOT_example_064\.
EOF

EXPECTED_ONE_LINE="$(echo "$EXPECTED" | grep -v '^$' | tr '\n' '\1')"
ACTUAL="$(cat "$EXAMPLE_OUTPUT" | grep -v '^$' | tr '\n' '\1')"
LINES="$(echo "$ACTUAL" | grep -c "$EXPECTED_ONE_LINE")"
if [ "$LINES" -ne 1 ]
then
    echo "Expected a string matching:"
    echo "$EXPECTED"
    echo "Got:"
    cat "$EXAMPLE_OUTPUT" | grep -v '^$'
    PREFIX_GREP="$(relpath "$DIR/prefix-grep.py" "$PWD")"
    ${PYTHON} "$PREFIX_GREP" "$ACTUAL" "$EXPECTED_ONE_LINE"
    exit 1
fi
exit 0
