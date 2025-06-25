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
EXAMPLE_DIRECTORY="example_${N}"
EXAMPLE_INPUT="example_${N}.v"
EXAMPLE_OUTPUT="bug_${N}.v"
##########################################################

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/$EXAMPLE_DIRECTORY" || exit $?

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
{ EXPECTED_ERROR=$(cat); } <<EOF
File "[^"]*\+\.v", line [0-9]\+, characters 6-10:
Error: Illegal application (Non-functional construction):\s
The expression "Set" of type "Type"
cannot be applied to the term
 "Set" : "Type"

\?.\?Does this output display the correct error? \[(y)es/(n)o\]\s
I think the error is 'Error: Illegal application (Non-functional construction):\s
The expression "Set" of type "Type"
cannot be applied to the term
 "Set" : "Type"
.\?'\.
The corresponding regular expression is 'File "\[^"\]+", line (\[0-9\]+), characters \[0-9-\]+:\\\\n(Error:\\\\s+Illegal\\\\s+application\\\\s+\\\\(Non\\\\-functional\\\\s+construction\\\\):\\\\s+The\\\\s+expression\\\\s+"Set"\\\\s+of\\\\s+type\\\\s+"Type"\\\\scannot\\\\s+be\\\\s+applied\\\\s+to\\\\s+the\\\\s+term\\\\s+"Set"\\\\s+:\\\\s+"Type")'\.

\?Is this correct? \[(y)es/(n)o\] Traceback (most recent call last):
EOF
# pre-build the files to normalize the output for the run we're testing
# ??? sometimes this doesn't create the output file, cf https://gitlab.com/coq/coq/-/jobs/591578724 ????
# so for now, we emit the output
echo "DEBUG: INITIAL RUN OUTPUT"
echo "y" | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" # 2>/dev/null >/dev/null
echo "DEBUG: END INITIAL RUN OUTPUT"
# kludge: create the .glob file so we don't run the makefile
touch "${EXAMPLE_OUTPUT%%.v}.glob"
ACTUAL_PRE="$( (echo "y"; echo "y") | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" 2>&1)"
echo "==================== ACTUAL ===================="
echo "${ACTUAL_PRE}"
echo "==================== ACTUAL ===================="
echo "==================== EXPECTED_ERROR ===================="
echo "${EXPECTED_ERROR}"
echo "==================== EXPECTED_ERROR ===================="
ACTUAL_PRE_ONE_LINE="$(echo "$ACTUAL_PRE" | tr '\n' '\1' | tr -d '\r')"
TEST_FOR="$(echo "$EXPECTED_ERROR" | tr '\n' '\1' | tr -d '\r')"
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
find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" || exit $?

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
{ EXPECTED=$(cat); } <<EOF
(\* -\*- mode: coq; coq-prog-args: ([^)]*) -\*- \*)
(\* File reduced by coq-bug-minimizer from original input\(, then from [0-9]\+ lines to [0-9]\+ lines\)\+ \*)
(\* coqc version [^\*]*\*)
Notation "(+ \*) " := (Set Set)\.
Check (+\*)\.
EOF

EXPECTED_ONE_LINE="$(strip_for_grep "$EXPECTED")"
ACTUAL="$(strip_for_grep "$(cat "$EXAMPLE_OUTPUT")")"
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
