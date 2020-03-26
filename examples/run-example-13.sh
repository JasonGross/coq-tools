#!/bin/bash
###################################################################
## This is a template file for new examples.  It explains how to ##
## check for various things.                                     ##
##                                                               ##
## An example script should exit with code 0 if the test passes, ##
## and with some other code if the test fails.                   ##
###################################################################

##########################################################
# Various options that must be updated for each example
N="13"
EXAMPLE_DIRECTORY="example_$N"
EXAMPLE_INPUT="example_$N.v"
EXAMPLE_OUTPUT="bug_$N.v"
##########################################################

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/$EXAMPLE_DIRECTORY"

# Set up bash to be verbose about displaying the commands run
PS4='$ '
set -x

# Disable parallel make in subcalls to the bug minimizer because it screws with things
. "$DIR/disable-parallel-make.sh"

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
getting example_13\.v
getting example_13\.glob

First, I will attempt to factor out all of the \[Require\]s example_[0-9]\+\.v, and store the result in bug_[0-9]\+\.v\.\.\.

Now, I will attempt to coq the file, and find the error\.\.\.

Coqing the file (bug_13\.v)\.\.\.

Running command: "coqc" "-nois" "-R" "\." "Foo" \("-top" "example_13" \)\?"/tmp/tmp[A-Za-z0-9_]\+\.v" "-q"
The timeout has been set to: 2

This file produces the following output when Coq'ed:
File "/tmp/tmp[A-Za-z0-9_]\+\.v", line 1[0-9], characters 6-9:
Error:
The term "foo" has type "Type" while it is expected to have type\s\?
"Set" (universe inconsistency[^)]*)\.

.\?Does this output display the correct error? \[(y)es/(n)o\]\s
I think the error is 'Error:
The term "foo" has type "Type" while it is expected to have type\s\?
"Set" (universe inconsistency[^)]*)\.
.\?'\.
The corresponding regular expression is 'File "\[^"\]+", line (\[0-9\]+), characters \[0-9-\]+:\\\\n(Error\\\\:\\\\sThe\\\\s+term\\\\s+\\\\"foo\\\\"\\\\s+has\\\\s+type\\\\s+\\\\"Type\\\\"\\\\s+while\\\\s+it\\\\s+is\\\\s+expected\\\\s+to\\\\s+have\\\\s+type\\\\s+\\\\"Set\\\\"\\\\s+\\\\(universe\\\\s+inconsistency[^)]*\\\\)\\\\.*
EOF
)
# pre-build the files to normalize the output for the run we're testing
rm -f *.vo *.glob *.d .*.d
echo "y" | python2 ../../find-bug.py "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" -R . Foo # 2>/dev/null >/dev/null
# kludge: create the .glob file so we don't run the makefile
touch "${EXAMPLE_OUTPUT%%.v}.glob"
ACTUAL_PRE="$((echo "y"; echo "y") | python2 ../../find-bug.py "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" -R . Foo -l - 2>&1)"
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
    python2 ../prefix-grep.py "$ACTUAL_PRE_ONE_LINE" "$TEST_FOR"
    exit 1
fi
#########################################################################################################


#####################################################################
# Run the bug minimizer on this example; error if it fails to run
# correctly.  Make sure you update the arguments, etc.
python2 ../../find-bug.py "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" -R . Foo || exit $?

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
EXPECTED=$(cat <<EOF
(\* -\*- mode: coq; coq-prog-args: ("-emacs" "-nois" "-R" "\." "Foo"\( "-top" "example_[0-9]\+"\)\?) -\*- \*)
(\* File reduced by coq-bug-finder from original input, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines \*)
(\* coqc version [^\*]*\*)

Definition foo : Type := Set\.

Check foo : Set\.

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
    python2 ../prefix-grep.py "$ACTUAL" "$EXPECTED_ONE_LINE"
    exit 1
fi
exit 0
