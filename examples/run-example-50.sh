#!/bin/bash
###################################################################
## Testing split definition pass                                 ##
###################################################################

##########################################################
# Various options that must be updated for each example
N="50"
EXAMPLE_DIRECTORY="example_$N"
EXAMPLE_INPUT="example_$N.v"
EXAMPLE_OUTPUT="bug_$N.v"
EXTRA_ARGS=("$@")
##########################################################

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/$EXAMPLE_DIRECTORY"
FIND_BUG_PY="$(cd "$DIR/.." && pwd)/find-bug.py"

# Initialize common settings like the version of python
. "$DIR/init-settings.sh"

ABS_PATH="$(${PYTHON} -c 'import os.path; print(os.path.abspath("."))')"

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
#
# Note also that the line numbers tend to be one larger in old
# versions of Coq (<= 8.6?)
EXPECTED_ERROR=$(cat <<EOF
This file produces the following output when Coq'ed:
foo
     : nat
File "/tmp/tmp[A-Za-z0-9_/]\+\.v", line 1\(0\|1\), characters 0-15:
Error: The command has not failed\s\?!
EOF
)
# pre-build the files to normalize the output for the run we're testing
find "$DIR/example_$N" \( -name "*.vo" -o -name "*.glob" \) -delete
echo "y" | ${PYTHON} "$FIND_BUG_PY" "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" 2>/dev/null >/dev/null
# kludge: create the .glob file so we don't run the makefile
touch "${EXAMPLE_OUTPUT%%.v}.glob"
ACTUAL_PRE="$((echo "y"; echo "y") | ${PYTHON} "$FIND_BUG_PY" "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" -l - 2>&1)"
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
    ${PYTHON} "$DIR/prefix-grep.py" "$ACTUAL_PRE_ONE_LINE" "$TEST_FOR"
    exit 1
fi
#########################################################################################################


#####################################################################
# Run the bug minimizer on this example; error if it fails to run
# correctly.  Make sure you update the arguments, etc.
${PYTHON} "$FIND_BUG_PY" "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" || exit $?

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
EXPECTED=$(cat <<EOF
(\* -\*- mode: coq; coq-prog-args: ("-emacs"\( "-w" "-deprecated-native-compiler-option,-native-compiler-disabled"\)\? "-R" "\." "Top"\( "-top" "example_[0-9]\+"\)\?\( "-native-compiler" "ondemand"\)\?) -\*- \*)
(\* File reduced by coq-bug-minimizer from original input, then from [0-9]\+ lines to [0-9]\+ lines, then from [0-9]\+ lines to [0-9]\+ lines \*)
(\* coqc version [^\*]*\*)

Definition foo : nat\.
Admitted\.
Fail Check foo\.

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
    ${PYTHON} "$DIR/prefix-grep.py" "$ACTUAL" "$EXPECTED_ONE_LINE"
    exit 1
fi
exit 0
