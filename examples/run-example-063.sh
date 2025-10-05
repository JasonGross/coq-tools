#!/usr/bin/env bash
###################################################################
## Test for -top computed correctly for passing coqc             ##
###################################################################

##########################################################
# Various options that must be updated for each example
N="${0##*-}"; N="${N%.sh}"
EXAMPLE_DIRECTORY="example_$N"
EXAMPLE_INPUT="example_$N.v"
EXAMPLE_OUTPUT="bug_$N.v"
EXTRA_ARGS=("--faster-skip-repeat-edit-suffixes" "--no-try-all-inlining-and-minimization-again-at-end" "--passing-coqc" "coqc" "--passing-R" "/tmp" "YESPASSING" "--nonpassing-R" "/tmp" "NONPASSING" "--nonpassing-R" "." "Foo" "$@")
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
{ EXPECTED_ERROR=$(cat); } <<EOF
Running command.*: "coqc" .*"-R" "/tmp" "NONPASSING" "-R" "." "Foo" "-top" "Foo.example_063" .*
.*
Running command.*: "coqc" .*"-R" "/tmp" "YESPASSING" "-top" "Foo.example_063" .*
EOF

# pre-build the files to normalize the output for the run we're testing
find "$DIR/$EXAMPLE_DIRECTORY" \( -name "*.vo" -o -name "*.glob" \) -delete
echo "y" | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" 2>/dev/null >/dev/null
# kludge: create the .glob file so we don't run the makefile
touch "${EXAMPLE_OUTPUT%%.v}.glob"
ACTUAL_PRE="$( (echo "y"; echo "y"; echo "y") | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" -l - 2>&1)"
ACTUAL_PRE_ONE_LINE="$(strip_for_grep "$ACTUAL_PRE")"
TEST_FOR="$(strip_for_grep "$EXPECTED_ERROR")"
if ! grep_contains "$ACTUAL_PRE_ONE_LINE" "$TEST_FOR"
then
    echo "Expected a string matching:"
    echo "$EXPECTED_ERROR"
    echo
    echo
    echo
    echo "Actual:"
    echo "$ACTUAL_PRE"
    PREFIX_GREP="$(relpath "$DIR/prefix-grep.py" "$PWD")"
    ${PYTHON} "$PREFIX_GREP" "$ACTUAL_PRE_ONE_LINE" "$TEST_FOR"
    exit 1
fi
#########################################################################################################