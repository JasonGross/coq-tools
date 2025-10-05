#!/usr/bin/env bash
###################################################################
## Test for Ltac2 support with non-existent binding             ##
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
EXTRA_ARGS=("--faster-skip-repeat-edit-suffixes" "--no-try-all-inlining-and-minimization-again-at-end" "--inline-user-contrib" "-Q" "/tmp/doesnotexist/Ltac2" "Ltac2" "$@")
##########################################################

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/$EXAMPLE_DIRECTORY" || exit $?
rm -rf /tmp/doesnotexist/Ltac2

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
File "[^"]*\.v", line [0-9]\+, characters [0-9]\+-[0-9]\+:
Error: The command has not failed
EOF

# pre-build the files to normalize the output for the run we're testing
find "$DIR/$EXAMPLE_DIRECTORY" \( -name "*.vo" -o -name "*.glob" \) -delete

echo "y" | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" 2>/dev/null >/dev/null
# kludge: create the .glob file so we don't run the makefile
touch "${EXAMPLE_OUTPUT%%.v}.glob"
ACTUAL_PRE="$( (echo "y"; echo "y") | find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" -l - 2>&1)"
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


#####################################################################
# Run the bug minimizer on this example; error if it fails to run
# correctly.  Make sure you update the arguments, etc.
find_bug "$EXAMPLE_INPUT" "$EXAMPLE_OUTPUT" "${EXTRA_ARGS[@]}" || exit $?

######################################################################
# Put some segment that you expect to see in the file here.  Or count
# the number of lines.  Or make some other test.  Or remove this block
# entirely if you don't care about the minimized file.
# Note that for this test, we only need to make sure that Ltac2.Init is the only module required, and Ltac2.List / Ltac2.Ltac2 is not.  We use some wildcards to account for changes in the stdlib.
{ EXPECTED=$(cat); } <<EOF
(\* -\*- mode: coq; coq-prog-args: ("-emacs"\( "-w" "-deprecated-native-compiler-option,-native-compiler-disabled"\)\?\( "-native-compiler" "ondemand"\)\? "-Q" "/tmp/doesnotexist/Ltac2" "Ltac2" .*\( "-top" "Top\.example_[0-9]\+"\)\?) -\*- \*)
(\* File reduced by coq-bug-minimizer from original input\(, then from [0-9]\+ lines to [0-9]\+ lines\)\+ \*)
(\* coqc version [^\*]*\*)
Require Ltac2\.Init\.
Module Export List\.

Import Ltac2\.Init\.

Ltac2 rec map (f : 'a -> 'b) (ls : 'a list)[^=]*:=
  match ls with
  | \[\] => \[\]
  | l :: ls => f l :: map f ls
  end.
Fail Ltac2 Eval List\.map (fun x => x) \[1; 2\]\.
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
