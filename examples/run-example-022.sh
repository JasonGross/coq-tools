#!/usr/bin/env bash

# test that some mostly untested files at least run

# Get the directory name of this script, and `cd` to that directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
mkdir -p "$DIR/example_22"
cd "$DIR/example_22"

# Initialize common settings like the version of python
. "$DIR/init-settings.sh"

# Set up bash to be verbose about displaying the commands run
PS4='$ '
set -x

minimize_requires -h || exit $?
touch ex22.v
minimize_requires --arg=-nois ex22.v || exit $?
rm -f ex22.v
exit 0
