#!/bin/bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_6"
PS4='$ '
set -x
COQC_84="$(readlink -f ~/.local64/coq/coq-8.4pl4/bin/coqc)"
COQTOP_84="$(readlink -f ~/.local64/coq/coq-trunk/bin/coqtop)"
COQC_TRUNK="$(readlink -f ~/.local64/coq/coq-trunk/bin/coqc)"
COQTOP_TRUNK="$(readlink -f ~/.local64/coq/coq-trunk/bin/coqtop)"
python ../../find-bug.py A.v bug_A.v --coqc "$COQC_84" --coqtop "$COQTOP_84" --passing-coqc "$COQC_TRUNK" "$@"
grep Section bug_A.v
ERR=$?
if [ $ERR -ne 0 ]
then
    exit 0
else
    echo "There should be no Section remaining"
    cat bug_A.v
    exit 1
fi
