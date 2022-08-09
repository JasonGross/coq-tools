#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
N="${0##*-}"; N="${N%.sh}"
cd "$DIR/example_${N}"
. "$DIR/init-settings.sh"
PS4='$ '
set -x
if [ -z "$COQC_84" ]; then COQC_84="$(readlink -f ~/.local64/coq/coq-8.4pl4/bin/coqc)"; fi
if [ -z "$COQTOP_84" ]; then COQTOP_84="$(readlink -f ~/.local64/coq/coq-trunk/bin/coqtop)"; fi
if [ -z "$COQC_TRUNK" ]; then COQC_TRUNK="$(readlink -f ~/.local64/coq/coq-trunk/bin/coqc)"; fi
if [ -z "$COQTOP_TRUNK" ]; then COQTOP_TRUNK="$(readlink -f ~/.local64/coq/coq-trunk/bin/coqtop)"; fi
${PYTHON} ../../find-bug.py A.v bug_A.v --no-minimize-before-inlining --coqc "$COQC_84" --coqtop "$COQTOP_84" --passing-coqc "$COQC_TRUNK" "$@" || exit $?
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
