#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR/example_24"
. "$DIR/init-settings.sh"
ABS_PATH="$(${PYTHON} -c 'import os.path; print(os.path.abspath("."))')"
PS4='$ '
set -x
rm -rf outputs
mkdir -p outputs
cp -a _CoqProject *.v outputs/
cd outputs
rm -f ok
${COQBIN}coq_makefile -f _CoqProject -o Makefile || exit $?
make
(${PYTHON} ../../../minimize-requires.py --all -f _CoqProject 2>&1 && touch ok) | grep -v '^$' | grep -v '^Running command:' | grep -v '^The timeout for ' | sed 's/^\(getting [^ ]*\) (.*)$/\1/g' | tee run.log
rm ok || exit $?
for f in run.log _CoqProject $(ls *.v); do
    diff ../expected/$f $f
    cmp ../expected/$f $f || exit $?
done
