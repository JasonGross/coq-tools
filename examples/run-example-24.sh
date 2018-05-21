#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
cd "example_24"
PS4='$ '
set -x
rm -rf outputs
mkdir -p outputs
cp -a _CoqProject *.v outputs/
cd outputs
rm -f ok
${COQBIN}coq_makefile -f _CoqProject -o Makefile || exit $?
make
(python2 ../../../minimize-requires.py --all -f _CoqProject 2>&1 && touch ok) | tee run.log
rm ok || exit $?
for f in run.log _CoqProject $(ls *.v); do
    cmp ../expected/$f $f || exit $?
done
