#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export FIND_BUG_PY="$(cd "$DIR/.." && pwd)/find-bug.py"
export MINIMIZE_REQUIRES_PY="$(cd "$DIR/.." && pwd)/minimize-requires.py"
export ABSOLUTIZE_IMPORTS_PY="$(cd "$DIR/.." && pwd)/absolutize-imports.py"

if [ -z "${PYTHON}" ]; then
   export PYTHON=python3
fi

if [ -z "${FIND_BUG}" ]; then
    function find_bug() {
        ${PYTHON} "${FIND_BUG_PY}" "$@"
    }
else
    function find_bug() {
        "${FIND_BUG}" "$@"
    }
fi

export -f find_bug

if [ -z "${MINIMIZE_REQUIRES}" ]; then
    function minimize_requires() {
        ${PYTHON} "${MINIMIZE_REQUIRES_PY}" "$@"
    }
else
    function minimize_requires() {
        "${MINIMIZE_REQUIRES}" "$@"
    }
fi

export -f minimize_requires

if [ -z "${ABSOLUTIZE_IMPORTS}" ]; then
    function absolutize_imports() {
        ${PYTHON} "${ABSOLUTIZE_IMPORTS_PY}" "$@"
    }
else
    function absolutize_imports() {
        "${ABSOLUTIZE_IMPORTS}" "$@"
    }
fi

export -f absolutize_imports
