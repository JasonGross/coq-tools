#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
FIND_BUG_PY="$(cd "$DIR/.." && pwd)/find-bug.py"
export FIND_BUG_PY
MINIMIZE_REQUIRES_PY="$(cd "$DIR/.." && pwd)/minimize-requires.py"
export MINIMIZE_REQUIRES_PY
ABSOLUTIZE_IMPORTS_PY="$(cd "$DIR/.." && pwd)/absolutize-imports.py"
export ABSOLUTIZE_IMPORTS_PY
INLINE_IMPORTS_PY="$(cd "$DIR/.." && pwd)/inline-imports.py"
export INLINE_IMPORTS_PY

if [ -z "${PYTHON}" ]; then
    PYTHON=python3
    export PYTHON
fi

if [ -z "${FIND_BUG}" ]; then
    function find_bug() {
        ${PYTHON} "${FIND_BUG_PY}" "$@"
    }
else
    FIND_BUG="$(cd "$DIR" && realpath "$(which "${FIND_BUG}")")"
    export FIND_BUG
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
    MINIMIZE_REQUIRES="$(cd "$DIR" && realpath "$(which "${MINIMIZE_REQUIRES}")")"
    export MINIMIZE_REQUIRES
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
    ABSOLUTIZE_IMPORTS="$(cd "$DIR" && realpath "$(which "${ABSOLUTIZE_IMPORTS}")")"
    export ABSOLUTIZE_IMPORTS
    function absolutize_imports() {
        "${ABSOLUTIZE_IMPORTS}" "$@"
    }
fi

export -f absolutize_imports


if [ -z "${INLINE_IMPORTS}" ]; then
    function inline_imports() {
        ${PYTHON} "${INLINE_IMPORTS_PY}" "$@"
    }
else
    INLINE_IMPORTS="$(cd "$DIR" && realpath "$(which "${INLINE_IMPORTS}")")"
    export INLINE_IMPORTS
    function inline_imports() {
        "${INLINE_IMPORTS}" "$@"
    }
fi

export -f inline_imports
