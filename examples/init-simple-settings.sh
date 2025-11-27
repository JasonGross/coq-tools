#!/bin/sh

if [ -z "${PYTHON}" ]; then
    PYTHON=python3
    export PYTHON
fi

if [ -z "${GREP}" ]; then
    if command -v ggrep >/dev/null 2>&1; then
        GREP="ggrep"
    else
        GREP="grep"
    fi
    export GREP
fi

FIND_BUG_PY="$(cd "$DIR/.." && pwd)/find-bug.py"
export FIND_BUG_PY
MINIMIZE_REQUIRES_PY="$(cd "$DIR/.." && pwd)/minimize-requires.py"
export MINIMIZE_REQUIRES_PY
ABSOLUTIZE_IMPORTS_PY="$(cd "$DIR/.." && pwd)/absolutize-imports.py"
export ABSOLUTIZE_IMPORTS_PY
INLINE_IMPORTS_PY="$(cd "$DIR/.." && pwd)/inline-imports.py"
export INLINE_IMPORTS_PY
