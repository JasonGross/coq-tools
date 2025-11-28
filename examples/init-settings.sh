#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
. "$DIR/init-simple-settings.sh"

strip_for_grep() {
    s="$(printf "%s" "$1" | "$GREP" -v '^$' | tr -d '\r')"
    # Trim leading whitespace
    s="${s#"${s%%[![:space:]]*}"}"
    # Trim trailing whitespace
    s="${s%"${s##*[![:space:]]}"}"
    s="$(printf "%s" "$s" | tr '\n' '\1')"
    printf "%s" "$s"
}

export -f strip_for_grep


strip_escape_for_grep() {
    s="$(printf "%s" "$1" | "$GREP" -v '^$' | tr -d '\r')"
    # Trim leading whitespace
    s="${s#"${s%%[![:space:]]*}"}"
    # Trim trailing whitespace
    s="${s%"${s##*[![:space:]]}"}"
    s="$(printf "%s" "$s" | tr '\n' '\1' | sed s'/\*/\\\*/g')"
    printf "%s" "$s"
}

export -f strip_escape_for_grep

grep_contains() {
    count="$(printf '%s' "$1" | "$GREP" -c "$2")"
    if [ -z "$count" ]; then
        return 1
    elif [ "$count" -lt 1 ]; then
        return 1
    else
        return 0
    fi
}

export -f grep_contains

if [ -z "${FIND_BUG}" ]; then
    find_bug() {
        ${PYTHON} "${FIND_BUG_PY}" "$@"
    }
else
    FIND_BUG="$(cd "$DIR" && realpath "$(which "${FIND_BUG}")")"
    export FIND_BUG
    find_bug() {
        "${FIND_BUG}" "$@"
    }
fi

export -f find_bug

if [ -z "${MINIMIZE_REQUIRES}" ]; then
    minimize_requires() {
        ${PYTHON} "${MINIMIZE_REQUIRES_PY}" "$@"
    }
else
    MINIMIZE_REQUIRES="$(cd "$DIR" && realpath "$(which "${MINIMIZE_REQUIRES}")")"
    export MINIMIZE_REQUIRES
    minimize_requires() {
        "${MINIMIZE_REQUIRES}" "$@"
    }
fi

export -f minimize_requires

if [ -z "${ABSOLUTIZE_IMPORTS}" ]; then
    absolutize_imports() {
        "${PYTHON}" "${ABSOLUTIZE_IMPORTS_PY}" "$@"
    }
else
    ABSOLUTIZE_IMPORTS="$(cd "$DIR" && realpath "$(which "${ABSOLUTIZE_IMPORTS}")")"
    export ABSOLUTIZE_IMPORTS
    absolutize_imports() {
        "${ABSOLUTIZE_IMPORTS}" "$@"
    }
fi

export -f absolutize_imports


if [ -z "${INLINE_IMPORTS}" ]; then
    inline_imports() {
        "${PYTHON}" "${INLINE_IMPORTS_PY}" "$@"
    }
else
    INLINE_IMPORTS="$(cd "$DIR" && realpath "$(which "${INLINE_IMPORTS}")")"
    export INLINE_IMPORTS
    inline_imports() {
        "${INLINE_IMPORTS}" "$@"
    }
fi

export -f inline_imports

if [ -z "${RELPATH}" ]; then
    relpath() {
        "${PYTHON}" -c "import os, sys; print(os.path.relpath(*sys.argv[1:]))" "$@"
    }
else
    RELPATH="$(cd "$DIR" && realpath "$(which "${RELPATH}")")"
    export RELPATH
    relpath() {
        "${RELPATH}" "$@"
    }
fi

export -f relpath
