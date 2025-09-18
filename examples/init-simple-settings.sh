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