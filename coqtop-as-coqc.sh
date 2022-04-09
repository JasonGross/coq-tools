#!/usr/bin/env bash

set -e

function strip_v() {
    echo "$1" && shift
    prev_top=""
    for i in "$@"
    do
	j="${i%.*}"
        if [ -z "${prev_top}" ] && ([ "$j.v" == "$i" ] || ([ "$j" == "$i" ] && [ -f "$i.v" ])); then
            echo "-compile" # or -compile
            echo "$j"
        else
            echo "$i"
        fi
        prev_top=""
        if [ "$i" == "-top" ] || [ "$i" == "-topfile" ]; then
            prev_top="yes"
        fi
    done
}

#cd "$(dirname "$0")"

#echo exec $(strip_v "$@")
echo | exec $(strip_v "$@")
