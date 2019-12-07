#!/bin/bash

set -e

function strip_v() {
    echo "$1" && shift
    for i in "$@"
    do
	j="${i%.*}"
        if [ "$j.v" == "$i" ] || ([ "$j" == "$i" ] && [ -f "$i.v" ]); then
            echo "-compile" # or -compile
            echo "$j"
        else
            echo "$i"
        fi
    done
}

#cd "$(dirname "$0")"

#echo exec $(strip_v "$@")
echo | exec $(strip_v "$@")
