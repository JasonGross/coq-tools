#!/bin/bash

set -e

function strip_v() {
    for i in "$@"
    do
        j="${i%.*}"
        if [ "$j.v" = "$i" ]; then
            echo "-load-vernac-source" # or -compile
            echo "$j"
        else
            echo "$i"
        fi

    done
}

#cd "$(dirname "$0")"

#echo exec $(strip_v "$@")
echo | exec $(strip_v "$@")
