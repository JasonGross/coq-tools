#!/bin/bash

set -e

function strip_v() {
    LAST=""
    DO_ECHO_THIS="yes"
    DO_ECHO_LOAD="yes"
    for i in "$@"
    do
	if [ ! -e "$DO_ECHO_THIS" ]; then
	    echo "$LAST"
	    DO_ECHO_THIS=""
	fi
        j="${i%.*}"
        if [ "$j.v" = "$i" ]; then
            echo "-compile" # or -compile
            echo "$j"
	    DO_ECHO_LOAD=""
	    DO_ECHO_THIS=""
        else
	    LAST="$i"
	    DO_ECHO_THIS="yes"
        fi

    done

    if [ ! -e "$DO_ECHO_THIS" ]; then
	if [ ! -e "$DO_ECHO_LOAD" ]; then
	    echo "-compile"
	fi
	echo "$LAST"
    fi

}

#cd "$(dirname "$0")"

#echo exec $(strip_v "$@")
echo | exec $(strip_v "$@")
