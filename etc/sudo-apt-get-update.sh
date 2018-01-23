#!/usr/bin/env bash

(sudo apt-get update "$@" 2>&1 || echo 'E: update failed') | tee /tmp/apt.err
! grep -q '^[WE]' /tmp/apt.err || exit $?
