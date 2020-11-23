#!/usr/bin/env bash

ruby -n -e '$s = 0 unless defined?($s)' -e '$s += (Integer($_) / 3) - 2; puts $s' ${BASH_SOURCE%/*}/../../inputs/day1.in | tail -n1

