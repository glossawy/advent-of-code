#!/usr/bin/env bash

ruby -n -e '$tf = 0 unless defined?($tf)' -e 'total_fuel = 0; mass = Integer($_)' -e "while mass > 0; f = (mass / 3) - 2; break if f <= 0; total_fuel += f; mass = f; end" -e '$tf += total_fuel; puts $tf' ${BASH_SOURCE%/*}/../../inputs/day1.in | tail -n1

