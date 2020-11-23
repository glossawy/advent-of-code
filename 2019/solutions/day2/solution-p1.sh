#!/usr/bin/env bash

# Equivalent Ruby Program
#
# while gets()  # Implied by -n
#   ($F = $_.split(',')) && next unless defined?($F) # implied by -a -F,
#   unless defined?($ops)
#     $ops = $F.map { |v| Integer(v) }
#   else
#     i = 0
#     $ops[1], $ops[2] = 12, 2
#     while $ops[i] != 99
#       case $ops[i]
#       when 1
#         $ops[$ops[i + 3]] = $ops[$ops[i + 1]] + $ops[$ops[i + 2]]
#         i += 4
#       when 2
#         $ops[$ops[i + 3]] = $ops[$ops[i + 1]] * $ops[$ops[i + 2]]
#         i += 4
#       when 99
#         break
#       end # note, I forget an else branch
#     end
#
#     puts "pos : val"
#     puts "---------"
#     $ops.each.with_index { |x, i| puts "#{i.to_s.ljust(3)} : #{x}" }
#   end
# end

ruby -na -F, \
  -e 'unless defined?($ops); $ops = $F.map { |v| Integer(v) }' \
  -e 'else; i = 0; $ops[1], $ops[2] = 12, 2' \
  -e 'while $ops[i] != 99 ' \
    -e 'case $ops[i]' \
    -e 'when 1; $ops[$ops[i+3]] = $ops[$ops[i+1]] + $ops[$ops[i+2]]; i += 4' \
    -e 'when 2; $ops[$ops[i+3]] = $ops[$ops[i+1]] * $ops[$ops[i+2]]; i += 4' \
    -e 'when 99; break' \
    -e 'end' \
  -e 'end; puts "pos : val"; puts "---------"; $ops.each.with_index { |x, i| puts "#{i.to_s.ljust(3)} : #{x}" }; end' ${BASH_SOURCE%/*}/../../inputs/day2.in
