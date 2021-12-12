module AdventOfCode::Days
  class Day11 < BaseDay
    require_relative './shared/vector_2d'

    Pos = Shared::Vector2D

    def solve_part1
      (1..100).sum { step!.size }.then do |flashes|
        solution(
          flashes,
          octopus_map: octopus_map
        )
      end
    end

    def solve_part2
      cycle_start = 0

      (cycle_start += 1; step!) until octopus_map.values.all?(&:zero?)

      solution(
        cycle_start,
        cycle: (0..).lazy.map { |i| cycle_start + (i * 10) }
      )
    end

    private

    def step!
      energize_all!
      flash!.tap do |flashed|
        reset!(flashed)
      end
    end

    def reset!(octs)
      octs.each do |oct|
        octopus_map[oct] = 0
      end
    end

    def energize_all!
      octopus_map.transform_values!(&:succ)
    end

    def energize!(positions)
      positions.each do |pos|
        octopus_map[pos] += 1
      end
    end

    def flashable?(octopus)
      octopus_map[octopus] > 9
    end

    def flash!
      Set.new.tap do |flashed|
        to_flash = octopus_map.keys.select { |o| flashable? o }

        until to_flash.empty?
          flashing_oct = to_flash.shift

          unless flashed.include?(flashing_oct)
            flashed.add(flashing_oct)

            all_neighbors(flashing_oct).then do |neighbors|
              # Ignore already flashed
              neighbors.subtract flashed
              binding.pry unless neighbors.all? { |n| octopus_map.key?(n) }
              energize!(neighbors)
              neighbors.keep_if { |n| flashable? n }
              to_flash.concat(neighbors.to_a)
            end
          end
        end
      end
    end

    def octopus_map
      @octopus_map ||=
        lines.to_a.map.with_index do |line, r|
          line.chars.map.with_index do |vs, c|
            [Pos.new(r, c), vs.parse_int!]
          end
        end.flatten(1).to_h
    end

    def rowsize = (@rowsize ||= octopus_map.keys.map(&:r).max)
    def colsize = (@colsize ||= octopus_map.keys.map(&:c).max)

    def all_neighbors(pos)
      Set.new(
        [
          [1, 0], # above
          [1, 1],
          [0, 1],
          [-1, 1],
          [-1, 0], # below
          [-1, -1],
          [0, -1],
          [1, -1]
        ].map do |(dr, dc)|
          pos.scalar_add(dr, dc)
        end.select do |npos|
          npos.r.between?(0, rowsize) && npos.c.between?(0, colsize)
        end
      )
    end
  end
end
