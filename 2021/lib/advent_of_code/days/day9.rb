module AdventOfCode::Days
  class Day9 < BaseDay
    def solve_part1
      solution(
        low_points.map(&:first).sum(&:succ),
        low_points: low_points,
        height_map: height_map
      )
    end

    def solve_part2
      print_height_map

      top_3 = basins.map(&:size).sort.reverse.take(3)

      solution(
        top_3.reduce(:*),
        basins: basins,
        height_map: height_map
      )
    end

    private

    def basins
      @basins ||=
        low_points.map { |(h, r, c)| find_basin(h, r, c) }
    end

    def low_points
      @low_points ||=
        height_map.map.with_index do |row, r|
          row.map.with_index do |height, c|
            if cardinal_neighbors(r, c).all? { |(h2, _r2, _c2)| h2 > height }
              [height, r, c]
            end
          end
        end.flatten(1).compact
    end

    def height_map
      @height_map ||=
        lines.map do |line|
          line.chars.map(&:parse_int!)
        end.to_a
    end

    def print_height_map
      all_basin_positions = basins.reduce(&:|)

      height_map.each.with_index do |row, r|
        row.each.with_index do |height, c|
          if all_basin_positions.include?([height, r, c])
            print $pastel.black.on_white(height.to_s)
          else
            print height.to_s
          end
        end
        puts
      end
    end

    def find_basin(low_point, r, c)
      # Basic fill algorithm via BFS
      basin_locations = Set.new([[low_point, r, c]])
      queue = [[r, c]]

      until queue.empty?
        r2, c2 = *queue.shift

        cardinal_neighbors(r2, c2).each do |(h3, r3, c3)|
          next if basin_locations.include?([h3, r3, c3]) || h3 == 9

          basin_locations.add([h3, r3, c3])
          queue.push([r3, c3])
        end
      end

      basin_locations
    end

    def cardinal_neighbors(r, c)
      points = [
        [r - 1, c],
        [r + 1, c],
        [r, c - 1],
        [r, c + 1]
      ].select do |(r2, c2)|
        (r2 >= 0 && r2 < height_map.size) && (c2 >= 0 && c2 < height_map[0].size)
      end

      points.map { |(r2, c2)| [height_map[r2][c2], r2, c2] }
    end
  end
end
