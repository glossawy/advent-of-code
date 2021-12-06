module AdventOfCode::Days
  class Day2 < BaseDay
    require_relative './day2/part1/submarine'
    require_relative './day2/part2/submarine'

    def solve_part1 = private_solve(Part1::Submarine)
    def solve_part2 = private_solve(Part2::Submarine)

    def submarine_path(submarine_class)
      commands.each_with_object([submarine_class.new]) do |(command, args), path|
        path << path.last.send(command, *args)
      end
    end

    private

    def private_solve(submarine_class)
      submarine_path(submarine_class).last.then do |submarine|
        solution(submarine.product, submarine: submarine)
      end
    end

    def commands
      lines.map do |line|
        command, *arguments = line.split
        [command, arguments.map(&:parse_int!)]
      end
    end
  end
end
