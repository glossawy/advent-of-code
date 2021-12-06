
module AdventOfCode::Days
  class Day2
    module Part2
      class Submarine < Part1::Submarine
        attr_reader :distance, :depth, :aim

        def initialize(distance: 0, depth: 0, aim: 0)
          super(distance: distance, depth: depth)
          @aim = aim
        end

        def forward(x) = move(horizontal: x, vertical: x * aim)
        def up(x) = move(angular: -x)
        def down(x) = move(angular: x)

        private

        def move(horizontal: 0, vertical: 0, angular: 0)
          Submarine.new(distance: distance + horizontal, depth: depth + vertical, aim: aim + angular)
        end
      end
    end
  end
end
