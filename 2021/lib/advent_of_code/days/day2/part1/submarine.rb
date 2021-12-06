
module AdventOfCode::Days
  class Day2
    module Part1
      class Submarine
        attr_reader :distance, :depth

        def initialize(distance: 0, depth: 0)
          @distance = distance
          @depth = depth
        end

        def product = distance * depth

        def forward(x) = move(horizontal: x)
        def up(x) = move(vertical: -x)
        def down(x) = move(vertical: x)

        private

        def move(horizontal: 0, vertical: 0)
          Submarine.new(distance: distance + horizontal, depth: depth + vertical)
        end
      end
    end
  end
end
