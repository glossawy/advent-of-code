module AdventOfCode::Days
  class Day7 < BaseDay
    using Module.new {
      refine(Integer) do
        def triangular_number = (self ** 2 + self)/2
      end
    }

    def solve_part1 = private_solve(&:itself)
    def solve_part2 = private_solve(&:triangular_number)

    private

    def private_solve(&distance_calculation)
      raise 'Missing distance calculation' unless distance_calculation

      positions_counts = horizontal_positions.group_by(&:itself).transform_values(&:count)
      positions_costs = Hash.new { |h,k| h[k] = 0 }
      0.upto(positions_counts.keys.max) do |position|
        positions_counts.each do |other_position, count|
          distance = (other_position - position).abs
          positions_costs[position] += distance_calculation.(distance) * count
        end
      end

      min_position, min_cost = *positions_costs.rassoc(positions_costs.values.min || raise('No minimum'))

      solution(
        min_cost,
        position: min_position,
        positions_costs: positions_costs,
        positions_counts: positions_counts
      )
    end

    def horizontal_positions
      @horizontal_positions ||= lines.to_a.first.split(',').map(&:parse_int!)
    end
  end
end
