module AdventOfCode::Days
  class Day1 < BaseDay
    def solve_part1
      solution(reported_pairs.count { |(last, current)|  current > last })
    end

    def solve_part2
      reported_triples.map(&:sum).each_cons(2).then do |sum_pairs|
        solution(sum_pairs.count { |(last, current)| current > last })
      end
    end

    private

    def report_values
      lines.map(&:parse_int!)
    end

    def reported_pairs
      report_values.each_cons(2)
    end

    def reported_triples
      report_values.each_cons(3)
    end
  end
end
