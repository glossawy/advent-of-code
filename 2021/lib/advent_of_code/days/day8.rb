module AdventOfCode::Days
  class Day8 < BaseDay
    Pattern = Struct.new(:signals, :output) do
      def all_entries = [*signals, *output]
    end

    def solve_part1
      all_outputs = patterns.flat_map(&:output)

      solution(
        all_outputs.count { |signal| [2, 4, 3, 7].include?(signal.size) },
        outputs: all_outputs,
        patterns: patterns
      )
    end

    NUMBER_REQUIREMENTS = {
      0 => %i[top top_left top_right bottom_left bottom_right bottom],
      1 => %i[top_right bottom_right],
      2 => %i[top top_right middle bottom_left bottom],
      3 => %i[top top_right middle bottom_right bottom],
      4 => %i[top_left top_right middle bottom_right],
      5 => %i[top top_left middle bottom_right bottom],
      6 => %i[top top_left middle bottom_left bottom_right bottom],
      7 => %i[top top_right bottom_right],
      8 => %i[top top_right middle top_left bottom_left bottom_right bottom],
      9 => %i[top_left top top_right middle bottom_right bottom]
    }.transform_values { |v| Set.new(v) }

    ALL_SEGMENTS = NUMBER_REQUIREMENTS.values.reduce(&:|)

    SEGMENT_COUNT_TO_NUMBERS = NUMBER_REQUIREMENTS.each_with_object(Hash.new { |h, k| h[k] = Set.new }) do |(number, segments), h|
      h[segments.size].add(number)
    end

    def solve_part2
      satisfiability_checkers = []
      outputs = patterns.map do |pattern|
        could_bes = Hash.new { |h, k| h[k] = Set.new }
        satisfy_checker = SatisfiabilityProblem.new

        pattern.all_entries.each do |signal|
          could_bes[signal].merge(SEGMENT_COUNT_TO_NUMBERS[signal.size])
        end

        could_bes.each do |signal, numbers|
          satisfy_checker.add_requirements(*numbers.map { |num| [signal, NUMBER_REQUIREMENTS[num]] })
        end

        assignment = search_for_assignment(satisfy_checker)

        satisfiability_checkers << satisfy_checker

        pattern.output.map do |output_signal|
          NUMBER_REQUIREMENTS.rassoc(Set.new(output_signal.chars.map { |c| assignment[c] })).first
        end.reverse.map.with_index do |digit, power|
          digit * (10 ** power)
        end.sum
      end

      solution(
        outputs.sum,
        outputs: outputs,
        satisfiability_checkers: satisfiability_checkers
      )
    end

    private

    def search_for_assignment(checker)
      possible_assignments = all_possible_assignments.dup

      until possible_assignments.empty?
        assignments = possible_assignments.pop
        return assignments if checker.satisfy?(assignments)
      end

      raise 'None found!'
    end

    def all_possible_assignments
      @all_possible_assignments ||=
        ALL_SEGMENTS.to_a.then do |segs|
          segs.product(*([segs]*6))
        end.select do |segment_lists|
          segment_lists.uniq.size == 7
        end.map do |segment_list|
          %w[a b c d e f g].zip(segment_list).to_h
        end
    end

    def to_assignment(could_bes, step)
      step.map { |signal, idx| [signal, could_bes[signal][idx]] }.to_h
    end

    def patterns
      @patterns ||=
        lines.map do |line|
          signals, output = *line.split('|').map { |side| side.strip.split(' ') }
          Pattern.new(signals, output)
        end.to_a
    end

    class SatisfiabilityProblem
      attr_reader :conditions

      def initialize
        @conditions = []
      end

      def add_requirements(requirement, *requirements)
        conditions.push([requirement, *requirements])
      end

      def satisfy?(assignments)
        conditions.all? do |clause|
          clause.any? do |cond|
            signal, required_segments = *cond

            Set.new(signal.chars.map { |c| assignments[c] }) == required_segments
          end
        end
      end

      def to_s
        conditions.map do |clause|
          signal = clause.first.first

          t = clause.map do |cond|
            *, segs = *cond
            NUMBER_REQUIREMENTS.rassoc(segs).first.to_s
          end.join(' || ')

          "(mapping applied to '#{signal}' yields segments for #{t})"
        end.join(' && ')
      end
    end
  end
end
