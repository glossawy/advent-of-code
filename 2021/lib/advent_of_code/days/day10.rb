module AdventOfCode::Days
  class Day10 < BaseDay
    using Module.new {
      refine(Array) do
        def second = self[1]
      end
    }

    Validation = Struct.new(:chunk, :errors)

    CorruptionError = Struct.new(:opening, :expected, :found) do
      def message = "Expected '#{expected}' but found '#{found}' instead, for '#{opening}'"
      def corruption? = true
      def incomplete? = false
    end

    IncompleteError = Struct.new(:opening, :expected) do
      def message = "Missing '#{expected}' to close '#{opening}'"
      def corruption? = false
      def incomplete? = true
    end

    OPENINGS = %w^{ [ ( <^
    CLOSINGS = %w^} ] ) >^

    OPEN_TO_CLOSE = OPENINGS.zip(CLOSINGS).to_h.freeze
    CLOSE_TO_OPEN = CLOSINGS.zip(OPENINGS).to_h.freeze

    def solve_part1
      illegality_scores = { ')' => 3, ']' => 57, '}' => 1197, '>' => 25137 }

      results = validation_results.select do |v|
        v.errors.any?(&:corruption?)
      end.map do |v|
        Validation.new(v.chunk, v.errors.select(&:corruption?))
      end

      first_errors = results.map { |v| v.errors.first }
      solution(
        first_errors.map { |err| illegality_scores[err.found] }.sum,
        first_errors: first_errors,
        all_results: results
      )
    end

    def solve_part2
      illegality_modifiers = { ')' => 1, ']' => 2, '}' => 3, '>' => 4 }

      results = validation_results.reject do |v|
        v.errors.any?(&:corruption?) || v.errors.none?(&:incomplete?)
      end.map do |v|
        Validation.new(v.chunk, v.errors.select(&:incomplete?))
      end

      completion_suffixes = results.map { |v| v.errors.map { |err| err.expected } }

      total_scores = completion_suffixes.map do |suffix_chars|
        suffix_chars.reduce(0) do |s, c|
          (s * 5) + illegality_modifiers[c]
        end
      end

      total_scores = completion_suffixes.zip(total_scores)
      sorted_scores = total_scores.sort_by(&:second)

      solution(
        middle_score(sorted_scores.map(&:second)),
        results: results,
        completion_suffixes: completion_suffixes,
        total_scores: total_scores,
        sorted_scores: sorted_scores
      )
    end

    private

    def middle_score(scores)
      scores[scores.size / 2]
    end

    def validation_results
      @validation_results ||=
        lines.map do |chunk|
          Validation.new(chunk, validate_chunk(chunk))
        end.to_a
    end

    def validate_chunk(chunk)
      open_stack = []
      [].tap do |errors|
        chunk.each_char do |c|
          if opening?(c)
            open_stack << c
          elsif closing?(c)
            opening = open_stack.pop
            expecting = OPEN_TO_CLOSE[opening]
            unless c == expecting
              errors << CorruptionError.new(opening, expecting, c)
            end
          else
            raise "Unknown chunk character: #{c}"
          end
        end

        if open_stack.any?
          errors << IncompleteError.new(open_stack.last, OPEN_TO_CLOSE[open_stack.pop]) until open_stack.empty?
        end
      end
    end

    def opening?(c) = OPENINGS.include?(c)
    def closing?(c) = CLOSINGS.include?(c)
  end
end
