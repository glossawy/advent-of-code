module AdventOfCode::Days
  class Day3 < BaseDay
    require_relative './day3/bit_histogram'

    INPUT_BIT_LENGTH = 12

    def solve_part1
      BitHistogram.new(INPUT_BIT_LENGTH).process_all(numbers).then do |result|
        solution(result.most_frequent_bits * result.least_frequent_bits, histogram: result)
      end
    end

    def solve_part2
      numbers.to_a.then do |bitpatterns|
        oxygen = calculate_oxygen_rating(bitpatterns)
        carbon_dioxide = calculate_co2_rating(bitpatterns)

        solution(oxygen * carbon_dioxide, oxygen_rating: oxygen, co2_rating: carbon_dioxide)
      end
    end

    private

    def numbers
      lines.map { |bits| Integer(bits, 2) }
    end

    def calculate_oxygen_rating(bitpatterns) = rating_helper(bitpatterns, type: :most_frequent, tie_break: 1)
    def calculate_co2_rating(bitpatterns) = rating_helper(bitpatterns, type: :least_frequent, tie_break: 0)

    def rating_helper(bitpatterns, bitlength: INPUT_BIT_LENGTH, position: bitlength, type:, tie_break:)
      return bitpatterns.first if bitpatterns.size == 1
      raise 'Something went wrong, no more bitpatterns' if bitpatterns.empty?
      raise 'Something went wrong, position went below 1' if position < 1

      BitHistogram.new(bitlength).then do |histogram|
        histogram.process_all(bitpatterns)
        bin = histogram.bin_at(position)

        target = bin.public_send(type, tie_break: tie_break) << bin.shift_amount
        rating_helper(
          bitpatterns.select { |bp| bp & bin.bitmask == target },
          bitlength: bitlength,
          position: position - 1,
          type: type,
          tie_break: tie_break
        )
      end
    end
  end
end
