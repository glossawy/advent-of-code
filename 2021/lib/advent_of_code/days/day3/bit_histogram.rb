module AdventOfCode::Days
  class Day3
    class BitHistogram
      attr_reader :bins, :bit_length

      class Bin
        attr_reader :ones, :zeroes, :position, :bitmask, :shift_amount

        def initialize(position)
          @ones = @zeroes = 0
          @position = position
          @shift_amount = position - 1
          @bitmask = 2 ** (position - 1)
        end

        def process(bitpattern)
          if (bitpattern & bitmask).zero?
            @zeroes += 1
          else
            @ones += 1
          end
        end

        def most_frequent(tie_break: 1)
          return tie_break if tied?

          zeroes > ones ? 0 : 1
        end

        def least_frequent(tie_break: 1)
          return tie_break if tied?

          zeroes < ones ? 0 : 1
        end

        def tied? = (zeroes == ones)
      end

      def initialize(bitlen)
        @bit_length = bitlen
        reset_bins!
      end

      def bin_at(i)
        bins[i - 1]
      end

      def most_frequent_bits
        raise 'No processing done yet' if bins.nil?

        bins.reduce(0) do |acc, bin|
          acc | (bin.most_frequent << bin.shift_amount)
        end
      end

      def least_frequent_bits
        raise 'No processing done yet' if bins.nil?

        ((2 ** bit_length) - 1) ^ most_frequent_bits
      end

      def process(bitpattern)
        tap do
          bins.each { |bin| bin.process(bitpattern) }
        end
      end

      def process_all(bitpatterns)
        tap do
          bitpatterns.each { |bp| process(bp) }
        end
      end

      def reset_bins!
        @bins = (1..bit_length).map { |i| BitHistogram::Bin.new(i) }
      end
    end
  end
end
