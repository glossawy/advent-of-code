class AdventOfCode::Days::Day4
  module Bingo
    class Board
      attr_reader :matrix, :location_map

      NotOnBoard = Class.new(AdventOfCode::AdventOfCodeError)

      def won? = @is_winning

      def initialize(rows)
        @is_winning = false
        @location_map = {}
        @matrix = []

        rows.each.with_index do |row, r|
          matrix[r] = [false] * row.size
          row.each.with_index do |value, c|
            location_map[value] = [r, c]
          end
        end
      end

      def current_score
        unmarked_numbers.sum
      end

      def mark!(called_number)
        if location_map.key?(called_number)
          r, c = *location_map[called_number]
          matrix[r][c] = true
          check_for_win!(r, c)
        end

        self
      end

      def marked?(number)
        return false unless location_map.key?(number)

        r, c = *location_map[number]
        matrix[r][c]
      end

      def marked_numbers
        location_map.keys.select { |num| marked?(num) }
      end

      def unmarked_numbers
        location_map.keys.reject { |num| marked?(num) }
      end

      def to_s
        cell_width = location_map.keys.map(&:to_s).map(&:size).max
        smat = matrix.map.with_index do |row, r|
          row.map.with_index do |col, c|
            location_map.rassoc([r, c]).first.to_s.rjust(cell_width).then do |colstr|
                (
                  if matrix[r][c]
                    $pastel.black.on_white(colstr).to_s
                  else
                    colstr
                  end
                )
            end
          end.join(' ')
        end.join($RS)

        <<~BOARD
          #{won? ? 'Winning' : 'Incomplete'} board with #{current_score} points
          #{smat}
        BOARD
      end

      private

      def check_for_win!(r, c)
        @is_winning ||= row_filled?(r) || column_filled?(c)
      end

      def row_filled?(r) = matrix[r].all?
      def column_filled?(c) = matrix.all? { |row| row[c] }
    end
  end
end
