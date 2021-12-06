module AdventOfCode::Days
  class Day4 < BaseDay
    require_relative './day4/bingo/board'

    BOARD_SIZE = 5

    def solve_part1
      calls.each do |called_number|
        boards.each { |b| b.mark!(called_number) }

        boards.find(&:won?).then do |winning_board|
          next if winning_board.nil?

          return solution(
            winning_board.current_score * called_number,
            boards: boards,
            winning_board: winning_board,
            calls: calls,
            winning_score: winning_board.current_score,
            winning_number: called_number
          )
        end
      end
    end

    def solve_part2
      win_order = []
      playing_boards = Set.new(boards).compare_by_identity

      calls.each do |called_number|
        playing_boards.each { |b| b.mark!(called_number) }

        playing_boards.select(&:won?).then do |winners|
          win_order.concat winners
          playing_boards -= winners
        end

        if playing_boards.empty?
          win_order.last.then do |losing_board|
            return solution(
              losing_board.current_score * called_number,
              boards: boards,
              losing_board: losing_board,
              calls: calls,
              losing_score: losing_board.current_score,
              losing_number: called_number
            )
          end
        end
      end
    end

    private

    def calls
      lines.first
    end

    def boards
      @board ||=
        lines.drop(1).each_slice(BOARD_SIZE).map do |raw_board|
          Bingo::Board.new(raw_board)
        end
    end

    def lines
      @lines ||=
        begin
          ls = super.to_a.reject(&:empty?)
          [
            ls.first.split(',').map(&:parse_int!),
            *ls.drop(1).map do |line|
              line.split(' ').map(&:parse_int!)
            end
          ]
        end
    end
  end
end
