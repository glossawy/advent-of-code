module AdventOfCode::Days
  class Day13 < BaseDay
    require_relative './shared/vector_2d'

    FOLD_COMMAND_REGEX = /fold along (?<direction>[xy])=(?<value>\d+)/i.freeze

    def solve_part1
      final = commands.take(1).reduce(initial_holes) do |hs, command|
        method, arg = *command
        send(method, arg, hs)
      end

      solution(
        final.size,
        initial: initial_holes,
        final: final,
        commands: commands
      )
    end

    def solve_part2
      final = commands.reduce(initial_holes) do |hs, command|
        method, arg = *command
        send(method, arg, hs)
      end

      solution(
        paper_to_s(final, padding: 3),
        initial: initial_holes,
        final: final,
        commands: commands
      )
    end

    private

    def paper_to_s(h, padding: 0)
      positions = h.keys
      paper_height = positions.map(&:y).max + 1 + padding
      paper_width = positions.map(&:x).max + 1 + padding

      dot_matrix = (0...paper_height + padding).map { ['.'] * (paper_width + padding * 2) }

      (0...paper_height + padding).each do |y|
        (0...paper_width + padding).each do |x|
          dot_matrix[y][x] = h.key?(Shared::Vector2D.new(x - padding, y - padding)) ? '#' : '.'
        end
      end

      dot_matrix.map { |l| l.join '' }.join $RS
    end

    def initial_holes
      @initial_holes ||=
        fold_h.tap do |initial|
          coords.each do |p|
            initial[p].add(p)
          end
        end
    end

    def coords
      @coords ||= lines.take_while { |s| !s.empty? }.map do |l|
        x, y = *l.split(',').map(&:parse_int!)
        Shared::Vector2D.new(x, y)
      end.to_a
    end

    def commands
      @commands ||= lines.drop(coords.size + 1).map do |cmd_line|
        m = cmd_line.match(FOLD_COMMAND_REGEX)

        case m[:direction]
        when 'x'
          [:vertical_fold, m[:value].parse_int!]
        when 'y'
          [:horizontal_fold, m[:value].parse_int!]
        else
          raise "Cannot parse command: #{cmd_line}"
        end
      end.to_a
    end

    def vertical_fold(at_x, fold_hash)
      # >= might be > here
      positions_in_fold = fold_hash.keys.select { |p| p.x >= at_x }
      position_changes = positions_in_fold.zip(positions_in_fold.map do |p|
        dist = p.x - at_x
        p.scalar_sub(dist * 2, 0)
      end).to_h

      fold_hash.each_with_object(fold_h) do |(pos, overlaps), hsh|
        if position_changes.key?(pos)
          hsh[position_changes[pos]].merge(overlaps)
        else
          hsh[pos] = overlaps
        end
      end
    end

    def horizontal_fold(at_y, fold_hash)
      # >= might be > here
      positions_in_fold = fold_hash.keys.select { |p| p.y >= at_y }
      position_changes = positions_in_fold.zip(positions_in_fold.map do |p|
        dist = p.y - at_y
        p.scalar_sub(0, dist * 2)
      end).to_h

      fold_hash.each_with_object(fold_h) do |(pos, overlaps), hsh|
        if position_changes.key?(pos)
          hsh[position_changes[pos]].merge(overlaps)
        else
          hsh[pos] = overlaps
        end
      end
    end

    def fold_h
      Hash.new { |h, k| h[k] = Set.new }
    end
  end
end
