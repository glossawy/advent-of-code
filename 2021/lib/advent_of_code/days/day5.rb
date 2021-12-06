module AdventOfCode::Days
  class Day5 < BaseDay
    require_relative './shared/vector_2d'

    def solve_part1 = (private_solve :part1)
    def solve_part2 = (private_solve :part2)

    private

    def private_solve(part)
      case part
      when :part1
        segments = line_segments.select { |l| l.vertical? || l.horizontal? }
      when :part2
        segments = line_segments
      else
        raise "Unknown part: #{part}"
      end

      map = Hash.new { |h, k| h[k] = 0 }
      segments.each do |segment|
        segment.to_points.each do |point|
          map[point] += 1
        end
      end

      output_map(map, is_part1: (part == :part1)) if ENV['DAY5_PRINT_MAP'] == 'true'

      solution(
        map.values.select { |v| v > 1 }.size,
        segments: segments,
        map: map
      )
    end

    def line_segments
      @line_segments ||=
        lines.map do |segment_desc|
          first_coord, second_coord = *segment_desc.split(' -> ')

          first_coord = first_coord.split(',').map(&:parse_int!)
          second_coord = second_coord.split(',').map(&:parse_int!)

          LineSegment.new(Shared::Vector2D.new(*first_coord), Shared::Vector2D.new(*second_coord))
        end.to_a
    end

    def output_map(map, is_part1:)
      filename = is_part1 ? 'day5_map_part1.txt' : 'day5_map_part2.txt'
      max_x = map.keys.map(&:x).max
      max_y = map.keys.map(&:y).max
      matrix = (0..max_y).map { (0..max_x).map { 0 } }
      map.each do |point, v|
        matrix[point.y][point.x] = v
      end
      matrix.map! { |row| row.map!(&:to_s) }
      cell_width = matrix.flatten.map(&:size).max
      open(Pathname('.').join(filename), 'w') do |f|
        matrix.each do |row|
          f.puts row.map { |i| i.rjust(cell_width) }.join(' ')
        end
      end
    end

    class LineSegment
      attr_reader :from_vect, :to_vect

      def initialize(from, to)
        @from_vect = from
        @to_vect = to
      end

      def horizontal? = (from_vect.y == to_vect.y)
      def vertical? = (from_vect.x == to_vect.x)
      def as_vector = to_vect.sub(from_vect)

      def to_points
        as_vector.then do |self_vector|
          slope_y = self_vector.y
          slope_x = self_vector.x

          if slope_x.zero? && slope_y.zero?
            # Single point
            [from_vect]
          elsif slope_x.zero?
            # Vertical Line
            diff = to_vect.y - from_vect.y
            sign = diff.abs / diff
            (0..diff.abs).map do |dy|
              from_vect.scalar_add(0, sign*dy)
            end
          elsif slope_y.zero?
            # Horizontal Line
            diff = to_vect.x - from_vect.x
            sign = diff.abs / diff
            (0..diff.abs).map do |dx|
              from_vect.scalar_add(sign*dx, 0)
            end
          else
            # Sloped line
            slope_y.gcd(slope_x).then do |gcd|
              slope_y /= gcd
              slope_x /= gcd
            end

            current = from_vect
            while current != to_vect
              result << current
              current = current.scalar_add(slope_x, slope_y)
            end
            [*result, current]
          end
        end
      end

      def ==(other)
        from_vect == other.from_vect &&
          to_vect == other.to_vect
      end

      def eql?(other) = (self == other)
      def hash = [from_vect, to_vect].hash
    end
  end
end
