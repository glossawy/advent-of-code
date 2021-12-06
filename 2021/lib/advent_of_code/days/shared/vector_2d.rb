module AdventOfCode::Days
  module Shared
    class Vector2D
      attr_reader :first, :second

      alias x first
      alias y second

      alias r y
      alias c x

      def initialize(x, y)
        @first = x
        @second = y
      end

      def magnitude_sq = (first * first + second * second)

      def scale(s) = Vector2D.new(first * s, second * s)

      def scalar_add(dx, dy) = Vector2D.new(first + dx, second + dy)
      def scalar_add!(dx, dy) = tap { @first += dx; @second += dy }
      def scalar_sub(dx, dy) = Vector2D.new(first - dx, second - dy)
      def scalar_sub!(dx, dy) = tap { @first -= dx; @second -= dy }

      def add(other_vect) = scalar_add(other_vect.first, other_vect.second)
      def add!(other_vect) = scalar_add!(other_vect.first, other_vect.second)
      def sub(other_vect) = scalar_sub(other_vect.first, other_vect.second)
      def sub!(other_vect) = scalar_sub!(other_vect.first, other_vect.second)

      def dot(other_vect) = (first * other_vect.first + second * other_vect.second)
      def cross(other_vect) = (first * other_vect.second - second * other_vect.first)
      def collinear_with?(other_vect) = cross(other_vect).zero?
      def perpendicular = Vector2D.new(second, -first)

      def ==(other)
        self.class == other.class &&
          self.first == other.first &&
          self.second == other.second
      end

      def eql?(other) = (self == other)
      def hash = [first, second].hash
    end
  end
end
