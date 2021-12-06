require 'forwardable'

module AdventOfCode::Days
  class BaseDay
    def self.day_name
      @day_name ||= name.demodulize.sub(/(day)(\d+)/i, '\1 \2')
    end

    Solution = Struct.new(:additional_data, :solution, keyword_init: true) do
      def data = OpenStruct.new(additional_data)
    end

    attr_reader :input_file

    def initialize(input_file)
      @input_file = input_file
    end

    def solve(part)
      method_name = "solve_#{part}"

      raise AdventOfCode::NoSolutionYet, "#{self.class.day_name} does not have a solution yet for #{part}" \
        unless self.class.method_defined?(method_name)

      send(method_name)
    end

    private

    def solution(value, **additional_data) = Solution.new(solution: value, additional_data: additional_data)

    def input = input_file.read
    def lines = input_file.each_line.lazy.map(&:strip)
  end
end
