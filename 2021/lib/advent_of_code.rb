lib = File.expand_path('../lib', __dir__)
$LOAD_PATH.unshift(lib) unless $LOAD_PATH.include?(lib)

require 'ostruct'
require 'pastel'
require 'pathname'
require 'pry'
require 'set'

$pastel = Pastel.new

module AdventOfCode
  AdventOfCodeError = Class.new(StandardError)
  NoSolutionYet = Class.new(AdventOfCodeError)

  require 'advent_of_code/core_ext/string'

  require 'advent_of_code/days'

  module Paths
    class << self
      def root
        Pathname(File.expand_path('..', __dir__))
      end

      def inputs
        root.join 'inputs'
      end

      def days
        inputs.join 'days'
      end
    end
  end

  def self.paths = Paths
  def self.solver_for(day, part) = Days.solver_for(day, part)
  def self.solve_for(day, part) = Days.solve_for(day, part)

  def self.placeholder(msg = 'Placeholder for future solution') = raise(NoSolutionYet, msg)
end
