module AdventOfCode::Days
  class Day15 < BaseDay
    require 'fibonacci_heap'

    require_relative './shared/vector_2d'

    Pos = Shared::Vector2D

    def solve_part1 = private_solve
    def solve_part2 = private_solve

    private

    def private_solve
      min_paths(top_left).then do |(dist, prev)|
        solution(
          dist[bottom_right],
          dist: dist, prev: prev, chosen_path: path_from(prev, bottom_right),
          risk_matrix: input_matrix,
        )
      end
    end

    # This finds all shortest paths from source to any other node, normal dijkstra i just
    # didnt add the optional "break if current == target" condition
    #
    # Was fine with it since I was using a fibonacci heap with sufficient decrease_key perf
    #
    # i just didnt want to implement a binheap and worry about decrease_key, i did that in college
    def min_paths(source)
      queue = FibonacciHeap::Heap.new
      seen = Set.new
      dist = {}; prev = {}

      all_vertices.each do |pos|
        dist[pos] = Float::INFINITY
        prev[pos] = nil
      end

      dist[source] = 0

      pos_to_node = dist.each_with_object({}) do |(pos, dist), ptn|
        queue.insert(ptn[pos] = FibonacciHeap::Node.new(dist, pos))
      end

      until queue.empty?
        heap_node = queue.pop
        current = heap_node.value
        seen.add(current)

        neighbors_of(current).each do |n|
          next if seen.include? n

          new_cost = dist[current] + input_matrix[n.r][n.c]
          if new_cost < dist[n]
            dist[n] = new_cost
            prev[n] = current
            queue.decrease_key(pos_to_node[n], new_cost)
          end
        end
      end

      [dist, prev]
    end

    def input_matrix
      @input_matrix ||=
        lines.to_a.map do |r|
          r.split('').map(&:parse_int!)
        end
    end

    def path_from(prev, target)
      path = []
      until target.nil?
        path << target
        target = prev[target]
      end

      path.reverse
    end

    def all_vertices
      @all_vertices ||=
        (0...rowsize).flat_map do |r|
          (0...colsize).map do |c|
            Pos.new(r, c)
          end
        end
    end

    def neighbors_of(pos)
      [
        pos.scalar_add(1, 0),
        pos.scalar_add(0, 1),
        pos.scalar_add(-1, 0),
        pos.scalar_add(0, -1),
      ].select { |p| within_map? p }
    end

    def rowsize = (@rowsize ||= input_matrix.size)
    def colsize = (@colsize ||= input_matrix.first.size)

    def top_left = Pos.new(0, 0)
    def bottom_right = Pos.new(rowsize - 1, colsize - 1)

    def within_map?(pos) = (pos.r >= 0 && pos.r < rowsize) && (pos.c >= 0 && pos.c < colsize)
  end
end
