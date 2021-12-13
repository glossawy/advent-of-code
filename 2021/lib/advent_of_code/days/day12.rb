module AdventOfCode::Days
  class Day12 < BaseDay
    def solve_part1
      all_paths('start', 'end').then do |paths|
        solution(
          paths.size,
          paths: paths,
          adjacency_map: adjacency_map
        )
      end
    end

    def solve_part2
      all_paths_with_revisit('start', 'end').then do |paths|
        solution(
          paths.size,
          paths: paths,
          adjacency_map: adjacency_map
        )
      end
    end

    private

    def adjacency_map
      @adjacency_map ||=
        lines.to_a.each_with_object(Hash.new { |h, k| h[k] = Set.new }) do |line, adj|
          from_node, to_node = *line.split('-')
          adj[from_node].add(to_node)
          adj[to_node].add(from_node)
        end
    end

    def all_paths(from_node, to_node, paths: [], current_path: [])
      current_path = [*current_path, from_node]
      if from_node == to_node
        paths << current_path
      else
        next_hops(from_node).each do |n|
          if unlimited_node?(n) || !current_path.include?(n)
            all_paths(n, to_node, paths: paths, current_path: current_path)
          end
        end
      end

      paths
    end

    def all_paths_with_revisit(from_node, to_node, paths: [], current_path: [])
      current_path = [*current_path, from_node]
      if from_node == to_node
        paths << current_path
      else
        next_hops(from_node).each do |n|
          next if n == 'start' # start is now limited

          if unlimited_node?(n) || !current_path.include?(n) || can_revisit_on?(current_path)
            all_paths_with_revisit(n, to_node, paths: paths, current_path: current_path)
          end
        end
      end

      paths
    end

    def can_revisit_on?(path)
      path.reject { |n| unlimited_node?(n) }.then do |p|
        p.uniq.size == p.size
      end
    end

    def unlimited_node?(x) = (x.upcase == x)
    def limited_node?(x) = !unlimited_node?(x)
    def next_hops(x) = adjacency_map[x]
  end
end
