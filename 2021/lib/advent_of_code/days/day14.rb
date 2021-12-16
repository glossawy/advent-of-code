module AdventOfCode::Days
  class Day14 < BaseDay
    def solve_part1 = private_solve(10)
    def solve_part2 = private_solve(40)

    private

    def private_solve(nsteps)
      final = (1..nsteps).reduce(initial_counts) do |pc, _i|
        step(pc)
      end

      atoms_only = final.select { |k, _v| k.size == 1 }
      low, high = *atoms_only.minmax_by { |s| s[1] }

      solution(
        high[1] - low[1],
        steps: nsteps,
        high: high, low: low,
        final: final,
        initial: initial_counts,
        rules: pair_insertion_rules
      )
    end

    def make_histogram = Hash.new { |h, k| h[k] = 0 }

    def initial_counts
      @initial_counts ||=
        polymer_template.chars.each_cons(2).each_with_object(make_histogram) do |(a, b), hsh|
          # Pairs
          hsh[a + b] += 1
        end.tap do |hsh|
          # Individual Elements
          polymer_template.each_char { |c| hsh[c] += 1 }
        end
    end

    def step(pair_counts)
      pair_counts.each_with_object(make_histogram) do |(pair, count), new_counts|
        next if count == 0

        if pair.size == 1
          new_counts[pair] += count
        else
          inserted = pair_insertion_rules[pair]

          p1, p2 = "#{pair[0]}#{inserted}", "#{inserted}#{pair[1]}"
          new_counts[p1] += count
          new_counts[p2] += count
          new_counts[inserted] += count
        end
      end
    end

    def lines = super.to_a

    def polymer_template
      @polymer_template ||= lines.first
    end

    def pair_insertion_rules
      @pair_insertion_rules ||=
        lines.drop(2).each_with_object({}) do |rule_string, rules|
          using, yields = *rule_string.split(' -> ')
          rules[using] = yields
        end
    end
  end
end
