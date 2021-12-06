module AdventOfCode::Days
  class Day6 < BaseDay
    TIMER_RESET_VALUE = 6
    INITIAL_TIMER_VALUE = 8

    def solve_part1 = simulate(80)

    # Thankfully ruby doesn't need special big int handling or something like IntInf ^-^
    def solve_part2 = simulate(256)

    private

    def simulate(ndays)
      timer_counts = initial_fish_timers.group_by(&:itself).transform_values(&:size)
      timer_counts.default_proc = proc { |h, k| h[k] = 0 }

      days_left = ndays
      total_fish = timer_counts.values.sum

      loop do
        timer_key = timer_counts.keys.min
        wait_days = timer_key + 1

        break if days_left < wait_days

        days_left -= wait_days
        expired_fish = timer_counts.delete(timer_key)

        # Decrease other timers
        timer_counts.transform_keys! { |timer| timer - wait_days }

        # Reset birthing fish
        timer_counts[TIMER_RESET_VALUE] += expired_fish

        # Add born fish
        timer_counts[INITIAL_TIMER_VALUE] += expired_fish

        # Increase count of fish by fish born
        total_fish += expired_fish
      end

      solution(
        total_fish,
        simulated_for: ndays,
        days_left: days_left,
        initial_timers: initial_fish_timers,
        final_counts: timer_counts
      )
    end

    def initial_fish_timers
      @initial_fish_timers ||= lines.flat_map { |line| line.split(',').map(&:parse_int!) }.to_a
    end
  end
end
