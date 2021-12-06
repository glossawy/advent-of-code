module AdventOfCode
  module Days
    require_relative './days/base_day'
    Dir["#{__dir__}/days/day*.rb"].each { |f| require f }

    InvalidSetup = Class.new(AdventOfCodeError)
    MissingPart = Class.new(AdventOfCodeError)

    DAY_REGEX = /\Aday\d+\z/.freeze

    def self.inputs_for(day)
      AdventOfCode.paths.inputs.join('days', day).then do |day_input_dir|
        raise InvalidSetup, 'Inputs directory not found' unless day_input_dir.exist?
        raise InvalidSetup, "#{day_input_dir} is not a directory" unless day_input_dir.directory?

        day_input_dir.each_child.select(&:file?)
      end
    end

    def self.solver_class(day)
      raise AdventOfCodeError, "#{day} is not the right format: #{DAY_REGEX}" unless DAY_REGEX.match? day

      normalized = day.gsub(/^d/, ?D)

      begin
        self.const_get(normalized)
      rescue NameError
        raise InvalidSetup, "Could not find a matching #{normalized} solver for #{day}"
      end
    end

    def self.solver_for(day, part)
      solver_class(day).then do |solver_factory|
        inputs_for(day).then do |input_files|
          raise MissingPart, "Asked for solution to part #{part} but we only have #{input_files.size} inputs" \
            if part > input_files.size

          solver_factory.new(input_files[part - 1])
        end
      end
    end

    def self.solve_for(day, part)
      solver_for(day, part).send("solve_part#{part}")
    end
  end
end
