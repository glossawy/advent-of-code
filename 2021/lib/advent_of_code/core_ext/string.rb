class String
  def demodulize
    split('::').last
  end

  def snakecase
    gsub(/([A-Z]+)([A-Z][a-z])/, '\1_\2').gsub(/([a-z])([A-Z])/, '\1_\2').downcase
  end

  def titlecase
    return self unless size > 0

    snakecase.split('_').map(&:capitalize).join ' '
  end

  def parse_int!
    Integer(self)
  end
end
