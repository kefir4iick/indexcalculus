require 'prime'
require 'benchmark'
require 'optparse'
require 'csv'
require 'timeout'
require 'etc'

module NumberTheory
  module_function

  def egcd(a, b)
    a = a.to_i
    b = b.to_i
    old_r = a
    r = b
    old_s = 1
    s = 0
    old_t = 0
    t = 1

    until r.zero?
      q = old_r / r
      old_r, r = r, old_r - q * r
      old_s, s = s, old_s - q * s
      old_t, t = t, old_t - q * t
    end

    [old_s, old_t, old_r.abs]
  end

  def mod_inverse(a, m)
    a %= m
    x, _y, g = egcd(a, m)
    return nil unless g == 1

    x % m
  end

  def crt_pair(a1, m1, a2, m2)
    inv = mod_inverse(m1, m2)
    raise ArgumentError, 'CRT moduli must be coprime' if inv.nil?

    t = ((a2 - a1) * inv) % m2
    (a1 + m1 * t) % (m1 * m2)
  end

  def crt(residues)
    x = 0
    m = 1
    residues.each do |ai, mi|
      x = crt_pair(x, m, ai % mi, mi)
      m *= mi
    end
    x
  end

  def prime_power_factorization(n)
    Prime.prime_division(n).map { |q, e| [q, q**e] }
  end

  def primitive_root?(g, p)
    return false unless Prime.prime?(p)

    g %= p
    return false if g <= 1

    n = p - 1
    Prime.prime_division(n).all? do |q, _e|
      g.pow(n / q, p) != 1
    end
  end

  def primitive_root(p)
    raise ArgumentError, 'p must be prime' unless Prime.prime?(p)

    g = 2
    g += 1 until primitive_root?(g, p)
    g
  end

  def random_prime_with_digits(digits)
    raise ArgumentError, 'digits must be positive' if digits < 1

    low = digits == 1 ? 2 : 10**(digits - 1)
    high = 10**digits - 1

    loop do
      candidate = rand(low..high)
      candidate += 1 if candidate.even?
      while candidate <= high
        return candidate if Prime.prime?(candidate)
        candidate += 2
      end
    end
  end
end

class LinearCongruenceSolver
  def initialize(modulus)
    @modulus = modulus
    @prime_powers = NumberTheory.prime_power_factorization(modulus)
  end

  def solve(matrix, rhs, num_vars)
    residues_by_modulus = []

    @prime_powers.each do |prime, prime_power|
      solution = solve_mod_prime_power(matrix, rhs, num_vars, prime, prime_power)
      return nil if solution.nil?

      residues_by_modulus << [solution, prime_power]
    end

    Array.new(num_vars) do |j|
      residues = residues_by_modulus.map { |solution, mod| [solution[j], mod] }
      NumberTheory.crt(residues) % @modulus
    end
  end

  private

  def solve_mod_prime_power(matrix, rhs, num_vars, prime, modulus)
    aug = matrix.each_with_index.map do |row, i|
      row.map { |v| v % modulus } + [rhs[i] % modulus]
    end

    num_rows = aug.length
    pivot_row = 0
    pivot_cols = []

    (0...num_vars).each do |col|
      break if pivot_row >= num_rows

      selected = nil
      (pivot_row...num_rows).each do |r|
        if (aug[r][col] % prime) != 0
          selected = r
          break
        end
      end

      next if selected.nil?

      aug[pivot_row], aug[selected] = aug[selected], aug[pivot_row]

      pivot = aug[pivot_row][col] % modulus
      inv = NumberTheory.mod_inverse(pivot, modulus)
      return nil if inv.nil?

      (col..num_vars).each do |j|
        aug[pivot_row][j] = (aug[pivot_row][j] * inv) % modulus
      end

      (0...num_rows).each do |r|
        next if r == pivot_row

        factor = aug[r][col] % modulus
        next if factor.zero?

        (col..num_vars).each do |j|
          aug[r][j] = (aug[r][j] - factor * aug[pivot_row][j]) % modulus
        end
      end

      pivot_cols << col
      pivot_row += 1
    end

    return nil unless pivot_cols.length == num_vars

    solution = Array.new(num_vars, 0)
    pivot_cols.each_with_index do |col, r|
      solution[col] = aug[r][num_vars] % modulus
    end

    matrix.each_with_index do |row, i|
      lhs = 0
      row.each_with_index { |a, j| lhs += a * solution[j] }
      return nil unless lhs % modulus == rhs[i] % modulus
    end

    solution
  end
end

class IndexCalculusParallel
  attr_reader :alpha, :beta, :p, :n, :factor_base, :last_relation_count

  DEFAULT_EXTRA_RELATIONS = 25
  DEFAULT_MAX_SOLVE_ATTEMPTS = 20
  DEFAULT_BATCH_PER_WORKER = 4

  def initialize(alpha:, beta:, p:, workers: Etc.nprocessors, extra_relations: DEFAULT_EXTRA_RELATIONS, verbose: true)
    @p = Integer(p)
    @alpha = Integer(alpha) % @p
    @beta = Integer(beta) % @p
    @n = @p - 1
    @workers = Integer(workers)
    @extra_relations = extra_relations
    @verbose = verbose
    @factor_base = generate_factor_base
    @last_relation_count = 0

    validate_input!
  end

  def solve
    puts "p = #{@p}" if @verbose
    puts "alpha = #{@alpha}, beta = #{@beta}" if @verbose
    puts "factor base size = #{@factor_base.size}, B = #{factor_base_bound.round(4)}" if @verbose
    puts "mode = parallel, workers = #{@workers}" if @verbose

    target = @factor_base.size + @extra_relations
    matrix = []
    rhs = []

    DEFAULT_MAX_SOLVE_ATTEMPTS.times do
      additional = [target - matrix.length, @extra_relations].max
      puts "collecting relations in parallel: need #{additional} more..." if @verbose

      collect_relations_parallel(additional).each do |exponents, k|
        matrix << exponents
        rhs << k
      end

      @last_relation_count = matrix.length
      puts "trying to solve linear system with #{matrix.length} relations..." if @verbose

      logs = LinearCongruenceSolver.new(@n).solve(matrix, rhs, @factor_base.size)
      if logs && valid_factor_base_logs?(logs)
        puts 'factor base logarithms verified.' if @verbose
        return find_final_log(logs)
      end

      puts 'system was not full-rank/valid; collecting more relations.' if @verbose
      target += @extra_relations
    end

    raise RuntimeError, 'failed to obtain a valid full-rank system; try more relations or a smaller factor base'
  end

  def self.solve_once(alpha:, beta:, p:, workers: Etc.nprocessors, verbose: true)
    solver = new(alpha: alpha, beta: beta, p: p, workers: workers, verbose: verbose)
    result = nil
    elapsed = Benchmark.realtime { result = solver.solve }
    {
      x: result,
      time_sec: elapsed,
      success: alpha.to_i.pow(result, p.to_i) == beta.to_i % p.to_i,
      factor_base_size: solver.factor_base.size,
      relations: solver.last_relation_count
    }
  end

  private

  def validate_input!
    raise ArgumentError, 'p must be prime' unless Prime.prime?(@p)
    raise ArgumentError, 'alpha and beta must be non-zero modulo p' if @alpha.zero? || @beta.zero?
    raise ArgumentError, 'alpha must be a generator of Z_p^*' unless NumberTheory.primitive_root?(@alpha, @p)
    raise ArgumentError, 'workers must be positive' if @workers <= 0
  end

  def factor_base_bound
    return 2.0 if @n <= 3

    log_n = Math.log(@n)
    log_log_n = Math.log(log_n)
    3.38 * Math.exp(0.5 * Math.sqrt(log_n * log_log_n))
  end

  def generate_factor_base
    b = factor_base_bound
    upper = [[b.floor, 2].max, @p - 1].min
    base = Prime.each(upper).select { |q| q < b && q < @p }.to_a
    base.empty? ? [2] : base
  end

  def smooth_exponents(number)
    temp = number
    factors = Array.new(@factor_base.size, 0)

    @factor_base.each_with_index do |prime, idx|
      while (temp % prime).zero?
        factors[idx] += 1
        temp /= prime
      end
      break if temp == 1
    end

    temp == 1 ? factors : nil
  end

  def collect_relations_parallel(count)
    relations = []
    seen = {}
    batch_size = DEFAULT_BATCH_PER_WORKER

    while relations.length < count
      worker_count = [@workers, count - relations.length].min
      readers = []
      pids = []

      worker_count.times do
        reader, writer = IO.pipe
        pid = fork do
          reader.close
          srand(Process.pid ^ Time.now.to_i ^ rand(1 << 30))
          child_relations = collect_relations_child_batch(batch_size)
          Marshal.dump(child_relations, writer)
          writer.flush
          writer.close
          exit! 0
        end

        writer.close
        readers << reader
        pids << pid
      end

      readers.each do |reader|
        Marshal.load(reader).each do |exponents, k|
          key = exponents.join(',')
          next if seen.key?(key)

          seen[key] = true
          relations << [exponents, k]
          print_relation_progress(relations.length, count)
          break if relations.length >= count
        end
        reader.close
      end

      pids.each { |pid| Process.wait(pid) }
    end

    puts if @verbose
    relations.first(count)
  end

  def collect_relations_child_batch(count)
    relations = []
    seen = {}

    until relations.length >= count
      k = rand(1...@n)
      val = @alpha.pow(k, @p)
      exponents = smooth_exponents(val)
      next if exponents.nil?
      next if exponents.all?(&:zero?)

      key = exponents.join(',')
      next if seen.key?(key)

      seen[key] = true
      relations << [exponents, k]
    end

    relations
  end

  def print_relation_progress(current, total)
    return unless @verbose

    print '.' if (current % 5).zero? || current == total
    STDOUT.flush
  end

  def valid_factor_base_logs?(logs)
    @factor_base.each_with_index.all? do |prime, i|
      @alpha.pow(logs[i], @p) == prime % @p
    end
  end

  def find_final_log(logs)
    puts 'searching final smooth representation of beta * alpha^l...' if @verbose

    loop do
      l = rand(1...@n)
      val = (@beta * @alpha.pow(l, @p)) % @p
      exponents = smooth_exponents(val)
      next if exponents.nil?

      sum = 0
      exponents.each_with_index { |di, i| sum += di * logs[i] }
      x = (sum - l) % @n
      return x if @alpha.pow(x, @p) == @beta
    end
  end
end



if $PROGRAM_NAME == __FILE__
    print "alpha: "
    alpha = gets.strip.to_i
    print "beta: "
    beta = gets.strip.to_i
    print "p: "
    p = gets.strip.to_i
    result = IndexCalculusParallel.solve_once(alpha: alpha, beta: beta, p: p, verbose: true)
    puts "x = #{result[:x]}"
    puts "time with parallel: #{format('%.6f', result[:time_sec])} s"
end
