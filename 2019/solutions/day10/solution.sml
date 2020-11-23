(* Standard ML of New Jersey v110.91 *)

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

local
  val stdout = TextIO.stdOut
  val stderr = TextIO.stdErr
  val stdin = TextIO.stdIn
  fun writeOut ending pipe s = (TextIO.output (pipe, s ^ ending); TextIO.flushOut pipe)
in
  val removeNewline = String.translate (fn c => if c = #"\n" then "" else String.str c)
  val print = writeOut "\n" stdout
  val printConcat = print o concat
  val printErr = writeOut "\n" stderr
  val printErrConcat = printErr o concat
  fun readUserInput prompt = (writeOut "" stdout prompt; (Option.map removeNewline o TextIO.inputLine) stdin)

  fun withFile filename f =
    let val fstrm = TextIO.openIn filename
        val out = f fstrm
    in TextIO.closeIn fstrm; out end

  fun readAllLines fstrm =
    case TextIO.inputLine fstrm of
      NONE => []
    | SOME ln => removeNewline ln :: readAllLines fstrm
end

local
  fun extremum (ordering : order) (f : 'a * 'a -> order) (l : 'a list) : 'a option =
    let fun reducer (elem, ex) =
          if f (elem, ex) = ordering
          then elem else ex
    in
      case l of
        [] => NONE
      | h :: t => (SOME o List.foldl reducer h) t
    end
in fun maximum f l = extremum GREATER f l
   fun minimum f l = extremum LESS f l
end

fun id x = x
fun curry f x y = f (x, y)

fun realEquals (a, b) = Real.abs (b - a) < 0.00001
fun realCompare (a, b) = if realEquals (a, b) then EQUAL else Real.compare (a, b)
fun rmod (a, b) =
  let val r = Real.rem (a, b)
  in if realCompare (r, 0.0) = LESS then r + b else r end

fun qsortBy cmp [] = []
  | qsortBy cmp (x :: xs) =
      let val (left, right) = List.partition (fn y => cmp (y, x) = LESS) xs
      in qsortBy cmp left @ [x] @ qsortBy cmp right end

fun takeWhile _ [] = []
  | takeWhile f (x :: xs) = if f x then x :: takeWhile f xs else []

fun strides _ [] = []
  | strides eq xs =
      let val stride = takeWhile (curry eq $ hd xs) xs
      in stride :: strides eq (List.drop (xs, length stride)) end

local fun indexHelp _ [] = []
        | indexHelp i (x :: xs) = (x, i) :: indexHelp (i + 1) xs
in
  fun withIndex xs = indexHelp 0 xs
end


signature MAP =
sig
  exception NotFound

  type key_t
  type 'v map

  val empty : 'v map

  val get : key_t -> 'v map -> 'v
  val insert : key_t -> 'v -> 'v map -> 'v map
  val insertOrUpdate : key_t -> ('v option -> 'v) -> 'v map -> 'v map
  val length : 'v map -> int
  val toList : 'v map -> (key_t * 'v) list
end

signature KEY =
sig
  type key
  val equal : key * key -> bool
end

functor MapFn (K : KEY) : MAP =
struct
  exception NotFound

  type key_t = K.key
  type 'v map = (key_t * 'v) list

  val empty = []
  fun get k m =
    Option.valOf o Option.map (#2) o List.find (fn (k', _) => K.equal (k, k')) $ m
    handle Option.Option => raise NotFound

  fun insertOrUpdate k f m =
    case m of
      [] => [(k, f NONE)]
    | ((k', v') :: t) =>
        if K.equal (k, k') then (k, f $ SOME v') :: t
        else (k', v') :: insertOrUpdate k f t

  fun insert k v m = insertOrUpdate k (fn _ => v) m
  fun length m = List.length m

  fun toList m = m
end

structure Map = MapFn (struct type key = real fun equal (k, k') = Real.compare (k, k') = EQUAL end)
type 'v realmap = 'v Map.map

structure Vect2 =
struct
  datatype t = Vect of real * real

  fun make (x, y) = Vect (x, y)
  fun makeInt (x, y) = make (Real.fromInt x, Real.fromInt y)
  fun equal (Vect (x, y), Vect (x', y')) = realEquals (x, x') andalso realEquals (y, y')
  fun toString (Vect (x, y)) = concat ["(", Real.toString x, ", ", Real.toString y, ")"]

  (* Zero and Ordinal Vectors *)
  val zero : t = makeInt (0, 0)

  fun add (Vect (vx, vy)) (Vect (wx, wy)) = make (vx + wx, vy + wy)
  fun sub (Vect (vx, vy)) (Vect (wx, wy)) = make (vx - wx, vy - wy)

  fun magnitude (Vect (x, y)) = Math.sqrt(x*x + y*y)
  fun distance v v' = magnitude $ sub v v'

  fun angleBetween u v =
    let val (Vect (x, y)) = sub u v
    in Math.atan2 (y, x) end

  fun isBetween w (u, v) =
    let val sum = distance w u + distance w v
        val direct = distance u v
    in realEquals (direct, sum) end
end
val vect2 = Vect2.make
fun intVect2 (x, y) = vect2 (Real.fromInt x, Real.fromInt y)

structure AsteroidMap =
struct
  exception UnknownToken of char

  type asteroid = Vect2.t
  type map = asteroid list

  fun toString (asteroid : asteroid) =
    concat ["Asteroid ", Vect2.toString asteroid]

  fun visibleAsteroids map =
    let fun visibleFrom a =
          let val others = List.filter (not o (curry Vect2.equal) a) map
              val angles = List.map (Vect2.angleBetween a) others
              val angleSet = List.foldl (fn (theta, m) => Map.insert theta theta m) Map.empty angles
          in length angleSet end
    in List.map (fn a => (a, visibleFrom a)) map end

  fun annihilationOrder amap from =
    let val others = List.filter (not o (curry Vect2.equal from)) amap
        fun calculateFor a =
          let val dist = Vect2.distance from a
              val angleBetween = Vect2.angleBetween a from
              val angleBetween = rmod (angleBetween + (Math.pi / 2.0), 2.0 * Math.pi)
          in (a, dist, angleBetween) end

        fun compareAngles ((_, _, a1), (_, _, a2)) = realCompare (a1, a2)
        fun compareDistances ((_, d1, _), (_, d2, _)) = realCompare (d1, d2)

        (* Sort by angles, then by distances *)
        val derived = qsortBy compareAngles $ map calculateFor others
        val derived = strides (fn (a, b) => realEquals (#3 a, #3 b)) derived
        val derived = map (qsortBy compareDistances) derived

        fun roundRobin (xs, []) = (xs, [])
          | roundRobin (xs, [] :: xss) = roundRobin (xs, xss)
          | roundRobin (res, (x :: xs) :: xss) =
              let val (res', xss') = roundRobin (res, xss)
              in (x :: res', xs :: xss') end

        fun deplete xss =
          let val (r, rest) = roundRobin ([], xss)
          in
            case rest of
              [] => r
            | _ => r @ deplete rest
          end
    in
      (* Visit each group in round robin order until exhausted *)
      deplete derived
    end

  fun fromTokens (nrows, ncols) tokens =
    let fun toAsteroid (tok, pos) =
          case tok of
            #"#" => SOME $ vect2 (Real.fromInt $ pos mod ncols, Real.fromInt $ pos div nrows)
          | #"." => NONE
          | _ => raise UnknownToken tok

        val asteroidOpts = map toAsteroid $ withIndex tokens
    in
      map Option.valOf o List.filter Option.isSome $ asteroidOpts
    end
end

fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day10.in")
      val rawInput = withFile filename readAllLines
      val (nrows, ncols) = (length rawInput, String.size o hd $ rawInput)
      val tokens = String.explode o concat $ rawInput
  in f { size = (nrows, ncols), tokens = tokens } end

fun part1 fOpt = withInput fOpt (fn { size = size, tokens = toks } => (
  let val amap = AsteroidMap.fromTokens size toks
      val visibilities = AsteroidMap.visibleAsteroids amap
  in maximum (fn ((_, a), (_, b)) => Int.compare (a,b)) $ visibilities end
))

fun part2 fOpt = withInput fOpt (fn { size = size, tokens = toks } => (
  let val amap = AsteroidMap.fromTokens size toks
      val laserPosition = intVect2 (14, 17) (* From part 1 *)
      val annihilations = Vector.fromList $ AsteroidMap.annihilationOrder amap laserPosition
  in Vector.sub (annihilations, 199) end
))

fun main ((name, args) : string * string list) =
  let fun exec "part1" x =
            let val (asteroid, count) = Option.valOf o part1 $ x
            in printConcat [AsteroidMap.toString asteroid, " : ", Int.toString count, " visible"] end
        | exec "part2" x =
            let val (asteroid as (Vect2.Vect (x, y)), _, _) = part2 x
                val answer = Real.toString $ x * 100.0 + y
            in printConcat ["200th Destroyed: ", AsteroidMap.toString asteroid, " => ", answer] end
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, " part [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
