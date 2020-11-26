(* Standard ML of New Jersey v110.91 *)

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

local fun writeOut pipe s = TextIO.output (pipe, s ^ "\n")
in val print = writeOut TextIO.stdOut
   val printConcat = print o concat
   val printErr = writeOut TextIO.stdErr
   val printErrConcat = printErr o concat
end

(* Basic useful functions *)
fun id x = x
fun const k = (fn _ => k)
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y

val forceParseInt = Option.valOf o Int.fromString

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

(* List helpers *)
fun adjacentPairs [] = []
  | adjacentPairs xs = ListPair.zip (xs, tl xs)

fun flatten xs = List.foldr op@ [] xs

(* Main body of solution *)

exception UnknownToken of char * int
exception IntersectionIsNotIntersection

(*
  A basic implementation of a 2-dimensional vector, though this particular
  implementation is specialized to grids and operations where we anticipate
  working solely with manhattan distances.

  Basically, distance here is *always* manhattan distance and *never* euclidean
  distance. For our purposes there are no operations where this will cause
  issues and is one of many places where assumptions are made.
*)
structure Vect2 =
struct
  datatype t = Vect of int * int

  fun make (x, y) = Vect (x, y)
  fun equal (Vect (x, y), Vect (x', y')) = x = x' andalso y = y'
  fun toString (Vect (x, y)) = concat ["Vect(", Int.toString x, ", ", Int.toString y, ")"]

  (* Zero and Ordinal Vectors *)
  val zero : t = make (0, 0)
  val north = make (0, 1) and south = make (0, ~1)
  and  east = make (1, 0) and  west = make (~1, 0)

  (*
    Typical 2D Vector operations with the usual definition for cross product.

    Note: (scale_inv a v) is equivalent to (1//a) * v  where // is integer
          division. This is to avoid complexity from introducing non-int
          numeric types.

    Using scale_inv, we are assuming intersections happen at integer coordinates.
  *)
  fun scale scalar (Vect (x, y)) = make (x * scalar, y * scalar)
  fun scale_inv inv_scalar (Vect (x, y)) = make (x div inv_scalar, y div inv_scalar)
  fun add (Vect (vx, vy)) (Vect (wx, wy)) = make (vx + wx, vy + wy)
  fun sub v1 v2 = add v1 $ scale ~1 v2
  fun dot (Vect (vx, vy)) (Vect (wx, wy)) = vx * wx + vy * wy
  fun cross (Vect (vx, vy)) (Vect (wx, wy))= vx * wy - vy * wx

  (*
    Reminder: all based on manhattan distance
  *)
  fun magnitude (Vect (x, y)) = abs(x) + abs(y)
  fun distance v v' = magnitude $ sub v v'
  fun norm v = scale_inv $ magnitude v $ v

  (* Projection of v onto u or (v . norm(u)) * norm(u) *)
  fun project v u =
    let val norm_u = norm u
        val scalar = dot v norm_u
    in scale scalar norm_u end

  fun isBetween w (u, v) = distance w u + distance w v = distance u v
end

(*
  A wire is a sequence of 2D Vectors start from (0, 0).

  Parsing is special by taking in a list of *movement* vectors (deltas)
  which describe how to create line segments starting from (0, 0).
*)
structure Wire =
struct
  type t = Vect2.t list

  fun length (wire : t) =
    let val distfn = uncurry Vect2.distance
        val segmentLengths = map distfn $ adjacentPairs wire
    in List.foldl op+ 0 segmentLengths end

  (* Find the number of steps necessary to encounter p, if at all encountered *)
  fun distanceTo (wire : t) (p : Vect2.t) =
    let val segments = adjacentPairs wire
        val seed = (NONE, 0)
        fun reducer (seg as (u, v), acc as (status, lengthSoFar)) =
          case status of
            SOME v => acc
          | NONE =>
            if Vect2.isBetween p seg
            then (SOME $ lengthSoFar + Vect2.distance u p, lengthSoFar)
            else (NONE, lengthSoFar + Vect2.distance u v)
        val (opt, _) = List.foldl reducer seed segments
    in opt end

  (* Enumerating intersections between two wires *)
  local
    (* Reminder: we are on a grid! Intersections ought to be orthogonal. *)
    (* Assuming no intersections at corners and
       Lines only intersect at 0 or 1 points for any pair of lines
    *)
    fun segmentIntersection (sA, tA) (sB, tB) =
      let val sA_to_sB = Vect2.sub sB sA
          val sA_to_tB = Vect2.sub tB sA
          val sA_to_tA = Vect2.sub tA sA
      in
        (*
          Check that sB and tA are on opposite sides of tA - sA.
          Based on properties of the 2D cross product.
        *)

        (*
          Assuming that the cross product will never be 0, meaning the
          end point of a line segment *is* the intersection.
        *)
        if Int.sameSign (Vect2.cross sA_to_tA sA_to_sB, Vect2.cross sA_to_tA sA_to_tB)
        then NONE
        else
          (* Since the lines are orthogonal, projection is the intersection.
             Probably unnecesary. *)
          let val projection = Vect2.project sA_to_sB sA_to_tA
              val adjusted = Vect2.add sA projection
          in
              if Vect2.isBetween adjusted (sA, tA)
              then SOME adjusted else NONE
          end
      end
  in
    (*
      Cartesian product makes this algorithm O(N*M)
      where N and M are the number of steps for each wire.
    *)
    fun intersections (wireA : t) (wireB : t) : Vect2.t list =
      let val segmentsA = adjacentPairs $ List.drop (wireA, 0)
          val segmentsB = adjacentPairs $ List.drop (wireB, 0)
          fun mapper segment =
            map $ segmentIntersection segment $ segmentsB
      in
        map Option.valOf o List.filter Option.isSome o flatten o map mapper $ segmentsA
      end
  end

  local
    fun parseInternal vects prev =
      case vects of
        [] => []
      | dv :: dvs =>
          let val v' = Vect2.add dv prev
          in v' :: parseInternal dvs v' end
    val start = Vect2.zero
  in
    fun parse vects = start :: parseInternal vects start
  end
end

(* Now to tie everything together! *)

fun parseToWire line =
  let val isDelimiter = curry op= #","
      val raw = String.tokens isDelimiter line

      fun parseSingleToken s =
        let val direction = String.sub (s, 0)
            val magnitude = forceParseInt $ String.extract (s, 1, NONE)
            val unit =
              case direction of
                #"U" => Vect2.north
              | #"D" => Vect2.south
              | #"L" => Vect2.west
              | #"R" => Vect2.east
              | _ => raise UnknownToken (direction, magnitude)
        in Vect2.scale magnitude unit end
  in Wire.parse o map parseSingleToken $ raw end

fun withInputs filenameOpt f =
  let val fstrm = TextIO.openIn $ Option.getOpt (filenameOpt, "../../inputs/day3.in")
      fun process readResult =
        case readResult of
          SOME ln => parseToWire ln :: (process $ TextIO.inputLine fstrm)
        | NONE => []

      val (w1 :: w2 :: _) = process $ TextIO.inputLine fstrm
      val intersections = Wire.intersections w1 w2
  in
     f (w1, w2) intersections
  end

fun solvePart1 fOpt =
  let fun findClosest _ = Option.valOf o minimum Int.compare o map Vect2.magnitude
  in withInputs fOpt findClosest end

fun solvePart2 fOpt =
  let fun findMinStep (w1, w2) =
        let fun cost p =
              case (Wire.distanceTo w1 p, Wire.distanceTo w2 p) of
                (SOME c1, SOME c2) => c1 + c2
              | _ => raise IntersectionIsNotIntersection  (* Being Lazy *)
        in Option.valOf o minimum Int.compare o map cost end
  in withInputs fOpt findMinStep end

fun main (name, args) =
  let fun exec "part1" = print o Int.toString o solvePart1
        | exec "part2" = print o Int.toString o solvePart2
        | exec s = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, "<part1|part2> [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
