local
  val stdout = TextIO.stdOut
  val stderr = TextIO.stdErr
  val stdin = TextIO.stdIn
  fun writeOut ending pipe s = (TextIO.output (pipe, s ^ ending); TextIO.flushOut pipe)
in
  val print = writeOut "\n" stdout
  val printConcat = print o concat
  val printErr = writeOut "\n" stderr
  val printErrConcat = printErr o concat
  fun readUserInput prompt = (writeOut "" stdout prompt; TextIO.inputLine stdin)

  fun withFile filename f =
    let val fstrm = TextIO.openIn filename
        val out = f fstrm
    in TextIO.closeIn fstrm; out end

  fun readAllLines fstream =
    case TextIO.inputLine fstream of
      NONE => []
    | SOME ln => String.translate (fn c => if c = #"\n" then "" else String.str c) ln :: readAllLines fstream
end

(* Basic useful functions *)
fun id x = x
fun const k = (fn _ => k)
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y
fun flip f (x, y) = f (y, x)

val forceParseInt = Option.valOf o Int.fromString

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

signature QUEUE =
sig
  exception Pop
  type 'a queue

  val empty : 'a queue
  val isEmpty : 'a queue -> bool
  val push : 'a -> 'a queue -> 'a queue
  val pop : 'a queue -> ('a * 'a queue)
end

structure Queue :> QUEUE =
struct
  exception Pop
  type 'a queue = 'a list * 'a list

  val empty = ([], [])
  fun isEmpty ([], []) = true
    | isEmpty _ = false

  fun push e (s1, s2) = (s1, e :: s2)
  fun pop ([], []) = raise Pop
    | pop ([], s2) = pop (rev s2, [])
    | pop (h :: t, s2) = (h, (t, s2))
end
type 'a queue = 'a Queue.queue

signature MAP =
sig
  type key_t
  type 'v map

  val empty : 'v map

  val get : key_t -> 'v map -> 'v option
  val insert : key_t -> 'v -> 'v map -> 'v map
  val insertOrUpdate : key_t -> ('v option -> 'v) -> 'v map -> 'v map
  val contains : key_t -> 'v map -> bool

  val keys : 'v map -> key_t list
  val values : 'v map -> 'v list
  val toList : 'v map -> (key_t * 'v) list
end

signature KEY =
sig
  type key
  val equal : key * key -> bool
end

functor MapFn (K : KEY) : MAP =
struct
  type key_t = K.key
  type 'v map = (key_t * 'v) list

  val empty = []
  fun get k m = Option.map (#2) o List.find (fn (k', _) => K.equal (k, k')) $ m
  fun contains k m = Option.isSome o get k $ m

  fun insertOrUpdate k f m =
    case m of
      [] => [(k, f NONE)]
    | ((k', v') :: t) =>
        if K.equal (k, k') then (k, f $ SOME v') :: t
        else (k', v') :: insertOrUpdate k f t

  fun insert k v m = insertOrUpdate k (fn _ => v) m
  fun keys m = #1 o ListPair.unzip $ m
  fun values m = #2 o ListPair.unzip $ m
  fun toList m = m
end

structure StringKey =
struct
  type key = string
  fun equal (k, k') = String.compare (k, k') = EQUAL
end
structure Map = MapFn (StringKey)
type 'v map = 'v Map.map

signature GRAPH =
sig
  type graph

  val orbitChecksum : string -> graph -> int
  val leapsBetween : string -> string -> graph -> int option
  val fromEdges : (string * string) list -> graph
end

structure Graph :> GRAPH =
struct
  type edge = string * string
  type graph = string list map * string list map

  fun orbitNeighborsOf s ((g, _) : graph) =
    Option.getOpt (Map.get s g, [])

  fun allNeighborsOf s ((f, b) : graph) =
    let val naive = Option.getOpt (Map.get s f, []) @ Option.getOpt (Map.get s b, [])
        val pseudoset = List.foldl (fn (s, m) => Map.insert s s m) Map.empty naive
    in Map.keys pseudoset end

  fun orbitChecksum start g  =
    let fun helper d s =
          let val neighborDepths = List.map (helper (d + 1)) $ orbitNeighborsOf s g
              val sumNeighbors = List.foldl op+ 0 neighborDepths
          in d + sumNeighbors end
    in helper 0 start end

  fun leapsBetween s t (f, b) =
    let val q : string list queue ref = ref $ Queue.push [s] Queue.empty
        val visited : string map ref = ref Map.empty
        fun isTarget x = String.compare (x, t) = EQUAL
        fun bfs () =
          if Queue.isEmpty (! q)
          then NONE
          else
            let val (path, q') = Queue.pop (! q)
                val prev = hd path
            in
              if isTarget prev then SOME path
              else
                let val vset = !visited
                    val neighbors = List.filter (fn n => not $ Map.contains n vset) $ allNeighborsOf prev (f, b)
                    val vset' = List.foldl (fn (n, v) => Map.insert n n v) vset neighbors
                    val q'' = List.foldl (fn (p, q) => Queue.push (p :: path) q) q' $ neighbors
                in visited := vset'; q := q''; bfs () end
            end
    in Option.map ((curry o flip) op- 3 o length) $ bfs () end

  fun fromEdges es  =
    let fun populate ((s, t), (f, b)) =
          let val f' = Map.insertOrUpdate s (fn NONE => [t]
                                 | SOME ts => t :: ts) f
              val b' = Map.insertOrUpdate t (fn NONE => [s]
                                              | SOME ss => s :: ss) b
          in (f', b') end
    in List.foldl populate (Map.empty, Map.empty) es end
end
type graph = Graph.graph


fun withInputs fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day6.in")
      val rawInput = withFile filename readAllLines
      val isDelim = curry op= #")"
      fun toEdge raw =
        let val (s :: t :: _) = String.tokens isDelim raw
        in (s, t) end
      val edges = List.map toEdge rawInput
      val graph = Graph.fromEdges edges
  in f graph end

fun solvePart1 fOpt = withInputs fOpt $ Graph.orbitChecksum "COM"
fun solvePart2 fOpt = withInputs fOpt $ Graph.leapsBetween "YOU" "SAN"

fun main (name, args) =
  let fun exec "part1" = print o Int.toString o solvePart1
        | exec "part2" = print o Int.toString o Option.valOf o solvePart2
        | exec s = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, "<part1|part2> [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
