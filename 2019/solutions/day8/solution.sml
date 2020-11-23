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
fun uncurry f (x, y) = f x y
fun flip f (x, y) = f (y, x)

val forceParseInt = Option.valOf o Int.fromString

signature MAP =
sig
  exception NotFound

  type key_t
  type 'v map

  val empty : 'v map

  val get : key_t -> 'v map -> 'v
  val getDefault : 'v -> key_t -> 'v map -> 'v
  val insert : key_t -> 'v -> 'v map -> 'v map
  val insertOrUpdate : key_t -> ('v option -> 'v) -> 'v map -> 'v map
  val merge : 'v map * 'v map -> 'v map
  val mergeWith : ('v * 'v -> 'v) -> 'v map * 'v map -> 'v map
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
  exception NotFound

  type key_t = K.key
  type 'v map = (key_t * 'v) list

  val empty = []
  fun get k m =
    Option.valOf o Option.map (#2) o List.find (fn (k', _) => K.equal (k, k')) $ m
    handle Option.Option => raise NotFound

  fun getDefault default k m = get k m handle NotFound => default

  fun insertOrUpdate k f m =
    case m of
      [] => [(k, f NONE)]
    | ((k', v') :: t) =>
        if K.equal (k, k') then (k, f $ SOME v') :: t
        else (k', v') :: insertOrUpdate k f t

  fun insert k v m = insertOrUpdate k (fn _ => v) m
  fun keys m = #1 o ListPair.unzip $ m
  fun values m = #2 o ListPair.unzip $ m

  fun mergeWith f (m1, m2) =
    let val pairs = m1 @ m2
        fun mergeEntry ((k, v), m) =
          insertOrUpdate k (fn NONE => v
                             | SOME v' => f (v', v)) m
    in List.foldl mergeEntry empty pairs end

  fun merge (m1, m2) = mergeWith (#2) (m1, m2)

  fun toList m = m
end

structure IntKey =
struct
  type key = int
  fun equal (k, k') = Int.compare (k, k') = EQUAL
end
structure IntMap = MapFn (IntKey)
type 'v intmap = 'v IntMap.map

fun groups n [] = []
  | groups n xs =
  let fun groupHelper _ [] = ([], [])
        | groupHelper 0 ys = ([], ys)
        | groupHelper m (y :: ys) =
            let val (grp, remaining) = groupHelper (m - 1) ys
            in (y :: grp, remaining) end
  in
    if n <= 0 then []
    else let val (g, xs') = groupHelper n xs
         in g :: groups n xs' end
  end

fun countInts xs =
  let fun initOrIncrement NONE = 1
        | initOrIncrement (SOME n) = n + 1
      fun reducer (i, histogram) =
        IntMap.insertOrUpdate i initOrIncrement histogram
  in List.foldl reducer IntMap.empty xs end


structure Image =
struct
  exception UnknownPixel of int

  type imgsize = int * int
  type layer = int list list

  datatype image = Image of { size : imgsize, layers : layer list }

  fun layerHistograms (Image img) =
    let fun addHistograms (h1, h2) =
          IntMap.mergeWith op+ (h1, h2)
        fun layerHistogram layer = List.foldl addHistograms IntMap.empty $ List.map countInts layer
        val rowHistograms = List.map (layerHistogram) $ #layers img
    in rowHistograms end

  local fun addLayers ((nr, nc) : imgsize) ((l1, l2) : layer * layer) : layer =
          let fun addPixels (top, bot) =
                case (top, bot) of
                  (0, _) => 0
                | (1, _) => 1
                | (2, n) => n
                | (n, _) => raise UnknownPixel n

              val rows = ListPair.map (ListPair.map addPixels) (l1, l2)
          in
            rows
          end
  in
    fun decode (Image img) =
      let val (top :: rest) = #layers img
          val decoded = List.foldl (flip $ addLayers (#size img)) top rest
      in
        Image { size = #size img, layers = [decoded] }
      end
  end

  fun makeImage ((ncols, nrows) : int * int)  (xs : int list) : image =
    let val rows = groups ncols xs
        fun takeLayers [] = []
          | takeLayers rs = List.take (rs, nrows) :: takeLayers (List.drop (rs, nrows))
    in Image { size = (ncols, nrows), layers = takeLayers rows } end

  fun toString img =
    let val (Image { layers = [layer], ... }) = decode img
        fun rowsToString [] = []
          | rowsToString (r :: rs) = (concat o map Int.toString) r ^ "\n" :: rowsToString rs
    in concat $ rowsToString layer end
end


fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day8.in")
      val rawInput = withFile filename (removeNewline o Option.valOf o TextIO.inputLine)
      val tokenized = map (forceParseInt o String.str) o String.explode $ rawInput
  in f tokenized end

fun solvePart1 fOpt = withInput fOpt (fn values => (
  let fun layerCountCmp (l1, l2) =
        Int.compare (IntMap.getDefault 0 0 l1, IntMap.getDefault 0 0 l2)

      val image = Image.makeImage (25, 6) values
      val layerCounts = Image.layerHistograms image
      val fewestZeroLayer = Option.valOf o minimum layerCountCmp $ layerCounts
      val numOnes = IntMap.getDefault 0 1 fewestZeroLayer
      val numTwos = IntMap.getDefault 0 2 fewestZeroLayer
  in
    {
      image = image,
      layerCounts = layerCounts,
      chosen = fewestZeroLayer,
      result = numOnes * numTwos
    }
  end
))

fun solvePart2 fOpt = withInput fOpt (fn values => (
  let val image = Image.makeImage (25, 6) values
  in print $ Image.toString image; image end
))

fun main (name, args) =
  let fun exec "part1" x =
          let val { image, layerCounts, chosen, result } = solvePart1 x
          in
            print "Additional debug info available in repl.\n";
            printConcat ["Result: ", Int.toString result];
            print "Image:";
            print $ Image.toString image
          end
        | exec "part2" x = ignore $ solvePart2 x
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, "<part1|part2> [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
