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

type intinf = IntInf.int

(* Basic useful functions *)
fun id x = x
fun const k = (fn _ => k)
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y
fun flip f (y, x) = f (x, y)

val forceParseInt = Option.valOf o Int.fromString
val forceParseIntInf = Option.valOf o IntInf.fromString

fun isListPrefix [] ys = true
  | isListPrefix xs [] = false
  | isListPrefix (x :: xs) (y :: ys) = if x = y then isListPrefix xs ys else false

fun gcd (a, 0) = a
  | gcd (a, b) = if a < b then gcd (b, a)
                 else gcd (b, a mod b)

fun lcm (a, b) = (a * b) div (gcd (a, b))

fun flatten xs = List.foldl op@ [] xs

structure StringUtil =
struct
  fun indexOf ss s =
    let fun find i cc [] = NONE
          | find i [] c  = SOME 0
          | find i cc c  = if isListPrefix cc c then SOME i else find (i + 1) cc (tl c)
    in find 0 $ String.explode ss $ String.explode s end

  fun split ss s =
    case indexOf ss s of
      NONE => [s]
    | SOME idx =>
        let val element = String.extract (s, 0, SOME idx)
            val rest = String.extract (s, idx + String.size ss, NONE)
        in element :: split ss rest end

  fun delete ss = String.translate (fn c => if Char.contains ss c then "" else String.str c)

  fun trimWS s =
    let fun helper provisional [] = []
          | helper provisional (c :: cs) =
              if c = #" " then helper (c :: provisional) cs
              else provisional @ (c :: helper [] cs)
    in String.implode o helper [] $ String.explode s end
end

structure StringMap = BinaryMapFn (
  struct
    type ord_key = string
    val compare = String.compare
  end
)

fun insertOrUpdate smap k v f =
    case StringMap.find (smap, k) of
      NONE => StringMap.insert (smap, k, v)
    | SOME v' => StringMap.insert (smap, k, f (v', v))

structure Chemistry =
struct
  structure M = StringMap

  type quantity = intinf
  type element = string

  datatype reaction = Rule of (quantity * element) list * (quantity * element)

  (* being lazy *)
  structure TopoSort =
  struct
    type edge = element * element

    fun isOutput x (_, out) = String.compare (x, out) = EQUAL
    fun isInput  x (inp, _) = String.compare (x, inp) = EQUAL

    fun toEdges [] =[]
      | toEdges ((Rule (inputs, (q, e))) :: rs) =
          let fun mkEdge (_, eIn) = (eIn, e)
          in map mkEdge inputs @ toEdges rs end

    fun sort rs root =
      let fun excludeInputs [] e' = true
            | excludeInputs (e :: es) (x as (inp, _)) =
                (not o isInput inp) e andalso excludeInputs es x
          fun helper _ [] result = result
            | helper edges (h::hs) result =
                let val (incoming, edges') = List.partition (isOutput h) edges
                    val next = map (#1) o List.filter (excludeInputs edges') $ incoming
                    val stack' = hs @ next
                in helper edges' stack' (h :: result) end
      in rev $ helper (toEdges rs) [root] [] end
  end

  fun requirementsMap [] = M.empty
    | requirementsMap ((Rule (reqs, (q,e ))) :: rs) =
        StringMap.insert (requirementsMap rs, e, (q, reqs))

  fun resourcesNeeded2 reactions (q, e) =
    let val requirements = requirementsMap reactions
        fun determine (elem, needed) =
          case M.find (requirements, elem) of
            NONE => needed
          | SOME (q_produced, inputs) =>
              let val SOME q_needed = M.find (needed, elem)
                  val scale = (q_needed div q_produced) + (Int.toLarge o IntInf.sign) (q_needed mod q_produced)
                  val needed' = insertOrUpdate needed elem q_needed op+
                  fun addNeeded ((q, e), m) = insertOrUpdate m e (scale * q) op+
              in List.foldl addNeeded needed' inputs end

        val initialMap = M.insert (M.empty, e, q)
        val _ = print $ String.concatWith " -> " (TopoSort.sort reactions e)
    in List.foldl determine initialMap (TopoSort.sort reactions e)  end

  fun resourcesNeeded reactions (q, e) =
    let val requirements = requirementsMap reactions
        fun determine (elem, needed) =
          case M.find (requirements, elem) of
            NONE => needed
          | SOME (q_produced, inputs) =>
              let val SOME q_needed = M.find (needed, elem)
                  val scale = (q_needed div q_produced) + (Int.toLarge o IntInf.sign) (q_needed mod q_produced)
                  val needed' = insertOrUpdate needed elem q_needed op+
                  fun addNeeded ((q, e), m) = insertOrUpdate m e (scale * q) op+
              in List.foldl addNeeded needed' inputs end

        val initialMap = M.insert (M.empty, e, q)
        val _ = print $ String.concatWith " -> " (TopoSort.sort reactions e)
    in List.foldl determine initialMap (TopoSort.sort reactions e)  end

  fun oreNeeded reactions (q, e) =
    Option.getOpt (M.find (resourcesNeeded reactions (q, e), "ORE"), Int.toLarge 0)

  fun parseElement (s : string) : (quantity * element) =
    let val [quant, name] = String.tokens (curry op= #" ") s
    in (forceParseIntInf quant, name) end

  fun parseReaction (s : string) : reaction =
    let val [prereqs, result] = StringUtil.split " => " s
        val tokens = map StringUtil.trimWS o String.tokens (curry op= #",") $ prereqs
        val result = StringUtil.trimWS result
    in
      Rule (map parseElement tokens, parseElement result)
    end
end

fun withInputs fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day14.in")
      val rawInput = withFile filename readAllLines
  in f $ map Chemistry.parseReaction rawInput end


(* The joys of topological sorts *)
fun part1 fOpt = withInputs fOpt (fn reactions =>
  Chemistry.oreNeeded reactions (Int.toLarge 1, "FUEL")
)

(* Binary search for fuel amount from ore *)
fun part2 fOpt = withInputs fOpt (fn reactions => (
  let val orePerFuel = Chemistry.oreNeeded reactions (Int.toLarge 1, "FUEL")
      val oreAvail = Option.valOf o IntInf.fromString $ "1000000000000"
      val estLow = oreAvail div orePerFuel
      val estHigh = estLow * 2

      fun search (min : IntInf.int) (max : IntInf.int) =
        if abs(max - min) <= 1 then min
        else
          let val fuelGuess = (min + max) div 2
              val oreForFuel = Chemistry.oreNeeded reactions (fuelGuess, "FUEL")
          in if oreForFuel > oreAvail then search min fuelGuess else search fuelGuess max end
  in search estLow estHigh end
))

fun main (name, args) =
  let fun exec "part1" x = print o IntInf.toString $ part1 x
        | exec "part2" x = print o IntInf.toString $ part2 x
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, " part [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
