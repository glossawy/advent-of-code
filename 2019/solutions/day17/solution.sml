(* Standard ML of New Jersey v110.91 *)

structure Cont = SMLofNJ.Cont
type 'a cont = 'a Cont.cont
val callcc = Cont.callcc
val throw = Cont.throw

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

local
  val stdout = TextIO.stdOut
  val stderr = TextIO.stdErr
  val stdin = TextIO.stdIn
  val removeNewline = String.translate (fn c => if c = #"\n" then "" else String.str c)
  fun writeOut ending pipe s = (TextIO.output (pipe, s ^ ending); TextIO.flushOut pipe)
in
  val write = writeOut "" stdout
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

type intinf = IntInf.int

fun id x = x
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y

val forceParseInt = Option.valOf o Int.fromString
val forceParseIntInf = Option.valOf o IntInf.fromString

fun pairToString f g (a, b) = concat ["(", f a, ", ", g b, ")"]
val intPairToString = pairToString Int.toString Int.toString

val explodeInt = map (forceParseInt o Char.toString) o String.explode o Int.toString

fun lpad n p xs = if length xs < n then p :: lpad (n - 1) p xs else xs

fun enumerate xs =
  let fun helper i [] = []
        | helper i (x :: xs) = (x, i) :: helper (i + 1) xs
  in helper 0 xs end

fun takeWhile _ [] = []
  | takeWhile f (x :: xs) = if f x then x :: takeWhile f xs else []

fun strides _ [] = []
  | strides eq xs =
      let val stride = takeWhile (curry eq $ hd xs) xs
      in stride :: strides eq (List.drop (xs, length stride)) end


structure ListUtil =
struct
  fun isPrefix [] ys = true
    | isPrefix xs [] = false
    | isPrefix (x :: xs) (y :: ys) = if x = y then isPrefix xs ys else false

  fun extract (xs, n, NONE) = List.drop (xs, n)
    | extract (xs, n, SOME l) = List.take (List.drop (xs, n), l)

  fun indexOf xss xs =
    let fun find i cc [] = NONE
          | find i [] c  = SOME 0
          | find i cc c  = if isPrefix cc c then SOME i else find (i + 1) cc (tl c)
    in find 0 xss xs end

  fun split xss xs =
    case indexOf xss xs of
      NONE => [xs]
    | SOME idx =>
        let val element = extract (xs, 0, SOME idx)
            val rest = extract (xs, idx + length xss, NONE)
        in element :: split xss rest end

  fun replaceAll xss' xss xs =
    case indexOf xss xs of
      NONE => xs
    | SOME idx =>
        let val element = extract (xs, 0, SOME idx)
            val rest = extract (xs, idx + length xss, NONE)
        in element @ xss' @ replaceAll xss' xss rest end

  fun flatten xs = List.foldl op@ [] xs
end

signature HEAP =
sig
  type 'a heap
  val make : (unit -> 'a) -> 'a heap
  val get : intinf -> 'a heap -> 'a
  val set : intinf -> 'a heap -> 'a -> unit

  val size : 'a heap -> int

  val fromList : (unit -> 'a) -> 'a list -> 'a heap
  val toList : 'a heap -> 'a list
end

infix 7 lmodi ldivi
fun op ldivi (a : intinf, b : int) = IntInf.div (a, Int.toLarge b)
fun op lmodi (a : intinf, b : int) = IntInf.mod (a, Int.toLarge b)
structure IntInfUtil =
struct
  val explodeIntInf =
    map (forceParseIntInf o String.str) o String.explode o IntInf.toString
end

structure IntMap = BinaryMapFn (struct
  type ord_key = intinf
  val compare = IntInf.compare
end)
type 'v intmap = 'v IntMap.map

structure Heap :> HEAP =
struct
  structure M = IntMap

  (* store, allocator, size *)
  type 'a heap = 'a ref intmap ref * (unit -> 'a) * int ref

  fun make alloc = (ref M.empty, alloc, ref 0)

  fun get loc (h, alloc, c) =
    case M.find (! h, loc) of
      SOME rv => ! rv
    | NONE =>
        let val default = alloc ()
        in (h := M.insert (! h, loc, ref default); c := !c + 1; default) end

  fun set loc (h, alloc, c) v =
    case M.find (! h, loc) of
      SOME rv => rv := v
    | NONE => (h := M.insert (! h, loc, ref v); c := !c + 1)

  fun size (_, _, c) = ! c

  fun fromList alloc xs =
    let fun createEntry ((x, i), m) =
          M.insert (m, Int.toLarge i, ref x)
        val store = List.foldl createEntry M.empty $ enumerate xs
    in (ref store, alloc, ref $ length xs) end

  fun toList ((h, _, _) : 'a heap) : 'a list = map op! $ M.listItems (! h)
end
type 'a heap = 'a Heap.heap

signature INTCODE =
sig
  type internal_state

  val initialProgramState : intinf list -> internal_state
  val defaultHandlers : string option -> (unit -> unit) * (string option cont -> 'a) * (string * unit cont -> 'b)

  val interpret : intinf list -> intinf heap
  val interpretLowLevel : (unit -> string option) * (string -> unit) -> internal_state -> intinf heap
  val interpretWithHandlers : (unit -> string option) * (string -> unit) -> intinf list -> intinf heap
  val interpretUnsafe : (unit -> unit) * (string option cont -> 'a) * (string * unit cont -> 'b)  -> internal_state -> intinf heap
end

(* Basic Intcode Interpreter *)
structure Intcode :> INTCODE =
struct
  open IntInfUtil
  exception Halt
  exception GetInput of string option cont
  exception SendOutput of string * unit cont

  exception Unhandled

  exception UnknownMode of int
  exception UnknownOpCode of int

  datatype evalmode = POSITION | IMMEDIATE | RELATIVE

  (* Program Counter, Heap, Relative Base *)
  type internal_state = intinf ref * intinf heap * intinf ref

  type withmode = evalmode * intinf
  datatype instruction =
      HaltProgram
    | Add of withmode * withmode * withmode
    | Mul of withmode * withmode * withmode
    | Input of withmode
    | Output of withmode
    | JumpIfTrue of withmode * withmode
    | JumpIfFalse of withmode * withmode
    | LessThan of withmode * withmode * withmode
    | Equals of withmode * withmode * withmode
    | Adjust of withmode

  val toLarge = Int.toLarge
  val fromLarge = Int.fromLarge

  fun evalmode_toString POSITION = "POS"
    | evalmode_toString IMMEDIATE = "IMM"
    | evalmode_toString RELATIVE = "REL"

  fun parseInstr (pc : intinf) (heap : intinf heap) : instruction =
    let fun getMode 0 = POSITION
          | getMode 1 = IMMEDIATE
          | getMode 2 = RELATIVE
          | getMode n = raise UnknownMode n
        fun get d = Heap.get (pc + toLarge d) heap
        fun getAll ds = map get ds
        val (modeint, opcode) = let val x = fromLarge $ get 0 in (x div 100, x mod 100) end

        val modes = rev o lpad 3 1 o lpad 2 0 o explodeInt $ modeint
        val modes = Vector.fromList o List.map getMode $ modes

        fun getWithMode d = (Vector.sub (modes, d - 1), get d)
        fun collectTernary pcon = pcon (getWithMode 1, getWithMode 2, getWithMode 3)
        fun collectBinary pcon = pcon (getWithMode 1, getWithMode 2)
    in
      case opcode of
        1 => collectTernary Add
      | 2 => collectTernary Mul
      | 3 => Input $ getWithMode 1
      | 4 => Output $ getWithMode 1
      | 5 => collectBinary JumpIfTrue
      | 6 => collectBinary JumpIfFalse
      | 7 => collectTernary LessThan
      | 8 => collectTernary Equals
      | 9 => Adjust $ getWithMode 1
      | 99 => HaltProgram
      | c => raise UnknownOpCode c
    end

  fun eval (pcref, heap, relbase) =
    let fun get l = Heap.get l heap
        fun set l v = Heap.set l heap v

        fun deriveLocation (IMMEDIATE, c) = c
          | deriveLocation (POSITION, l) = l
          | deriveLocation (RELATIVE, d) = !relbase + d

        fun derive (IMMEDIATE, c) = c
          | derive (POSITION , l) = get l
          | derive (RELATIVE , d) = get $ !relbase + d
        val pc = ! pcref
        fun adv n = (pcref := pc + n; eval (pcref, heap, relbase))
        fun jmp l = (pcref := l     ; eval (pcref, heap, relbase))
    in
      case parseInstr pc heap of
        Add (in1, in2, out) => (
          set $ deriveLocation out $ derive in1 + derive in2;
          adv 4
        )
      | Mul (in1, in2, out) => (
          set $ deriveLocation out $ derive in1 * derive in2;
          adv 4
        )
      | Input out => (
          let val c = callcc (fn k => raise GetInput k)
          in set (deriveLocation out) o Option.valOf o Option.map forceParseIntInf $ c end;
          adv 2
        )
      | Output src => (
          let val s = IntInf.toString $ derive src
          in callcc (fn k => raise SendOutput (s, k)) end;
          adv 2
        )
      | JumpIfTrue (cond, loc) =>
          if derive cond <> 0 then (jmp o derive) loc
          else adv 3
      | JumpIfFalse (cond, loc) =>
          if derive cond = 0 then (jmp o derive) loc
          else adv 3
      | LessThan (c1, c2, out) => (
          set (deriveLocation out) (if derive c1 < derive c2 then 1 else 0);
          adv 4
        )
      | Equals (c1, c2, out) => (
          set (deriveLocation out) (if derive c1 = derive c2 then 1 else 0);
          adv 4
        )
      | Adjust adj => (
          relbase := !relbase + derive adj;
          adv 2
        )
      | HaltProgram => raise Halt
    end

  fun defaultHandlers promptOpt =
    let val prompt = Option.getOpt (promptOpt, "Enter Input: ")
        val inputHdlr = (fn k => throw k $ readUserInput prompt)
        val outputHdlr = (fn (s, k) => (print s; throw k ()))
    in (fn () => (), inputHdlr, outputHdlr) end

  fun initialProgramState program =
    (ref $ toLarge 0, Heap.fromList (fn () => toLarge 0) program, ref $ toLarge 0)

  fun interpretUnsafe (onHalt, onInput, onOutput) (pc, heap, relbase) =
    eval (pc, heap, relbase)
    handle Halt => (onHalt (); heap)
         | GetInput k => (onInput k; raise Unhandled)
         | SendOutput (s, k) => (onOutput (s, k); raise Unhandled)

  fun interpretLowLevel (i, out) (pc, heap, relbase) =
    interpretUnsafe (id, (fn k => throw k $ i ()), (fn (s, k) => (out s; throw k ()))) (pc, heap, relbase)

  fun interpretWithHandlers (i, out) program =
    interpretLowLevel (i, out) $ initialProgramState program

  fun interpret program =
    interpretWithHandlers (fn () => readUserInput "Enter Input: ", print) program
end

structure IntPairKey = struct
  type ord_key = int * int
  fun compare ((a, b), (x, y)) =
    (* Sorting by descending y first
       since it doesn't affect semantics
       and makes printing easier for part 2
    *)
    case (Int.compare (y, b), Int.compare (a, x)) of
      (EQUAL, ord) => ord
    | (ord, _) => ord
end

structure IntPairMap = BinaryMapFn (IntPairKey)
structure IntPairSet = BinarySetFn (IntPairKey)
structure IPM = IntPairMap
structure IPS = IntPairSet
type 'a intpairmap = 'a IntPairMap.map
type intpairset = IntPairSet.set

fun attemptDequeue q = (SOME $ Queue.dequeue q) handle Queue.Dequeue => NONE

structure PathFinder =
struct
  datatype action = FORWARD | LEFT | RIGHT
  datatype orientation = NORTH | SOUTH | EAST | WEST
  type position = int * int

  datatype state = State of { facing : orientation, pos : position, path : action list, visitLimits : int intpairmap, seen : intpairset }
  type stateq = state Queue.queue

  fun makeState (d : orientation, p : position, pth : action list, v : int intpairmap, seen : intpairset) =
    State { facing = d, pos = p, path = pth, visitLimits = v, seen = seen }

  fun rotateLeft NORTH = WEST
    | rotateLeft WEST = SOUTH
    | rotateLeft SOUTH = EAST
    | rotateLeft EAST = NORTH

  fun rotateRight NORTH = EAST
    | rotateRight EAST = SOUTH
    | rotateRight SOUTH = WEST
    | rotateRight WEST = NORTH

  fun moveForward NORTH (r, c) = (r - 1, c)
    | moveForward SOUTH (r, c) = (r + 1, c)
    | moveForward EAST (r, c) = (r, c + 1)
    | moveForward WEST (r, c) = (r, c - 1)

  fun applyActions d (r, c) [] = (d, r, c)
    | applyActions d (r, c) (act :: acts) =
        case act of
          FORWARD => applyActions d (moveForward d (r, c)) acts
        | LEFT => applyActions (rotateLeft d) (r, c) acts
        | RIGHT => applyActions (rotateRight d) (r, c) acts

  fun findPaths (positions : ((int * int) * char) list) (intersections : (int * int) list) =
    let val [robotPosition] = map (#1) o List.filter (curry op= #"^" o (#2)) $ positions
        val scaffolds = map (#1) o List.filter (curry op= #"#" o (#2)) $ positions
        val intersectionSet = List.foldl IPS.add' IPS.empty intersections
        val scaffoldSet = List.foldl IPS.add' IPS.empty scaffolds
        val scaffoldVisitLimitMap = List.foldl (fn (p, m) =>
          let val limit = if IPS.member (intersectionSet, p) then 2 else 1
          in IPM.insert (m, p, limit) end
        ) IPM.empty scaffolds

        fun isValidPath path seen =
          let val diff = IPS.difference (scaffoldSet, seen)
          in IPS.isEmpty diff end

        (* Returns (direction and new location, actions to get there) pairs *)
        fun getPotentialActions (State { facing, pos, visitLimits, ... }) =
          let fun canVisit (_, r, c) =
                case IPM.find (visitLimits, (r, c)) of
                  NONE => false
                | SOME n => n > 0
              val possibleActions = [
                [FORWARD], [LEFT, FORWARD], [RIGHT, FORWARD], [LEFT, LEFT, FORWARD]
              ]
              val around = map (fn acts => applyActions facing pos acts) possibleActions
              val around = ListPair.zip (around, possibleActions)
              val around = List.filter (canVisit o (#1)) around
          in around end

          fun dfs (st as State { facing, pos, path, visitLimits, seen }, k : action list option cont) : action list option =
            let val actions = getPotentialActions st
                fun actionToState ((d, r, c), acts) =
                  let val (SOME n) = IPM.find (visitLimits, (r, c))
                      val visitLimits' = IPM.insert (visitLimits, (r, c), n - 1)
                  in makeState (d, (r, c), rev acts @ path, visitLimits', IPS.add (seen, (r, c))) end
            in
              case map actionToState actions of
                [] => if isValidPath path seen then throw k (SOME (rev path)) else ()
              | states => List.app (fn st => ignore $ dfs (st, k)) states;
              NONE
            end

        val initialState = makeState (NORTH, robotPosition, [], scaffoldVisitLimitMap, IPS.empty)
        val (SOME path) = callcc (fn k => dfs (initialState, k))
        val grouped = strides op= path

        fun toProgram [] = []
          | toProgram ([RIGHT] :: xs) = "R" :: toProgram xs
          | toProgram ([LEFT] :: xs) = "L" :: toProgram xs
          | toProgram (ms :: xs) = Int.toString (length ms) :: toProgram xs
    in toProgram grouped end
end

structure ASCII =
struct
  structure M = IntPairMap
  exception SignalUnknown of int

  fun make rountinesOpt =
    let exception Impossible
        val asciiCont : (unit -> (int * unit cont) cont) ref = ref (fn () => raise Impossible)
        val routineCont : (unit -> string option cont cont) ref = ref (fn () => raise Impossible)

        fun onInput k = throw $ (! routineCont) () $ k
        fun onOutput (s, k) = throw $ (! asciiCont) () $ (forceParseInt s, k)

        val locationMap : char intpairmap ref = ref M.empty
        val lines : char list list ref = ref [[]]
        val row : int ref = ref 0
        val col : int ref = ref 0
        val dust : int ref = ref 0

        fun getLines () = let val ls = rev o map rev $ (!lines) in map String.implode ls end
        fun getState () = (!locationMap, getLines (), !dust)
        fun setCont k = asciiCont := (fn () => k)
        fun setRoutineCont k = routineCont := (fn () => k)

        fun consume ch =
          let val (loc as (r, c)) = (!row, !col)
              val (ln :: lns) = !lines
              val ln' = ch :: ln
              val lns' = ln' :: lns
          in
            locationMap := M.insert (!locationMap, loc, ch);
            col := c + 1;
            case Char.ord ch of
              10 => (lines := ([] :: lns'); row := r + 1; col := 0)
            | _ => lines := lns'
          end

        fun checkpointAndCall setk k v =
          callcc (fn continue => (setk continue; throw k v))

        fun cameraServer (ord, k) =
          let val _ = consume $ Char.chr ord handle Char => if !dust = 0 then (dust := ord) else raise Char
          in cameraServer $ checkpointAndCall setCont k () end

        fun routineServer [] k = raise Impossible
          | routineServer (r :: rs) k =
              let fun subserver [] k = routineServer rs k
                    | subserver (c :: cs) k = subserver cs $ checkpointAndCall setRoutineCont k (SOME o Int.toString $ Char.ord c)
                  val cs = String.explode (String.concatWith "," r) @ [Char.chr 10]
              in subserver cs k end

        fun spinUp (setk, server) k = server $ callcc (fn continue => (setk continue; throw k ()))
    in
      callcc $ spinUp (setCont, cameraServer);
      callcc $ spinUp (setRoutineCont, routineServer $ Option.getOpt (rountinesOpt, []));
      (onInput, onOutput, getState)
    end
end

fun splitIntoRoutines maxSize xs =
  let open ListUtil
      datatype state = State of { progs : string list list, remaining : string list, depth : int }

      fun depthRequiredBFS d q k =
        case attemptDequeue q of
          NONE => ()
        | SOME (State { progs, remaining, depth }) => (
            case (depth = d, length remaining = 0) of
              (true, true) => throw k $ SOME progs
            | (false, true) => ()
            | (true, false) => ()
            | _ =>
              let
                fun makeStates n =
                  if n >= maxSize orelse n > length remaining then []
                  else
                    let val newProg = extract (remaining, 0, SOME n)
                        val remaining' = flatten $ split newProg remaining
                        val st = State { progs = newProg :: progs, remaining = remaining', depth = depth + 1 }
                    in st :: makeStates (n + 1) end
              in List.app (fn st => Queue.enqueue (q, st)) $ makeStates 2 end;
            depthRequiredBFS d q k
        )

      val initialState = State { progs = [], remaining = xs, depth = 0 }
      val initialQueue : state Queue.queue = Queue.mkQueue ()
      val _ = Queue.enqueue (initialQueue, initialState)
      val r = callcc (fn k => (depthRequiredBFS 3 initialQueue k; NONE))
  in r end

(* Entry Functions *)

fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day17.in")
      val rawInput = withFile filename (Option.valOf o TextIO.inputLine)
      val isDelim = curry op= #","
      val tokenized = map forceParseIntInf o String.tokens isDelim $ rawInput
  in f tokenized end

fun part1 fOpt = withInput fOpt (fn program => (
  let val state = Intcode.initialProgramState program
      val (_, outputHdlr, getState) = ASCII.make NONE
      val (haltHdlr, inputHdlr, _) = Intcode.defaultHandlers NONE

      val hdlrs = (haltHdlr, inputHdlr, outputHdlr)
      val heap = Intcode.interpretUnsafe hdlrs state
      val (writes, lines, _) = getState ()

      fun isIntersection (x, y) =
        let val checks = [(x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)]
            val opts = map (curry IPM.find $ writes) checks
            val chars = map (fn opt => Option.getOpt (opt, #" ")) opts
        in List.all (curry op= #"#") chars end

      val scaffolds = List.filter (curry op= #"#" o (#2)) $ IPM.listItemsi writes
      val intersections = List.filter isIntersection $ map (#1) scaffolds
      val parameters = map op* intersections
      val sum = List.foldl op+ 0 parameters
      val _ = print o concat $ lines
  in (intersections, sum, getState ()) end
))

fun part2 fOpt = withInput fOpt (fn program => (
  let val program = 2 :: tl program
      val state = Intcode.initialProgramState program
      val (intersections, _, (writes, _, _)) = part1 fOpt
      val positions = IPM.listItemsi writes
      val fullRoutine = PathFinder.findPaths positions intersections
      val SOME [a, b, c] = splitIntoRoutines 11 fullRoutine
      val reduced = ListUtil.replaceAll ["A"] a fullRoutine
      val reduced = ListUtil.replaceAll ["B"] b reduced
      val reduced = ListUtil.replaceAll ["C"] c reduced

      val (inputHdlr, outputHdlr, getState) = ASCII.make $ SOME ([reduced, a, b, c, ["n"]])
      val (haltHdlr, _, _) = Intcode.defaultHandlers NONE
      val hdlrs = (haltHdlr, inputHdlr, outputHdlr)
      val state = Intcode.initialProgramState program
      val heap = Intcode.interpretUnsafe hdlrs state
      val (_, _, dust) = getState ()
  in (fullRoutine, [a, b, c], reduced, dust) end
))

fun main ((name, args) : string * string list) : unit =
  let fun exec "part1" x =
          let val (_, ans, _) = part1 x
          in print $ Int.toString ans end
        | exec "part2" x =
          let val (_, _, _, ans) = part2 x
          in print $ Int.toString ans end
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, " part [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
