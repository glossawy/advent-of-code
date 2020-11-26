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
  val debug = false
  val stdin = TextIO.stdIn
  val removeNewline = String.translate (fn c => if c = #"\n" then "" else String.str c)
  fun writeOut ending pipe s = (TextIO.output (pipe, s ^ ending); TextIO.flushOut pipe)
in
  val print = writeOut "\n" stdout
  val printConcat = print o concat
  val printErr = writeOut "\n" stderr
  val printDebug = if debug then print else ignore
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

type intinf = IntInf.int

fun id x = x
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y

val forceParseInt = Option.valOf o Int.fromString
val forceParseIntInf = Option.valOf o IntInf.fromString

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

structure IntPairMap = BinaryMapFn (struct
  type ord_key = int * int
  fun compare ((a, b), (x, y)) =
    (* Sorting by descending y first
       since it doesn't affect semantics
       and makes printing easier for part 2
    *)
    case (Int.compare (y, b), Int.compare (a, x)) of
      (EQUAL, ord) => ord
    | (ord, _) => ord
end)
type 'a intpairmap = 'a IntPairMap.map

structure Arcade =
struct
  structure M = IntPairMap
  exception SignalUnknown of int

  datatype blocktype = EMPTY | WALL | BLOCK | PADDLE | BALL
  type position = int * int

  fun signalToBlockType 0 = EMPTY
    | signalToBlockType 1 = WALL
    | signalToBlockType 2 = BLOCK
    | signalToBlockType 3 = PADDLE
    | signalToBlockType 4 = BALL
    | signalToBlockType n = raise SignalUnknown n

  fun blockTypeToString EMPTY = " "
    | blockTypeToString WALL = "#"
    | blockTypeToString BLOCK = "□"
    | blockTypeToString PADDLE = "▢"
    | blockTypeToString BALL = "o"

  fun groupRows xs =
    strides (fn (((_, y), _), ((_, y'), _)) => y = y') xs

  fun drawArcadeScreen blocks =
    let fun renderRow blocks = concat $ map blockTypeToString blocks
        val minx = Option.valOf o minimum Int.compare $ map ((#1) o (#1)) blocks
        val maxx = Option.valOf o maximum Int.compare $ map ((#1) o (#1)) blocks

        fun xrange a b =
          if a >= b then []
          else a :: xrange (a + 1) b

        fun fillInDiscontinuities [] = []
          | fillInDiscontinuities [x] = [x]
          | fillInDiscontinuities (a :: b :: rest) =
              let val ((ax, ay), ac) = a
                  val ((bx, by), bc) = b
                  val filler = map (fn x => ((x, ay), EMPTY)) $ xrange (ax + 1) bx
              in (a :: filler) @ fillInDiscontinuities (b :: rest) end

        fun padToMin [] =[]
          | padToMin (xs as ((x, y), _) :: _) =
              let val filler = map (fn x' => ((x', y), EMPTY)) $ xrange minx x
              in filler @ xs end

        fun padToMax [] = []
          | padToMax (xs as [((x, y), _)]) =
              let val filler = map (fn x' => ((x', y), EMPTY)) $ xrange x maxx
              in xs @ filler end
          | padToMax (x :: xs) = x :: padToMin xs

        val rows = groupRows blocks
    in String.concatWith "\n" o map (renderRow o map (#2) o padToMax o padToMin o fillInDiscontinuities) $ rev rows end

  fun make () =
    let exception Impossible
        val arcadeCont : (unit -> (int * unit cont) cont) ref = ref (fn () => raise Impossible)
        val aiCont : (unit -> string option cont cont) ref = ref (fn () => raise Impossible)
        val score = ref 0
        val blocks : blocktype intpairmap ref = ref M.empty
        val ballPosition : position ref = ref (0, 0)
        val paddlePosition : position ref = ref (0, 0)

        fun onAiInput k =throw $ (! aiCont) () $ k
        fun onOutput (s, k) = throw $ (! arcadeCont) () $ (forceParseInt s, k)

        fun renderBlock (x, y) block =
          let val _ = (
            case block of
              BALL => ballPosition := (x, y)
            | PADDLE => paddlePosition := (x, y)
            | _ => ()
          )
          in blocks := M.insert (! blocks, (x, y), block) end

        fun getState () = (!score, M.listItemsi $ !blocks)
        fun setCont k = arcadeCont := (fn () => k)
        fun setAiCont k = aiCont := (fn () => k)
        fun updateScore s = (printDebug $ Int.toString s; score := s)

        fun aiServer k =
          let val (bx, by) = !ballPosition
              val (px, py) = !paddlePosition
              val joystick = Int.toString $ Int.sign (bx - px)
          in
            aiServer $ callcc (fn continue => (setAiCont continue; throw k $ SOME joystick))
          end

        fun server (x, k) =
          let val (y, k)    = callcc (fn continue => (setCont continue; throw k ()))
              val (b, k) = callcc (fn continue => (setCont continue; throw k ()))
          in
            if (x, y) = (~1, 0) then updateScore b
            else renderBlock (x, y) (signalToBlockType b);
            server $ callcc (fn continue => (setCont continue; throw k ()))
          end

        fun spinUp (setk, server) k =
          server $ callcc (fn continue => (setk continue; throw k ()))
    in
      callcc $ spinUp (setCont, server);
      callcc $ spinUp (setAiCont, aiServer);
      (onAiInput, onOutput, getState)
    end
end

(* Entry Functions *)

fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day13.in")
      val rawInput = withFile filename (Option.valOf o TextIO.inputLine)
      val isDelim = curry op= #","
      val tokenized = map forceParseIntInf o String.tokens isDelim $ rawInput
  in f tokenized end

fun part1 fOpt = withInput fOpt (fn program => (
  let val state = Intcode.initialProgramState program
      val (_, outputHdlr, getArcadeState) = Arcade.make ()
      val (haltHdlr, inputHdlr, _) = Intcode.defaultHandlers NONE
      val hdlrs = (haltHdlr, inputHdlr, outputHdlr)
      val heap = Intcode.interpretUnsafe hdlrs state
      val (_, blocks) = getArcadeState ()
  in
    length o List.filter (curry op= Arcade.BLOCK o (#2)) $ blocks
  end
))

datatype solvemode = SPECTATOR | INSTANT

fun part2 mode fOpt = withInput fOpt (fn program => (
  let val program = 2 :: tl program
      val state = Intcode.initialProgramState program
      val (aiHdlr, outputHdlr, getArcadeState) = Arcade.make ()
      val (haltHdlr, _, _) = Intcode.defaultHandlers NONE

      fun wait millis =
        let open Time
            fun spin stop =
              if Time.now () >= stop then ()
              else spin stop
        in spin $ Time.now () + Time.fromMilliseconds (Int.toLarge millis) end

      fun inputHdlr inK =
        let val (_, blocks) = getArcadeState ()
        in
          (
            case mode of
              INSTANT => ()
            | SPECTATOR => (
              print "\n";
              print o Arcade.drawArcadeScreen $ blocks;
              wait 10
            )
          );
          aiHdlr inK
        end

      val hdlrs = (haltHdlr, inputHdlr, outputHdlr)
      val heap = Intcode.interpretUnsafe hdlrs state
      val (score, _) = getArcadeState ()
  in
    score
  end
))

fun main ((name, args) : string * string list) =
  let fun exec "part1" = print o Int.toString o part1
        | exec "part2" = print o Int.toString o part2 INSTANT
        | exec "watch2" = print o Int.toString o part2 SPECTATOR
        | exec s = raise Fail $ concat ["Invalid part"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, " <part1|part2|watch2> [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
