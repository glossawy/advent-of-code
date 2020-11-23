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

signature HEAP =
sig
  type 'a heap
  val make : (unit -> 'a) -> 'a heap
  val get : intinf -> 'a heap -> 'a
  val set : intinf -> 'a heap -> 'a -> unit

  val size : 'a heap -> int

  val copy : 'a heap -> 'a heap
  val fromList : (unit -> 'a) -> 'a list -> 'a heap
  val toList : 'a heap -> 'a list
end

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

  fun copy (h, alloc, c) =
    let val pairs = map (fn (k, rv) => (k, ref $ !rv)) $ M.listItemsi (! h)
        val h' = List.foldl M.insert' M.empty pairs
    in (ref h', alloc, ref $ !c) end

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
  val copyProgramState : internal_state -> internal_state
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

  fun copyProgramState (pc, hp, relbase) =
    (ref $ !pc, Heap.copy hp, ref $ !relbase)

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

structure IntPairKey =
struct
  type ord_key = int * int
  fun compare ((a, b), (x, y)) =
    case (Int.compare (y, b), Int.compare (a, x)) of
      (EQUAL, ord) => ord
    | (ord, _) => ord
end

structure IntPairMap = BinaryMapFn (IntPairKey)
structure IntPairSet = BinarySetFn (IntPairKey)
type 'a pairmap = 'a IntPairMap.map
type pairset = IntPairSet.set

structure RemoteCommand =
struct
  structure M = IntPairMap
  structure S = IntPairSet
  exception SignalUnknown of int

  type position = int * int
  type program = Intcode.internal_state

  type visited_set =

  datatype action = MOVE_NORTH | MOVE_SOUTH | MOVE_EAST | MOVE_WEST
  datatype response = WALL | MOVED | FOUND
  datatype state = State of { actions : action list, pos : position, seen : pairset, program : program }

  (* Breadth-first search via continuations and returning to main function via continuation? *)
  (* Didn't think I would use continuations so much... *)

  val copyState = Intcode.copyProgramState

  fun make (initialProgram : program) (exitCont : state cont)  =
    let val stateQueue : state Queue.queue = Queue.mkQueue ()
        val initialState = State { actions = [], pos = (0, 0), seen = S.empty, program = initialProgram }
        val _ = Queue.enqueue (stateQueue, initialState)

        fun searchServer
    in end

end

(* Entry Functions *)

fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day15.in")
      val rawInput = withFile filename (Option.valOf o TextIO.inputLine)
      val isDelim = curry op= #","
      val tokenized = map forceParseIntInf o String.tokens isDelim $ rawInput
  in f tokenized end
