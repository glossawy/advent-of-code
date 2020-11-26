(* Standard ML of New Jersey v110.91 *)

structure Cont = SMLofNJ.Cont
type 'a cont = 'a Cont.cont
val callcc = Cont.callcc
val throw = Cont.throw

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

fun id x = x
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y

val forceParseInt = Option.valOf o Int.fromString
val explodeInt = map (forceParseInt o Char.toString) o String.explode o Int.toString

fun lpad n p xs = if length xs < n then p :: lpad (n - 1) p xs else xs
fun interleave x [] = [[x]]
  | interleave x (h::t) =
      (x::h::t)::(List.map(fn l => h::l) (interleave x t))

fun permute nil = [[]]
  | permute (h::t) = List.concat( List.map (fn l => interleave h l) (permute t))


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

  val toList : 'a queue -> 'a list
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

  fun toList ([], []) = []
    | toList q =
        let val (x, q') = pop q
        in x :: toList q' end
end
type 'a queue = 'a Queue.queue

signature SUSP =
sig
  type 'a susp
  val force : 'a susp -> 'a
  val delay : (unit -> 'a) -> 'a susp
end

structure Susp :> SUSP =
struct
  type 'a susp = unit -> 'a

  fun force f = f ()
  fun delay (f : 'a susp) =
    let exception Impossible
        val memo : 'a susp ref = ref (fn () => raise Impossible)
        fun suspended () =
          let val r = f () in memo := (fn () => r); r end
    in memo := suspended; fn () => (!memo) () end
end
type 'a susp = 'a Susp.susp
val (force, delay) = (Susp.force, Susp.delay)

signature STREAM =
sig
  type 'a stream

  val nilstream : unit -> 'a stream

  val next : 'a stream -> ('a * 'a stream) option
  val nextValue : 'a stream -> ('a * 'a stream)
  val isNil : 'a stream -> bool
  val append : 'a stream -> 'a stream -> 'a stream
  val fromList : 'a list -> 'a stream
  val toList : 'a stream -> 'a list
end

structure Stream :> STREAM =
struct
  datatype 'a stream = Nil | Cons of 'a * 'a stream susp
  type 'a stream = 'a stream susp

  fun nilstream () = delay (fn () => Nil)

  fun next strm =
    case force strm of
      Nil => NONE
    | Cons (x, strm') => SOME (x, strm')

  fun nextValue strm =
    Option.valOf o next $ strm

  fun isNil strm =
    not o Option.isSome $ next strm

  fun append strmA strmB =
    delay (fn () =>
      case force strmA of
        Nil => force strmB
      | Cons (x, strmA') => Cons (x, append strmA' strmB)
    )

  fun fromList xs =
    delay (fn () =>
      case xs of
        [] => Nil
      | (h :: t) => Cons (h, fromList t)
    )

  fun toList strm =
    case force strm of
      Nil => []
    | Cons (x, strm') => x :: toList strm'
end
type 'a stream = 'a Stream.stream


signature HEAP =
sig
  type 'a heap
  val get : int -> 'a heap -> 'a
  val set : int -> 'a heap -> 'a -> unit

  val size : 'a heap -> int

  val fromList : 'a list -> 'a heap
  val toList : 'a heap -> 'a list
end

structure Heap :> HEAP =
struct
  open Vector
  type 'a heap = 'a ref vector

  fun get loc h = op! o sub $ (h, loc)
  fun set loc h v = sub (h, loc) := v
  fun size h = Vector.length h

  fun fromList xs = Vector.fromList o List.map ref $ xs
  fun toList h = Vector.foldr op:: [] $ Vector.map op! h
end
type 'a heap = 'a Heap.heap

signature INTCODE =
sig
  type internal_state

  val initialProgramState : int list -> internal_state

  val interpret : int list -> int heap
  val interpretLowLevel : (unit -> string option) * (string -> unit) -> internal_state -> int heap
  val interpretWithHandlers : (unit -> string option) * (string -> unit) -> int list -> int heap
  val interpretUnsafe : (unit -> 'c) * (string option cont -> 'a) * (string * unit cont -> 'b)  -> internal_state -> int heap
end

(* Basic Intcode Interpreter *)
structure Intcode :> INTCODE =
struct
  exception Halt
  exception GetInput of string option cont
  exception SendOutput of string * unit cont

  exception Unhandled

  exception UnknownMode of int
  exception UnknownOpCode of int

  datatype evalmode = POSITION | IMMEDIATE

  type internal_state = int ref * int heap

  type withmode = evalmode * int
  datatype instruction =
      HaltProgram
    | Add of withmode * withmode * withmode
    | Mul of withmode * withmode * withmode
    | Input of int
    | Output of int
    | JumpIfTrue of withmode * withmode
    | JumpIfFalse of withmode * withmode
    | LessThan of withmode * withmode * withmode
    | Equals of withmode * withmode * withmode

  fun parseInstr (pc : int) (heap : int heap) : instruction =
    let fun getMode 0 = POSITION
          | getMode 1 = IMMEDIATE
          | getMode n = raise UnknownMode n
        fun get d = Heap.get (pc + d) heap
        fun getAll ds = map get ds
        val (modeint, opcode) = let val x = get 0 in (x div 100, x mod 100) end

        (* modeint = 11, modes = [1,1,0] *)
        val modes = rev o lpad 3 1 o lpad 2 0 o explodeInt $ modeint
        val modes = Vector.fromList o List.map getMode $ modes

        fun getWithMode d = (Vector.sub (modes, d - 1), get d)
        fun collectTernary pcon = pcon (getWithMode 1, getWithMode 2, getWithMode 3)
        fun collectBinary pcon = pcon (getWithMode 1, getWithMode 2)
    in
      case opcode of
        1 => collectTernary Add
      | 2 => collectTernary Mul
      | 3 => Input $ get 1
      | 4 => Output $ get 1
      | 5 => collectBinary JumpIfTrue
      | 6 => collectBinary JumpIfFalse
      | 7 => collectTernary LessThan
      | 8 => collectTernary Equals
      | 99 => HaltProgram
      | c => raise UnknownOpCode c
    end


  fun eval (pcref, heap) =
    let fun get l = Heap.get l heap
        fun set l v = Heap.set l heap v
        fun derive (IMMEDIATE, c) = c
          | derive (POSITION , l) = get l
        val pc = ! pcref
        fun adv n = (pcref := pc + n; eval (pcref, heap))
        fun jmp l = (pcref := l     ; eval (pcref, heap))
    in
      case parseInstr pc heap of
        Add (in1, in2, out) => (
          set $ derive out $ derive in1 + derive in2;
          adv 4
        )
      | Mul (in1, in2, out) => (
          set $ derive out $ derive in1 * derive in2;
          adv 4
        )
      | Input out => (
          (* print "Input"; *)
          let val c = callcc (fn k => raise GetInput k)
          in set out o Option.valOf o Option.map forceParseInt $ c end;
          (* print "Got input"; *)
          adv 2
        )
      | Output src => (
          (* print "Output"; *)
          let val s = Int.toString $ get src
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
          set (derive out) (if derive c1 < derive c2 then 1 else 0);
          adv 4
        )
      | Equals (c1, c2, out) => (
          set (derive out) (if derive c1 = derive c2 then 1 else 0);
          adv 4
        )
      | HaltProgram => raise Halt
    end

  fun initialProgramState program = (ref 0, Heap.fromList program)

  fun interpretUnsafe (onHalt, onInput, onOutput) (pc, heap) =
    eval (pc, heap)
    handle Halt => (onHalt (); heap)
         | GetInput k => (onInput k; raise Unhandled)
         | SendOutput (s, k) => (onOutput (s, k); raise Unhandled)

  fun interpretLowLevel (i, out) (pc, heap) =
    interpretUnsafe (id, (fn k => throw k $ i ()), (fn (s, k) => (out s; throw k ()))) (pc, heap)

  fun interpretWithHandlers (i, out) program =
    interpretLowLevel (i, out) $ initialProgramState program

  fun interpret program =
    interpretWithHandlers (fn () => readUserInput "Enter Input: ", print) program

end

(* Entry Functions *)

fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day7.in")
      val rawInput = withFile filename (Option.valOf o TextIO.inputLine)
      val isDelim = curry op= #","
      val tokenized = map forceParseInt o String.tokens isDelim $ rawInput
  in f tokenized end

fun toInputTuple (x1 :: x2 :: x3 :: x4 :: x5 :: _) = (x1, x2, x3, x4, x5)
val allPermutations = map toInputTuple o permute $ [0, 1, 2, 3, 4]
val allPermutations2 = map toInputTuple o permute $ [5, 6, 7, 8, 9]

fun run fOpt (p1, p2, p3, p4, p5) = withInput fOpt (fn program =>
  let val output = ref 0
      fun handler s =
        let val strm = ref s
            fun f () =
              case Stream.next (! strm) of
                NONE => NONE
              | SOME (x, strm') => (strm := strm'; SOME x)
        in f end
      fun listHdlr xs = handler o Stream.fromList $ List.map Int.toString xs
      fun outputHdlr s = output := forceParseInt s
      val _ = Intcode.interpretWithHandlers (listHdlr [p1, 0], outputHdlr) program
      val _ = Intcode.interpretWithHandlers (listHdlr [p2, ! output], outputHdlr) program
  in
    Intcode.interpretWithHandlers (listHdlr [p1, 0], outputHdlr) program;
    Intcode.interpretWithHandlers (listHdlr [p2, !output], outputHdlr) program;
    Intcode.interpretWithHandlers (listHdlr [p3, !output], outputHdlr) program;
    Intcode.interpretWithHandlers (listHdlr [p4, !output], outputHdlr) program;
    Intcode.interpretWithHandlers (listHdlr [p5, !output], outputHdlr) program;
    !output
  end
)

fun runPart2 fOpt (p1, p2, p3, p4, p5) = withInput fOpt (fn program =>
  let
      (* Queue Helpers *)
      fun enqueue x q = q := (Queue.push x (! q))
      fun dequeue q =
        let val (x, q') = Queue.pop (! q)
        in (q := q'; x) end
      fun dequeueOpt default q = dequeue q handle Queue.Pop => default

      val states = List.map Intcode.initialProgramState $ [
        program, program, program, program, program
      ]

      val output = ref 0
      val currentAmp = ref ~1
      val amps = Vector.fromList states

      val initialInputs : string list queue ref =
        let val wrapUp = List.foldl (uncurry Queue.push) Queue.empty
            val mapper = List.map Int.toString
            val inputs = List.map mapper [
              [p1, 0], [p2], [p3], [p4], [p5]
            ]
        in ref o wrapUp $ inputs end

      fun nextAmp () =
        let val n = (!currentAmp + 1) mod 5
        in (currentAmp := n; Vector.sub (amps, n)) end

      (* Pretty hard coded, but does the threading of continuations.

        Can almost certainly be generalized.
      *)
      fun run st using onHalt =
        let val strmval = Stream.fromList using
            val seedval = Stream.fromList $ dequeueOpt [] initialInputs
            val strm = ref $ Stream.append seedval strmval
            val outputs : string queue ref = ref Queue.empty
        in
          callcc (fn k => (
            Intcode.interpretUnsafe (
              (fn () =>
                if !currentAmp <> 4 then throw k ()
                else onHalt ()
              ),
              (fn kIn =>
                case Stream.next $ !strm of
                  NONE => throw k ()
                | SOME (x, strm') => (strm := strm'; throw kIn $ SOME x)
              ),
              (fn (s, kOut) => (
                output := forceParseInt s;
                enqueue s outputs;
                throw kOut ()
              ))
            ) st;
            ()
          ));
          run $ nextAmp () $ Queue.toList (! outputs) $ onHalt
        end
  in
    callcc (fn k => (run $ nextAmp () $ [] $ throw k));
    ! output
  end
)

fun solve fOpt =
  let val results = List.map (run fOpt) allPermutations
  in Option.valOf o maximum Int.compare $ results end

fun solvePart2 fOpt =
  let val results = List.map (runPart2 fOpt) allPermutations2
      val maximum = Option.valOf o maximum Int.compare $ results
  in maximum end

fun main (name, args) =
  let fun exec "part1" fOpt = print $ Int.toString (solve fOpt)
        | exec "part2" fOpt = print $ Int.toString (solvePart2 fOpt)
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, "<part1|part2> [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
