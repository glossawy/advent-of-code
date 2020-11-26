(* Standard ML of New Jersey v110.91 *)

structure Cont = SMLofNJ.Cont
type 'a cont = 'a Cont.cont
val callcc = Cont.callcc
val throw = Cont.throw

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
end

fun id x = x
fun curry f x y = f (x, y)

val forceParseInt = Option.valOf o Int.fromString
val explodeInt = map (forceParseInt o Char.toString) o String.explode o Int.toString

fun lpad n p xs = if length xs < n then p :: lpad (n - 1) p xs else xs

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

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
  val interpretWithHandler : ((string * string option cont) -> 'b) -> int list -> int heap
  val interpret : int list -> int heap
end

(* Basic Intcode Interpreter *)
structure Intcode :> INTCODE =
struct
  exception Halt
  exception GetInput of string * string option cont
  exception Unhandled
  exception UnknownMode of int
  exception UnknownOpCode of int

  datatype evalmode = POSITION | IMMEDIATE

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


  fun eval (pc, heap) =
    let fun get l = Heap.get l heap
        fun set l v = Heap.set l heap v
        fun derive (IMMEDIATE, c) = c
          | derive (POSITION , l) = get l
    in
      case parseInstr pc heap of
        Add (in1, in2, out) => (
          set $ derive out $ derive in1 + derive in2;
          eval (pc + 4, heap)
        )
      | Mul (in1, in2, out) => (
          set $ derive out $ derive in1 * derive in2;
          eval (pc + 4, heap)
        )
      | Input out => (
          set out o Option.valOf o (Option.map forceParseInt) $ callcc (fn k => raise GetInput ("Enter Input: ", k));
          eval (pc + 2, heap)
        )
      | Output src => (
          print o Int.toString $ get src;
          eval (pc + 2, heap)
        )
      | JumpIfTrue (cond, loc) =>
          if derive cond <> 0 then eval (derive loc, heap)
          else eval (pc + 3, heap)
      | JumpIfFalse (cond, loc) =>
          if derive cond = 0 then eval (derive loc, heap)
          else eval (pc + 3, heap)
      | LessThan (c1, c2, out) => (
          set (derive out) (if derive c1 < derive c2 then 1 else 0);
          eval (pc + 4, heap)
        )
      | Equals (c1, c2, out) => (
          set (derive out) (if derive c1 = derive c2 then 1 else 0);
          eval (pc + 4, heap)
        )
      | HaltProgram => raise Halt
    end

  fun interpretWithHandler onInput program  = 
    let val (pc, heap) = (0, Heap.fromList program)
    in
      eval (pc, heap)
      handle Halt => heap
           | GetInput (prompt, k) => (onInput (prompt, k); raise Unhandled)
    end

  val interpret = interpretWithHandler (fn (prompt, k) => throw k (readUserInput prompt))
end

(* Entry Functions *)

fun withInput fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day5.in")
      val rawInput = withFile filename (Option.valOf o TextIO.inputLine)
      val isDelim = curry op= #","
      val tokenized = map forceParseInt o String.tokens isDelim $ rawInput
  in f tokenized end

fun solve inp fOpt = withInput fOpt $ (fn tokens => 
  let exception EmptyBuffer
      val inputs : string list ref = ref $ List.map Int.toString inp
      fun onInput (_, k) =
        let val inputBuffer = ! inputs
            val _ = (if List.length inputBuffer = 0 then raise EmptyBuffer else true)
            val (nxt :: rest) = inputBuffer
            val _ = (inputs := rest)
        in 
          printConcat ["Yielding input: ", nxt];
          throw k $ SOME nxt
        end
  in
    Intcode.interpretWithHandler onInput tokens
  end
)

fun main (name, args) = ignore $
  let fun exec "part1" = solve [1]
        | exec "part2" = solve [5]
        | exec s = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, "<part1|part2> [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
