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

val raised : exn option ref = ref NONE
type intinf = IntInf.int

(* Basic useful functions *)
fun id x = x
fun const k = (fn _ => k)
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y
fun flip f (y, x) = f (x, y)

val forceParseInt = Option.valOf o Int.fromString

fun enumerate [] = []
  | enumerate xs =
      let fun enumHelp i [] = []
            | enumHelp i (x :: xs) = (x, i) :: enumHelp (i + 1) xs
      in enumHelp 0 xs end

fun repeat n xs =
  if n <= 0 then []
  else xs @ repeat (n - 1) xs

fun repeatedly n action =
  if n <= 0 then ()
  else (action (); repeatedly n action)

fun makeList n x =
  if n <= 0 then []
  else x :: makeList (n-1) x

fun cutInHalf [] = ([], [])
  | cutInHalf xs =
      let val halfLen = length xs div 2
      in (List.take (xs, halfLen), List.drop (xs, halfLen)) end


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
  val nextValue : 'a stream -> 'a * 'a stream
  val peek : 'a stream -> 'a option
  val isNil : 'a stream -> bool

  val map : ('a -> 'b) -> 'a stream -> 'b stream
  val zip : 'a stream -> 'b stream -> ('a * 'b) stream
  val fold : ('a * 'b -> 'b) -> 'b -> 'a stream -> 'b

  val take : int -> 'a stream -> 'a list * 'a stream
  val drop : int -> 'a stream -> 'a stream

  val sequence : 'a stream list -> 'a stream
  val repeat : int -> 'a -> 'a stream
  val iterate : ('a -> 'a option) -> 'a -> 'a stream
  val generate : (unit -> 'a) -> 'a stream
  val cycle : 'a stream -> 'a stream
  val cycleList : 'a list -> 'a stream

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

  fun map f strm =
    delay (fn () =>
      case force strm of
        Nil => Nil
      | Cons (v, strm') => Cons (f v, map f strm')
    )

  fun append strmA strmB =
    delay (fn () =>
      case force strmA of
        Nil => force strmB
      | Cons (x, strmA') => Cons (x, append strmA' strmB)
    )

  fun take n strm =
    if (print o Int.toString $ n; n <= 0) then ([], strm)
    else
      case force strm of
        Nil => ([], strm)
      | Cons (x, strm') =>
          let val (xs, strm'') = take (n - 1) strm'
          in (x :: xs, strm'') end

  fun drop n strm =
    if n <= 0 then strm
    else
      case force strm of
        Nil => nilstream ()
      | Cons (x, strm') => drop (n - 1) strm'

  fun peek strm =
    case force strm of
      Nil => NONE
    | Cons (x, _) => SOME x

  fun fold reducer init strm =
    case force strm of
      Nil => init
    | Cons (x, strm') => fold reducer (reducer (x, init)) strm'

  fun zip strmA strmB =
    delay (fn () => (
      case (force strmA, force strmB) of
        (Cons (x, strmA'), Cons (y, strmB')) => Cons ((x, y), zip strmA' strmB')
      | _ => Nil
    ))

  fun sequence strms =
    let fun seqHelp [] = seqHelp strms
          | seqHelp (s :: ss) =
              case force s of
                Nil => seqHelp ss
              | Cons (x, s') => Cons (x, delay (fn () => seqHelp (s' :: ss)))
    in delay (fn () => seqHelp strms) end

  fun repeat n x =
    delay (fn () => (
      if n <= 0 then Nil
      else Cons (x, repeat (n - 1) x)
    ))

  fun iterate f x =
    let fun iterHelp NONE = nilstream ()
          | iterHelp (SOME x') = delay (fn () => Cons (x', iterHelp $ f x') )
    in
      delay (fn () => Cons (x, iterHelp $ f x))
    end

  fun generate f =
    delay (fn () => Cons (f (), generate f))

  fun cycle strm =
    let fun cycleHelp strm' =
          case force strm' of
            Nil => cycleHelp strm
          | Cons (x, strm'') => Cons (x, delay (fn () => cycleHelp strm''))
    in delay (fn () => cycleHelp strm) end

  fun fromList xs =
    delay (fn () =>
      case xs of
        [] => Nil
      | (h :: t) => Cons (h, fromList t)
    )

  fun cycleList xs = cycle o fromList $ xs

  fun toList strm =
    case force strm of
      Nil => []
    | Cons (x, strm') => x :: toList strm'
end

val baseSignal = [0, 1, 0, ~1]

structure FFT =
struct
  val baseSignal = Vector.fromList [0, 1, 0, ~1]

  fun deriveBaseSignalGen pos =
    let val idx = ref 0
        val remaining = ref pos
        fun generate () =
          let val _ = if !remaining = 0 then (idx := (!idx + 1) mod 4; remaining := (pos - 1))
                      else (remaining := !remaining - 1)
              val v = Vector.sub (baseSignal, ! idx)
          in v end
    in generate end

  fun decodeStep inputSignal =
    let val sz = length inputSignal
        fun calculatePosition n =
          let
              val generate = deriveBaseSignalGen (n)
              val _ = generate ()
              val sum = List.foldl (fn (d, s) => s + (d * generate ())) 0 inputSignal
          in abs(sum) mod 10 end
    in map (calculatePosition o (curry op+ 1) o (#2)) $ enumerate inputSignal end

  fun decodeUpTo cycles signal =
    if cycles = 0 then signal
    else decodeUpTo (cycles - 1) (decodeStep signal)

  (*
    Here we exploit the following property:

    The second half of the signal is determined solely by a partial sum which can be seen by constructing
    a matrix product like:

    v = [2 4 3 1 5 6]
    M = [
       1  0  0  0  0  0
       0  1  0  0  0  0
      -1  1  1  0  0  0
       0  0  1  1  0  0
       1  0  1  1  1  0
       0 -1  0  1  1  1
    ]

    v' = v * M

    Assuming len(v) is even, we can divide v into two equal parts v = [ v_1 | v_2 ]
    v' similarly will have v' = [v_1' | v_2']

    v_2' is entirely determined by the values in v_2 *AND* if v_2 = [x_n, x_{n-1}, ..., x_2, x_1]
    then v_2' = [..., (x_3 + x_2 + x_1) mod 10, (x_2 + x_1) mod 10, x_1 mod 10].

    Note: abs(.) not needed since we have no negative valuesi n the partial sums

    Knowing the message offset is some subsequence of v_2, we can just apply phases to v_2 to
    get v_2'' after 100 cycles and finding the message using the offset from [v_1 | v_2''].
  *)
  fun decodeStepPartialSums signal =
    let fun partialSums [] = (0, [])
          | partialSums (v :: vs) =
              let val (s, sums) = partialSums vs
                  val s' = (s + v) mod 10
              in  (s', s' :: sums) end
        val (_, output) = partialSums signal
    in output end

  fun decodeUpToPartialSums cycles signal =
    if cycles = 0 then signal
    else decodeUpToPartialSums (cycles - 1) (decodeStepPartialSums signal)
end

fun withInputs fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day16.in")
      val rawInput = withFile filename (removeNewline o Option.valOf o TextIO.inputLine)
      val signal = map (forceParseInt o String.str) $ String.explode rawInput
  in f signal end

fun part1 fOpt = withInputs fOpt (fn signal => (
  let val result = FFT.decodeUpTo 100 signal
  in result end
))

fun part2 fOpt = withInputs fOpt (fn signal => (
  let val (xsl, xsr) = cutInHalf o repeat 10000 $  withInputs NONE id;
      val msgOffset = forceParseInt o concat o map Int.toString $ List.take (signal, 7)
      val result = concat o map Int.toString $ xsl @ (FFT.decodeUpToPartialSums 100 xsr)
  in String.extract (result, msgOffset, SOME 8) end
))

fun main (name, args) =
  let fun exec "part1" x =
          let val result = part1 x
              val _ = print $ "[" ^ String.concatWith ", " (map Int.toString o List.take $ (result, 16)) ^ ", ...]"
              val important = List.take (result, 8)
          in printConcat o map Int.toString $ important end
        | exec "part2" x = print $ part2 x
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, " part [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
