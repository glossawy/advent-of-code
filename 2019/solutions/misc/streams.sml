infix 3 $
fun f $ x = f x

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

  val forEach : ('a -> unit) -> 'a stream -> unit

  val map : ('a -> 'b) -> 'a stream -> 'b stream
  val mapWithStream : ('a * 'a stream -> 'b * 'a stream) -> 'a stream -> 'b stream
  val filter : ('a -> bool) -> 'a stream -> 'a stream
  val fold : ('a * 'b -> 'b) -> 'b -> 'a stream -> 'b

  val take : int -> 'a stream -> 'a list * 'a stream
  val drop : int -> 'a stream -> 'a stream

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

  (* fun stdin prompt =
    delay (fn () => Cons ((Option.valOf o readUserInput) prompt, stdin prompt)) *)

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

  fun forEach f strm =
    case force strm of
      Nil => ()
    | Cons (x, strm') => (f x; forEach f strm')

  fun map f strm =
    delay (fn () =>
      case force strm of
        Nil => Nil
      | Cons (v, strm') => Cons (f v, map f strm')
    )

  fun mapWithStream f strm =
    delay (fn () =>
      case force strm of
        Nil => Nil
      | Cons (v, strm') =>
          let val (z, strm'') = f (v, strm')
          in Cons (z, mapWithStream f strm'') end
    )

  fun filter p strm =
    case force strm of
      Nil => delay (fn () => Nil)
    | Cons (v, strm') =>
        if p v
        then delay (fn () => Cons (v, filter p strm'))
        else filter p strm'

  fun take n strm =
    if n <= 0 then ([], strm)
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
