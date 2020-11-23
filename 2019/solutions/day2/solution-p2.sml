(* Standard ML of New Jersey v110.91 *)

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
in
  fun maximum f l = extremum GREATER f l
  fun minimum f l = extremum LESS f l
end

local
  val stdout = TextIO.stdOut
  val stderr = TextIO.stdErr
  fun writeOut pipe s = TextIO.output (pipe, s ^ "\n")
in
  val print = writeOut stdout
  val printConcat = print o concat
  val printErr = writeOut stderr
  val printErrConcat = printErr o concat
end

fun id x = x
fun const k = (fn _ => k)
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y

structure Heap =
struct
  type loc = int
  type 'a t = 'a ref vector

  local
    structure V = Vector
    fun skipFirst f =
      let val flag = ref true
      in fn (e, a) => if ! flag then (flag := false; e) else f (e, a) end

    fun concatVectorWith d v =
      V.foldl (skipFirst (fn (e, a) => a ^ d ^ e)) "" v
  in
    fun fromList (l : 'a list) : 'a t = (V.fromList o map ref) l
    fun size (h : 'a t) = V.length h

    fun get (h : 'a t) (l : loc) : 'a = !(V.sub (h, l))
    fun set (h : 'a t) (l : loc) (v : 'a) : unit = V.sub (h, l) := v

    fun toString (f : 'a -> string) (h : 'a t) =
      let fun deref (ref v) = v
      in concat ["[", concatVectorWith ", " (Vector.map (f o deref) h), "]"] end
  end
end


structure Either =
struct
  exception Either

  datatype ('l, 'r) t = LEFT of 'l | RIGHT of 'r

  fun map f _ (LEFT v) = LEFT (f v)
    | map _ f (RIGHT v) = RIGHT (f v)

  fun mapL f = map f id
  fun mapR f = map id f

  fun valueOfL (LEFT v) = v
    | valueOfL _ = raise Either

  fun valueOfR (RIGHT v) = v
    | valueOfR _ = raise Either
end

type environment = (string * int) list

exception FindSolution
exception HaltProgram
exception UnknownOpCodeError of Heap.loc

structure Term =
struct
  datatype t =
      Const of int
    | Var of string
    | Sum of t * t
    | Product of t * t

  fun size term =
    case term of
      Sum (t1, t2) => 1 + size t1 + size t2
    | Product (t1, t2) => 1 + size t1 + size t2
    | _ => 1

  fun equal (t1, t2) =
    case (t1, t2) of
      (Const c, Const c') => c = c'
    | (Var x, Var x') => String.compare (x, x') = EQUAL
    | (Sum (st1, st2), Sum (st1', st2')) => equal (st1, st1') andalso equal (st2, st2')
    | (Product (st1, st2), Product (st1', st2')) => equal (st1, st1') andalso equal (st2, st2')
    | _ => false

  fun compare (t1, t2) =
    case Int.compare (size t1, size t2) of
      EQUAL => if equal (t1, t2) then EQUAL else LESS
    | ord => ord

  fun negate t =
    case t of
      Const c => Const (~c)
    | Var x => Product (Const ~1, Var x)
    | Sum (st1, st2) => Sum (negate st1, negate st2)
    | Product _ => Product (Const ~1, t)

  fun simplify term =
    let val minTerm = Option.valOf o minimum compare
        fun simplify_commutativity tcon t (st1, st2) =
          let val commuteL = tcon (st1, t)
              val commuteR = tcon (st2, t)
              val candidate1 = tcon (simplify commuteL, st2)
              val candidate2 = tcon (st1, simplify commuteR)
          in minTerm [term, candidate1, candidate2] end

        fun simplify_distributivity t (st1, st2) =
          let val st' = (Product (t, st1), Product (t, st2))
          in minTerm [term, simplify (Sum st')] end
    in
    case term of
      Const c => Const c
    | Var x => Var x
    | Sum (t1, t2) => (
        case (simplify t1, simplify t2) of
          (Const c, Const c') => Const (c + c')
          (* Commutativity of Addition *)
        | (Sum (st1, st2), t2' as Const c) =>
            simplify_commutativity Sum t2' (st1, st2)
        | (t1' as Const c, Sum (st1, st2)) =>
            simplify_commutativity Sum t1' (st1, st2)
          (* No Simplification *)
        | (t1', t2') => Sum (t1', t2')
      )
    | Product (t1, t2) => (
        case (simplify t1, simplify t2) of
          (Const c, Const c') => Const (c * c')
          (* Distributive Property *)
        | (t1' as Const c, Sum (st1, st2)) =>
            simplify_distributivity t1' (st1, st2)
        | (Sum (st1, st2), t2' as Const c) =>
            simplify_distributivity t2' (st1, st2)
          (* Commutativity of Multiplication *)
        | (Product (st1, st2), t2' as Const c) =>
            simplify_commutativity Product t2' (st1, st2)
        | (t1' as Const c, Product (st1, st2)) =>
            simplify_commutativity Product t1' (st1, st2)
          (* No Simplification *)
        | (t1', t2') => Product (t1', t2')
      )
    end

  fun toString term =
    case term of
      Const c => Int.toString c
    | Var x => x
    | Sum (t1, t2) => concat ["(", toString t1, " + ", toString t2, ")"]
    | Product (t1, t2) => concat [toString t1, " * ", toString t2]
end

local
  val freshvar_counter = ref 0
in
  fun freshvar () =
    let val fv = "Z_" ^ (Int.toString o op!) freshvar_counter
    in
      (freshvar_counter := !freshvar_counter + 1; fv)
    end
end


datatype state = State of Term.t Heap.t * environment

fun concatWith d v =
  List.foldl (fn (e, a) => if size a = 0 then e else a ^ d ^ e) "" v

fun envToString (e : environment) =
  let fun mapper (x, v) = concat [x, " = ", Int.toString v]
  in (concatWith ", " o List.map mapper) e end

fun getTermAt (State (h, _)) = Heap.get h
fun setTermAt (State (h, _)) = Heap.set h
fun getVar (State (_, e)) x =
  let val opt = List.find (fn (x', _) => x = x') e
  in Option.map (fn (_, v) => v) opt end

local
  open Term
in
  fun evalTerm s term =
    let open Either
        fun performBinOp pcon f t1 t2 =
          let val r1 = evalTerm s t1
              val r2 = evalTerm s t2
          in
            (*
              The goal here is to evaluate the term as much as possible,
              possibly simplifying.
            *)
            case r1 of
              LEFT v1 => (
                case r2 of
                  LEFT v2 => LEFT (f (v1, v2))
                | RIGHT t2' => RIGHT (pcon (Const v1, t2'))
              )
            | RIGHT t1' => (
                case r2 of
                  LEFT v2 => RIGHT (pcon (t1', Const v2))
                | RIGHT t2' => RIGHT (pcon (t1', t2'))
              )
          end
    in
      case term of
        Var name => (
          case getVar s name of
            SOME v => LEFT v
          | NONE => RIGHT term
        )
      | Const c => LEFT c
      | Sum (t1, t2) => performBinOp Sum op+ t1 t2
      | Product (t1, t2) => performBinOp Product op* t1 t2
    end
end

fun evalTermToValue s t = (Either.valueOfL o evalTerm s) t
fun evalTermToTerm s t = (Either.valueOfR o evalTerm s) t

(*
  The intuition is to track what locations are affected by what other
  locations at what particular times, each position should end up with
  a representation of it's final value as sums and products of variables
  which can then be assigned the initial value for each location. This
  allows us to calculate a result and gives us enough information to figure
  out how to change a value at one location into some other desired value
  as in Part 2 of the challenge.

  I expect this to be guaranteed to work as long as the values being
  tinkered with are not values relating to where the effects of computations
  go (the 4th component of any instruction), which I believe determine the values of
  all other locations, though I have not gone through the effort to prove this.
*)

fun eval s i =
  let
    fun get delta = getTermAt s (i + delta)
    val get_eval = evalTermToValue s o get
    val getget = getTermAt s o get_eval
    fun update v  = setTermAt s (get_eval 3) v
    fun performOp f = f (getget 1, getget 2)
    val _ =
      case get_eval 0 of
        1 => update (performOp Term.Sum)
      | 2 => update (performOp Term.Product)
      | 99 => raise HaltProgram
      | _ => ()
  in
    eval s (i + 4)
  end

(* Terribly Messy Solver

   The intuition is creating a linear function to investigate, but really
   just having the formula allows for finding the root and thus the closest
   integer x value with the smallest positive integer y value. This was just
   quickly thrown together for fun.
*)
fun findSolutions xvar (s, l) term on_solution =
  let
    open Either
    fun loop x =
      let val env = [(xvar, x)]
          val state = State (Heap.fromList [], env)
          val either_res = evalTerm state term
      in
        Either.map (curry on_solution x) (const ()) either_res;
        if x - s < l then loop (x + 1) else ()
      end
  in loop s end

fun printState (s as State (h, e)) =
  let
      val heapstring = Heap.toString Term.toString h
      val envstring = envToString e
      val zeroth_term = getTermAt s 0
      val value = evalTermToValue s zeroth_term
      val (env_h :: (x1, v1) :: (x2, v2) :: env_t) = e
      val s' = State (h, env_h :: env_t)
      val zeroth_term' = (Term.simplify o evalTermToTerm s') zeroth_term
  in
    (
      print heapstring;
      print envstring;
      print "";
      printConcat [Term.toString zeroth_term, " = ", Int.toString value];
      print "";
      printConcat [
            "With missing info the equation for location 0 is:\n",
            Term.toString zeroth_term', "\n\n",
            "Sample Solutions:"
      ];
      (* Do some solving, this is all very particular to the problem and not generalized *)
      (
        let open Term
            fun print_solutions yvar st =
              let val xvar = if String.compare (yvar, x1) = EQUAL then x2 else x1
                  fun on_solution (x, y) =
                    printConcat ["(", Int.toString x, ", ", Int.toString y, ")"]
              in printConcat ["(", xvar, ", ", yvar, ")"]; findSolutions xvar (65, 5) (Sum (Const 19690720, Term.negate st)) on_solution end
        in
          case zeroth_term' of
            Sum (Var y, st2) => print_solutions y st2
          | Sum (st1, Var y) => print_solutions y st1
          | _ => raise FindSolution
        end
      )
    )
  end


(*
    Parsing and Main
 *)

val isOpCodeDelim = curry op= #","
val parseInput =
  let open Term
      val forceParseInt = Option.valOf o Int.fromString
      fun processInitialState ((h, e) : Term.t ref list * (string * int) list) (tokens : string list) : state =
        case tokens of
          [] => State (Vector.fromList (rev h), rev e)
        | t :: ts =>
          let val x = freshvar ()
              val st' = (ref (Var x) :: h, (x, forceParseInt t) :: e)
          in processInitialState st' ts end
  in
    processInitialState ([], []) o (String.tokens isOpCodeDelim)
  end

fun main (name : string, args: string list) =
  let val filename = (case args of f :: _ => f | _ => "../../inputs/day2.in")
      val fid = TextIO.openIn filename
      val s : state = (Option.valOf o Option.map parseInput o TextIO.inputLine) fid

      fun wrapUp () =
        (printState s; OS.Process.success)

      fun fail msg =
        (printErrConcat msg; OS.Process.failure)
  in
    eval s 0
    handle UnknownOpCodeError l => fail ["Unknown instruction at location ", Int.toString l]
         | HaltProgram => wrapUp ()
  end
