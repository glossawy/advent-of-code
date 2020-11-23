(* Standard ML of New Jersey v110.91 *)

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

fun curry f x y = f (x, y)

(* Quick Suspension Library, mostly for fun *)
type 'a susp = unit -> 'a

fun force t = t ()
fun delay (f : 'a susp) =
  let exception Impossible
      val memo : 'a susp ref = ref (fn () => raise Impossible)
      fun suspended () =
        let val r = f () in memo := (fn () => r); r end
  in memo := suspended; fn () => (!memo) () end

(* Quick Lazy Int Stream library based on Suspension, mostly for fun *)
datatype intstream = Nil | Cons of int * intstream susp

fun ifilter f istrm =
  case force istrm of
    Nil => delay (fn () => Nil)
  | Cons (x, istrm') =>
      if f x then delay (fn () => Cons (x, ifilter f istrm'))
      else ifilter f istrm'

fun irange (n, m) =
  let fun rangeHelper i = if i > Option.valOf m then Nil else Cons (i, delay (fn () => rangeHelper $ i + 1))
  in delay (fn () => rangeHelper n) end

fun istreamToList istrm =
  case force istrm of
    Nil => []
  | Cons (x, istrm') => x :: istreamToList istrm'

(* List Manipulation Helpers *)
fun adjacentPairs [] = []
  | adjacentPairs xs = ListPair.zip (xs, tl xs)

fun takeWhile _ [] = []
  | takeWhile f (x :: xs) = if f x then x :: takeWhile f xs else []

fun strides _ [] = []
  | strides eq xs =
      let val stride = takeWhile (curry eq $ hd xs) xs
      in stride :: strides eq (List.drop (xs, length stride)) end

fun compress _ [] = []
  | compress eq xs =
      map (fn ys => (hd ys, length ys)) $ strides eq xs

(* Int Manipulation Helpers *)
val forceParseInt = Option.valOf o Int.fromString

val explodeInt =
  map (forceParseInt o Char.toString) o String.explode o Int.toString

val implodeInt =
  concat o map Int.toString

fun withDigits f = f o explodeInt

(* Predicate Logic and Filters *)
infix 5 /\
fun p /\ q = (fn x => p x andalso q x)

fun monotonicDigits i = withDigits (List.all op<= o adjacentPairs) i
fun identicalAdjacentPair i = withDigits (List.exists op= o adjacentPairs) i
fun identicalAdjacentPairOnly i =
  let fun isPairCount (_, 2) = true
        | isPairCount _ = false
  in withDigits (List.exists isPairCount o compress op=) i end

(* Solvers *)
fun solvePart1 () =
  let val istrm = irange (172930, SOME 683082)
      val pred = monotonicDigits /\ identicalAdjacentPair
      val results = istreamToList $ ifilter pred istrm
  in (length results, results) end

fun solvePart2 () =
  let val istrm = irange (172930, SOME 683082)
      val pred = monotonicDigits /\ identicalAdjacentPairOnly
      val results = istreamToList $ ifilter pred istrm
  in (length results, results) end
