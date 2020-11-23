(* Standard ML of New Jersey v110.91 *)

(* Function application for reducing parens a la Haskell *)
infix 3 $
fun f $ x = f x

fun curry f x y = f (x, y)

(* List Helpers *)
fun filter f = List.filter f
fun range (n, m) = if n <= m then n :: range (n + 1, m) else []

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
  let val values = range (172930, 683082)
      val pred = monotonicDigits /\ identicalAdjacentPair
      val results = filter pred values
  in (length results, results) end

fun solvePart2 () =
  let val values = range (172930, 683082)
      val pred = monotonicDigits /\ identicalAdjacentPairOnly
      val results = filter pred values
  in (length results, results) end
