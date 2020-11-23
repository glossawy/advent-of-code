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

(* Basic useful functions *)
fun id x = x
fun const k = (fn _ => k)
fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y
fun flip f (y, x) = f (x, y)

val forceParseInt = Option.valOf o Int.fromString
fun flatten [] = []
  | flatten (xs :: xss) = xs @ flatten xss

structure StringUtil =
struct
  fun delete withinSet =
    let fun translator c =
          if Char.contains withinSet c then ""
          else String.str c
    in String.translate translator end

  val compact = delete " "
end

(* IntInf specialized gcd and lcm for this problem specifically *)
fun gcd (a : IntInf.int) (b : IntInf.int) : IntInf.int =
  if a < b then gcd b a
  else
    case (a, b) of
      (a, 0) => a
    | _ => gcd b (a mod b)

fun lcm (a : IntInf.int) (b : IntInf.int) : IntInf.int = (a * b) div (gcd a b)


structure Vect3 =
struct
  datatype t = Vect3 of int * int * int

  fun make p = Vect3 p
  fun unmake (Vect3 p) = p

  val zero  = make (0, 0, 0)

  fun equal (Vect3 (x, y, z) , Vect3 (x', y', z')) = x = x' andalso y = y' andalso z = z'
  fun toString (Vect3 (x, y, z)) = concat ["Vect(", Int.toString x, ", ", Int.toString y, ", ", Int.toString z, ")"]

  fun scale scalar (Vect3 (x, y, z)) = make (x * scalar, y * scalar, z * scalar)
  fun add (Vect3 (vx, vy, vz)) (Vect3 (wx, wy, wz)) = make (vx + wx, vy + wy, vz + wz)
  fun sub v1 v2 = add v1 $ scale ~1 v2
end

structure Moon =
struct
  datatype moon = Moon of { pos : Vect3.t, vel : Vect3.t }

  fun make pos = Moon { pos = pos, vel = Vect3.zero }
  fun equal (Moon { pos, vel }, Moon { pos = pos', vel = vel' }) = List.all (Vect3.equal) [(pos, pos'), (vel, vel')]

  fun influenceWith (cur as Moon { pos = cPos, vel = cVel}) (influence as Moon { pos = iPos, ... }) =
    let val (x, y, z) = Vect3.unmake $ Vect3.sub iPos cPos
        val deltaVel = Vect3.make $ (Int.sign x, Int.sign y, Int.sign z)
    in Moon { pos = cPos, vel = Vect3.add cVel deltaVel } end

  fun applyVelocity (Moon { pos, vel }) = Moon { pos = Vect3.add pos vel, vel = vel }

  local fun absoluteSum (Vect3.Vect3 (x, y, z)) = List.foldl op+ 0 o List.map abs $ [x, y, z]
  in
    fun potentialEnergy (Moon { pos, ...}) = absoluteSum pos
    fun kineticEnergy (Moon { vel, ...}) = absoluteSum vel
  end

  fun totalEnergy moon = potentialEnergy moon * kineticEnergy moon

  fun step n moons =
    if n <= 0 then moons
    else
      let fun applyInfluence moon =
            List.foldl (flip $ uncurry influenceWith) moon moons
          val moons' = map (applyVelocity o applyInfluence) moons
      in step (n - 1) moons' end

  (*
    Suppose we start with:
      m_i = { position = (px_i, py_i, pz_i), velocity = (vx_i, vy_i, vz_i) }
      for 0 < i <= 4

      And after some number of steps we say we have:
        m_i' = { position = (px_i', py_i', pz_i'), velocity = (vx_i', vy_i', vz_i') }
        for 0 < i <= 4

      Then we can algorithmically find the periods T_x, T_y, T_z where
        T_x = minimum number steps to find (px_i = px_i' AND vx_i = v_i') for all 0 < i <= 4
        T_y = same for y components
        T_z = same for z components
      NOTE: Although we are using m_i' without specifying how many steps have been taken, we should assume
            it possible, if not extremely likely, that T_x =/= T_y =/= T_z.

      With these component periods we need to find the period of the entire system, T.

      T must necessarily be some multiple of T_x, some multiple of T_y, and some multiple of T_z. That is,
      T must be divisible by T_x, T_y, and T_z since T is effecively the conjunction of the conditions stated
      earlier.

      Finding the minimum such T is equivalent to finding the least common multiple of T_x, T_y, T_z:
        min(T) = lcm(T_x, T_y, T_z)
  *)
  fun findPeriod moons =
    let val (periods as (xref, yref, zref)) = (ref NONE, ref NONE, ref NONE)

        fun allFound () = List.all (Option.isSome o op!) $ [xref, yref, zref]
        fun setOrNoop r v = r := (SOME o Option.getOpt) (!r, v)

        fun getEqualComponents (Moon { pos, vel }, Moon { pos = pos', vel = vel' }) =
          let val (Vect3.Vect3 (px, py, pz), Vect3.Vect3 (vx, vy, vz)) = (pos, vel)
              val (Vect3.Vect3 (px', py', pz'), Vect3.Vect3 (vx', vy', vz')) = (pos', vel')
          in (px = px' andalso vx = vx', py = py' andalso vy = vy', pz = pz' andalso vz = vz') end

        fun performUpdate steps moons' =
          let fun combine ((x, y ,z), (x', y', z')) = (x andalso x', y andalso y', z andalso z')
              val equalityVecs = map getEqualComponents $ ListPair.zip (moons, moons')
              val (xcond, ycond, zcond) = List.foldl combine (true, true, true) equalityVecs
          in
            if xcond then setOrNoop xref steps else ();
            if ycond then setOrNoop yref steps else ();
            if zcond then setOrNoop zref steps else ()
          end

        fun search steps moons' =
          let val _ = performUpdate steps moons'
              val moons'' = step 1 moons'
          in if allFound () then () else search (steps + 1) moons'' end

        val _ = search 1 (step 1 moons)

        val (SOME xperiod, SOME yperiod, SOME zperiod) = (!xref, !yref, !zref)
        val periods = [xperiod, yperiod, zperiod]
        val systemPeriod = List.foldl (uncurry lcm) (Int.toLarge 1) $ map Int.toLarge periods
    in systemPeriod end

  fun systemEnergy moons =
    List.foldl op+ 0 o List.map totalEnergy $ moons
end


fun parseMoon line =
  let open String
      open StringUtil
      fun toValue s =
        let val [_, value] = tokens (curry op= #"=") s
        in forceParseInt value end
      fun toMoon (x :: y :: z :: _) = Moon.make o Vect3.make $ (x, y, z)
        | toMoon _ = raise Fail $ "Not enough values in " ^ line
      val components = List.map compact o tokens (curry op= #",") o delete "<>" $ line
  in toMoon o List.map toValue $ components end

fun withInputs fOpt f =
  let val filename = Option.getOpt (fOpt, "../../inputs/day12.in")
      val rawInput = withFile filename readAllLines
  in f $ map parseMoon rawInput end


fun part1 fOpt = withInputs fOpt (fn moons =>
  let val moons' = Moon.step 1000 moons
  in (moons', Moon.systemEnergy moons') end
)

fun part2 fOpt = withInputs fOpt Moon.findPeriod

fun main (name, args) =
  let fun exec "part1" x =
            let val (_, energy) = part1 x
            in print o Int.toString $ energy end
        | exec "part2" x = print o IntInf.toString $ part2 x
        | exec s _ = raise Fail $ concat ["Invalid part, must be part1 or part2"]
  in
   case args of
      [part, file] => exec part $ SOME file
    | [part] => exec part $ NONE
    | _ => raise Fail $ concat ["usage: ", name, " part [infile]"]
  end
  handle Fail s => (printErr s; OS.Process.exit(OS.Process.failure))
val main : string * string list -> unit = main
