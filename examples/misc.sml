(** Simple function *)
fun length [] = 0
| length ( x :: l ) = 1 + length l

(** Record types *)
type r = { name : string, 
           age : int }
fun isBob ({name = "Bob", ...}: r) = true
  | isBob {...} = false
  
(** Infix functions *)
infix F
fun op F (x, y) = x*x + y
val f = op F
val x = 5 F 2
val y = op F (2, 3)
   
(** Nested pattern matching *)
fun filter [] _ = []
  | filter (x :: l) p = case (p x) 
    of true => x :: (filter l p)
     | false => filter l p

(** Mutual recursion *)
datatype 'a evenList = ENil
                     | ECons of 'a * 'a oddList
and 'a oddList = OCons of 'a * 'a evenList

fun lengthE (ENil: 'a evenList) = 0
  | lengthE (ECons (_, l)) = lengthO l
and lengthO (OCons (_, l)) = lengthE l

(** Function contracts *)
(!! 
  posAdd(x, y) ==> b;
  REQUIRES: x > 0 andalso y > 0;
  ENSURES: b > x andalso b > y; 
!!)
fun posAdd(x, y) = x + y;

(** Partial function *)
fun hd_sum ((a,b)::l) ((a',b')::l') = a + b + a' + b'
  | hd_sum ((a,b)::l) l'            = a + b
  | hd_sum l          ((a',b')::l') = a' + b'

(** Module system *)
signature PAIR =
sig
  type t1
  type t2
  type t = t1 * t2
  val default : unit -> t
end

structure IntString : PAIR =
struct
  type t1 = int
  type t2 = string
  type t = t1 * t2
  fun default () = (0, "")
end

functor Example (Pair : PAIR) =
struct
  val (a, b) = Pair.default ()
end

structure S = Example (IntString) 

(** Non-terminating (typechecks but not accepted) *)
fun collatz 1 = [1]
  | collatz n = n :: (case n mod 2 of
      0 => collatz (n div 2)
    | _ => collatz (3*n + 1) )
;
