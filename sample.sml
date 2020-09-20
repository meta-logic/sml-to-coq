(* Partial function *)
fun p_head (x::_) = x

(* Value declarations *)
val x :: l = [1,2,3]
val (a, b) = (5.5, 3.2)

(* Mutual recursion *)
fun even [] = true
  | even (x :: l) = odd l
and odd [] = false
  | odd (x :: l) = even l;

(* Records *)
type r = { name : string, 
           age : int,
           height : real }

fun isBob ({name = "Bob", ...}: r) = true
  | isBob {...} = false

(* Non-structurally terminating *)
datatype tree = Leaf of int
              | Node of tree * tree

fun treeListSum ([]: tree list): int = 0
  | treeListSum (Leaf(y)::xs) = y + treeListSum xs
  | treeListSum (Node(l,r)::xs) = treeListSum (l::r::xs)

(* Non-terminating *)
(* Does not terminate for negative numbers *)
fun fact 0 = 1
  | fact n = n * fact (n-1)

(* Does not terminate for 0 or negative numbers *)
(* Non top level match expression *)
fun collatz 1 = [1]
  | collatz n = n :: (case n mod 2 of
      0 => collatz (n div 2)
    | _ => collatz (3*n + 1) )


fun member (_: int, []: int list): bool = false
  | member (x, y::l) = x=y orelse member (x, l)

fun remove (x: int, y::l: int list): int list = 
  if x = y then l else y :: remove (x, l)
 

fun isPermutation ([]: int list, []: int list): bool = true
  | isPermutation (x::l, l') = member (x, l') andalso isPermutation (l, remove(x, l'))
  | isPermutation _ = false

;
