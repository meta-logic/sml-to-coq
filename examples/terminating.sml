(* Non-trivial terminating recursions *)

datatype tree = Leaf of int
              | Node of tree * tree

fun treeListSum ([]: tree list): int = 0
  | treeListSum (Leaf(y)::xs) = y + treeListSum xs
  | treeListSum (Node(l,r)::xs) = treeListSum (l::r::xs)

fun remove (x: int, y::l: int list): int list = 
  if x = y then l else y :: remove (x, l)

fun isPermutation ([]: int list, []: int list): bool = true
  | isPermutation (x::l, l') = 
    (List.exists (fn e => e = x) l') andalso isPermutation (l, remove(x, l'))
  | isPermutation _ = false

fun permutations l = case l 
  of [] => []
  | [x] => [[x]]
  | _ => List.foldl (fn (x, acc) => let
      val l_no_x = List.filter (fn e => e <> x) l
      val ps = permutations l_no_x
    in
      acc @ List.map (fn p => x :: p) ps
    end
    ) [] l
;
