Require Import intSml.
Require Import listSml.
Require Import realSml.
Require Import stringSml.
Require Import charSml.
Require Import boolSml.
Require Import optionSml.
Require Import listPairSml.
Require Import notationsSml.
From Equations Require Import Equations.

Inductive tree  : Type := 
  | Leaf : Z -> (@ tree )  
  | Node : (tree * tree) % type -> (@ tree ).

Equations treeListSum (x1: (@ list tree)): Z :=
  treeListSum [] := 0;
  treeListSum ((Leaf y) :: xs) := y + (treeListSum xs);
  treeListSum ((Node (l, r)) :: xs) := (treeListSum (l :: r :: xs)).

Equations remove (x1: (Z * (@ list Z)) % type) {H: (exists  y1  y2  y3 , eq (x1) (tuple y1 y2 :: y3))}: (@ list Z) :=
  remove (x, (y :: l)) := if x = y then l else y :: (remove (x, l));
  remove _ := _.

Equations isPermutation (x1: ((@ list Z) * (@ list Z)) % type): bool :=
  isPermutation ([], []) := true;
  isPermutation ((x :: l), l') := (((List.existsb (fun  _id13967 => 
  match _id13967 with
  | e => e = x
  end)) l')) && (isPermutation (l, (remove (x, l'))));
  isPermutation _ := false.

Equations permutations {_''13962: Type} (x1: (@ list _''13962)): (@ list (@ list _''13962)) :=
  permutations l := 
  match l with
  | [] => []  
  | [x] => [[x]]  
  | _ => (((List.foldl (fun  _id13968 => 
  match _id13968 with
  | (x, acc) => 
  let l_no_x := ((List.filter (fun  _id13969 => 
  match _id13969 with
  | e => e <> x
  end)) l) in 
  let ps := (permutations l_no_x) in acc @ ((List.map (fun  _id13970 => 
  match _id13970 with
  | p => x :: p
  end)) ps)
  end)) []) l)
  end.
