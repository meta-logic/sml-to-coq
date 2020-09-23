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
  | Leaf : (Z -> (@ tree ))  
  | Node : ((tree * tree) % type -> (@ tree )).

Equations treeListSum (x1: (@ list tree)): Z :=
  treeListSum [] := 0;
  treeListSum ((Leaf y) :: xs) := y + ((treeListSum xs));
  treeListSum ((Node (l, r)) :: xs) := ((treeListSum (l :: r :: xs))).

Equations remove (x1: (Z * (@ list Z))) {H: (exists  y1  y2  y3 , eq (x1) ((y1, y2 :: y3)))}: (@ list Z) :=
  remove (x, (y :: l)) := if x = y then l else y :: ((remove (x, l)));
  remove _ := _.

Equations isPermutation (x1: ((@ list Z) * (@ list Z))): bool :=
  isPermutation ([], []) := true;
  isPermutation ((x :: l), l') := (((((List.existsb (fun  _id13935 => 
  match _id13935 with
  | e => e = x
  end))) l'))) && ((isPermutation (l, ((remove (x, l'))))));
  isPermutation _ := false.

Equations permutations {_''13930: Type} (x1: (@ list _''13930)): (@ list (@ list _''13930)) :=
  permutations l := 
  match l with
  | [] => []  
  | [x] => [[x]]  
  | _ => ((((((List.foldl (fun  _id13936 => 
  match _id13936 with
  | (x, acc) => 
  let l_no_x := ((((List.filter (fun  _id13937 => 
  match _id13937 with
  | e => e <> x
  end))) l)) in 
  let ps := ((permutations l_no_x)) in acc @ ((((List.map (fun  _id13938 => 
  match _id13938 with
  | p => x :: p
  end))) ps))
  end))) [])) l))
  end.
