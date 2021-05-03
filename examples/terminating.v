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

Generalizable All Variables.

Inductive tree  : Type := 
  | Leaf : Z -> @tree   
  | Node : (tree * tree)%type -> @tree .

Equations treeListSum (x1: @list tree): Z :=
  treeListSum [] := 0;
  treeListSum ((Leaf y) :: xs) := (y + (treeListSum xs));
  treeListSum ((Node (l, r)) :: xs) := (treeListSum ((l :: (r :: xs)))).

Equations remove (x1: (Z * @list Z)%type) {H: exists y1 y2 y3 , eq (x1) ((y1, y2 :: y3))}: @list Z :=
  remove (x, (y :: l)) := if (x = y) then l else (y :: (@remove (x, l) _));
  remove _ := _.
Admit Obligations.

Equations isPermutation (x1: (@list Z * @list Z)%type): bool :=
  isPermutation ([], []) := true;
  isPermutation ((x :: l), l') := (((List.existsb (fun _id13974 => 
  match _id13974 with
  | e => (e = x)
  end)) l')) && (isPermutation (l, (@remove (x, l') _)));
  isPermutation _ := false.

Equations permutations `(x1: @list _''13962): @list @list _''13962 :=
  permutations l := 
  match l with
  | [] => []  
  | [x] => [[x]]  
  | _ => (((List.foldl (fun _id13975 => 
  match _id13975 with
  | (x, acc) => 
  let l_no_x := ((List.filter (fun _id13976 => 
  match _id13976 with
  | e => (e <> x)
  end)) l) in 
  let ps := (permutations l_no_x) in (acc @ ((List.map (fun _id13977 => 
  match _id13977 with
  | p => (x :: p)
  end)) ps))
  end)) []) l)
  end.
