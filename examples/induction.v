Require Import intSml.
Require Import listSml.
Require Import realSml.
Require Import stringSml.
Require Import charSml.
Require Import boolSml.
Require Import optionSml.
Require Import listPairSml.
Require Import notationsSml.
Require Import Lia.
From Equations Require Import Equations.

Generalizable All Variables.

Inductive tree  {_a : Type}  {_b : Type} : Type := 
  | Leaf1 : _a -> @tree _a _b  
  | Leaf2 : _b -> @tree _a _b  
  | Node : (@tree _a _b * _a * _b * @tree _a _b)%type -> @tree _a _b.

Theorem tree_ind_princip: (forall  (_a _b : Type) (P:@tree _a _b -> Prop), (forall p1, P (Leaf1 (p1))) -> (forall p1, P (Leaf2 (p1))) -> (forall p1 p2 p3 p4, P p1 -> P p4 -> P (Node (p1, p2, p3, p4))) -> (forall tree_obj, P tree_obj)).
Admitted.

Equations treeSum (x1: @tree Z Z): Z :=
  treeSum (Leaf1 x) := x;
  treeSum (Leaf2 x) := x;
  treeSum (Node (t1, a, b, t2)) := ((((treeSum t1) + a) + b) + (treeSum t2)).

Equations treeSumCont' `(x1: Z -> _'13471) (x2: @tree Z Z): _'13471 :=
  treeSumCont' k (Leaf1 x) := (k x);
  treeSumCont' k (Leaf2 x) := (k x);
  treeSumCont' k (Node (t1, a, b, t2)) := ((treeSumCont' (fun _id13487 => 
  match _id13487 with
  | x => ((treeSumCont' (fun _id13488 => 
  match _id13488 with
  | y => (k ((((x + a) + b) + y)))
  end)) t2)
  end)) t1).

Equations treeSumCont (x1: @tree Z Z): Z :=
  treeSumCont t := ((treeSumCont' (fun _id13489 => 
  match _id13489 with
  | x => x
  end)) t).

Lemma testCont : forall t (k : Z -> Z), treeSumCont' k t = k (treeSum t).
  Proof.
    induction t using tree_ind_princip; intros k; try reflexivity.
    simp treeSumCont'. rewrite IHt1. rewrite IHt2. simp treeSum.
    reflexivity.
Qed.

Theorem treeSumeq : forall t, treeSumCont t = treeSum t.
  Proof.
    intros t. simp treeSumCont. rewrite testCont.
    reflexivity.
Qed.



