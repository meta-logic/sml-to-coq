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

Inductive test  {_a : Type} : Type := 
  | NoArgs  
  | NotAbstractArg : Z -> @test _a  
  | CombinationArg : (_a * Z * @test _a)%type -> @test _a.

Fixpoint test_ind_princip_proof  (_a : Type) (P:@test _a -> Prop) (Hyp_NoArgs:P NoArgs) (Hyp_NotAbstractArg:(forall p1, P (NotAbstractArg (p1)))) (Hyp_CombinationArg:(forall p1 p2 p3, P p3 -> P (CombinationArg (p1, p2, p3)))) (test_obj:@test _a)  : P test_obj := 
  match test_obj with
  | NoArgs => Hyp_NoArgs  
  | (NotAbstractArg (p1)) => Hyp_NotAbstractArg p1  
  | (CombinationArg (p1, p2, p3)) => Hyp_CombinationArg p1 p2 p3 (test_ind_princip_proof _a P Hyp_NoArgs Hyp_NotAbstractArg Hyp_CombinationArg p3)
  end.

Inductive tree  {_a : Type}  {_b : Type} : Type := 
  | Leaf1 : _a -> @tree _a _b  
  | Leaf2 : _b -> @tree _a _b  
  | Node : (@tree _a _b * _a * _b * @tree _a _b)%type -> @tree _a _b.

Fixpoint tree_ind_princip_proof  (_a _b : Type) (P:@tree _a _b -> Prop) (Hyp_Leaf1:(forall p1, P (Leaf1 (p1)))) (Hyp_Leaf2:(forall p1, P (Leaf2 (p1)))) (Hyp_Node:(forall p1 p2 p3 p4, P p1 -> P p4 -> P (Node (p1, p2, p3, p4)))) (tree_obj:@tree _a _b)  : P tree_obj := 
  match tree_obj with
  | (Leaf1 (p1)) => Hyp_Leaf1 p1  
  | (Leaf2 (p1)) => Hyp_Leaf2 p1  
  | (Node (p1, p2, p3, p4)) => Hyp_Node p1 p2 p3 p4 (tree_ind_princip_proof _a _b P Hyp_Leaf1 Hyp_Leaf2 Hyp_Node p1) (tree_ind_princip_proof _a _b P Hyp_Leaf1 Hyp_Leaf2 Hyp_Node p4)
  end.

Equations treeSum (x1: @tree Z Z): Z :=
  treeSum (Leaf1 x) := x;
  treeSum (Leaf2 x) := x;
  treeSum (Node (t1, a, b, t2)) := ((((treeSum t1) + a) + b) + (treeSum t2)).

Equations treeSumCont' `(x1: Z -> _'13474) (x2: @tree Z Z): _'13474 :=
  treeSumCont' k (Leaf1 x) := (k x);
  treeSumCont' k (Leaf2 x) := (k x);
  treeSumCont' k (Node (t1, a, b, t2)) := ((treeSumCont' (fun _id13490 => 
  match _id13490 with
  | x => ((treeSumCont' (fun _id13491 => 
  match _id13491 with
  | y => (k ((((x + a) + b) + y)))
  end)) t2)
  end)) t1).

Equations treeSumCont (x1: @tree Z Z): Z :=
  treeSumCont t := ((treeSumCont' (fun _id13492 => 
  match _id13492 with
  | x => x
  end)) t).

Lemma testCont : forall t (k : Z -> Z), treeSumCont' k t = k (treeSum t).
  Proof.
    induction t using tree_ind_princip_proof; intros k; try reflexivity.
    simp treeSumCont'. rewrite IHt1. rewrite IHt2. simp treeSum.
    reflexivity.
Qed.

Theorem treeSumeq : forall t, treeSumCont t = treeSum t.
  Proof.
    intros t. simp treeSumCont. rewrite testCont.
    reflexivity.
Qed.

