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

Inductive treeS  : Type := 
  | emptyS  
  | leafS : string -> @ treeS   
  | nodeS : (treeS * treeS) % type -> @ treeS .

Equations inorder (x1: treeS): @ list string :=
  inorder (emptyS) := nil;
  inorder (leafS x) := [x];
  inorder (nodeS (tL, tR)) := ((inorder tL)) @ ((inorder tR)).

Equations canonical' (x1: treeS): bool :=
  canonical' (emptyS) := false;
  canonical' (leafS _) := true;
  canonical' (nodeS (tL, tR)) := (canonical' tL) && (canonical' tR).

Equations canonical (x1: treeS): bool :=
  canonical (emptyS) := true;
  canonical (t) := (canonical' t).

Equations normalize (x1: treeS): treeS :=
  normalize (emptyS) := emptyS;
  normalize (leafS x) := (leafS x);
  normalize (nodeS (tL, tR)) := (
  match ((normalize tL), (normalize tR)) with
  | (emptyS, tR') => tR'  
  | (tL', emptyS) => tL'  
  | (tL', tR') => (nodeS (tL', tR'))
  end).

Theorem normalize_correctness : forall T, canonical (normalize T) = true.
Proof.
  intro.
  induction T.
  + auto. (* empty case *)
  + auto. (* leaf case *)
  + case p. intros. eapply (normalize_elim).
    - auto.
    - auto.
    - intros.