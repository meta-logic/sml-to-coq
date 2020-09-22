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
  inorder emptyS := nil;
  inorder (leafS x) := [x];
  inorder (nodeS (tL, tR)) := ((inorder tL)) @ ((inorder tR)).

Equations normal' (x1: treeS): bool :=
  normal' emptyS := false;
  normal' (leafS _) := true;
  normal' (nodeS (tL, tR)) := (normal' tL) && (normal' tR).

Equations normal (x1: treeS): bool :=
  normal emptyS := true;
  normal t := (normal' t).

Equations normalize (x1: treeS): treeS :=
  normalize emptyS := emptyS;
  normalize (leafS x) := (leafS x);
  normalize (nodeS (tL, tR)) := (
  match ((normalize tL), (normalize tR)) with
  | (emptyS, tR') => tR'  
  | (tL', emptyS) => tL'  
  | (tL', tR') => (nodeS (tL', tR'))
  end).
