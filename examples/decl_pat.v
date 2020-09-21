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

Definition z := 5.

Definition L := [8].

Definition x := 
  match [1; 2; 3] with
  (x::l) => x
  | _ => patternFailure
  end.

Definition l := 
  match [1; 2; 3] with
  (x::l) => l
  | _ => patternFailure
  end.

Definition a := 
  match (5.5%float, 3.2%float) with
  (a, b) => a
  end.

Definition b := 
  match (5.5%float, 3.2%float) with
  (a, b) => b
  end.

Fail Equations six (x1: _'13426): Z :=
  six x := 
  let x := 6 in x.

Fail Equations head (x1: @ list _'13437): _'13437 :=
  head x := 
  let h {_'13437 : Type} := 
  match (x : @ list _'13437) with
  (h::t) => h
  | _ => patternFailure
  end in 
  let t := 
  match (x : @ list _'13437) with
  (h::t) => t
  | _ => patternFailure
  end in h.

