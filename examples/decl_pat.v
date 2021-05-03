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

Definition e {_'13405 : Type} := ([] : @list _'13405).

Definition opt {_'13408 : Type} := (None : @option _'13408).

Definition z := 5.

Definition L := ["hello"].

Definition x := 
  match [1; 2; 3] with
  (x :: l) => x
  | _ => patternFailure
  end.

Definition l := 
  match [1; 2; 3] with
  (x :: l) => l
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

Definition y := 
  match [[4; 3; 2]] with
  [(y :: l')] => y
  | _ => patternFailure
  end.

Definition l' := 
  match [[4; 3; 2]] with
  [(y :: l')] => l'
  | _ => patternFailure
  end.

Equations six `(x1: _'13449): Z :=
  six x := 
  let x := 6 in x.

Equations head `(x1: @list _'13460): _'13460 :=
  head x := 
  let h := 
  match x with
  (h :: t) => h
  | _ => patternFailure
  end in 
  let t := 
  match x with
  (h :: t) => t
  | _ => patternFailure
  end in h.

Equations singleton `(x1: _'13474): @list _'13474 :=
  singleton x := 
  let e {_'13469 : Type} := ([] : @list _'13469) in (x :: e).
