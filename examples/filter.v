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

Equations filter {_'13436: Type} (x1: @ list _'13436) (x2: _'13436 -> bool): @ list _'13436 :=
  filter [] _ := ([] : @ list _'13436);
  filter (x :: l) p := 
  match ((p x)) with
  | true => x :: (((filter l) p))  
  | false => ((filter l) p)
  end.
