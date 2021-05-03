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

Equations filter `(x1: @list _'13506) `(x2: _'13506 -> bool): @list _'13506 :=
  filter [] _ := [];
  filter (x :: l) p := 
  match ((p x)) with
  | true => (x :: (((filter l) p)))  
  | false => ((filter l) p)
  end.
