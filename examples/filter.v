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

Equations filter {_'13425: Type} (x1: @ list _'13425) (x2: _'13425 -> bool): @ list _'13425 :=
  filter [] _ := ([] : @ list _'13425);
  filter (x :: l) p := 
  match ((p x)) with
  | true => x :: (((filter l) p))  
  | false => ((filter l) p)
  end;
  filter _ _ := _.
