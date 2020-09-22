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

Inductive evenList  {_a : Type} : Type := 
  | ENil  
  | ECons : (_a * @ oddList _a) % type -> @ evenList _a
with oddList  {_a : Type} : Type := 
  | OCons : (_a * @ evenList _a) % type -> @ oddList _a.

Equations lengthE {'a: Type} (x1: @ evenList 'a): Z :=
  lengthE (ENil) := 0;
  lengthE (ECons (_, l)) := (lengthO (l : @ oddList 'a));
  lengthE (_) := _
with lengthO (x1: @ oddList 'a): Z :=
  lengthO (OCons (_, l)) := (lengthE l).

Equations even {_'13456: Type} (x1: @ list _'13456): bool :=
  even ([]) := true;
  even ((x :: l)) := (odd (l : @ list _'13456));
  even (_) := _
with odd (x1: @ list _'13456): bool :=
  odd ([]) := false;
  odd ((x :: l)) := (even l);
  odd (_) := _.

Equations f (x1: Z): Z :=
  f (x) := ((g x)) + 10
with g (x1: Z): Z :=
  g (x) := x * 10.