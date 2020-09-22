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

Equations lengthE {_a: Type} {_a: Type} (x1: @ evenList _a): Z :=
  lengthE ENil := 0;
  lengthE (ECons (_, l)) := ((lengthO : @ oddList _a -> int) l)
with lengthO {_a: Type} {_a: Type} (x1: @ oddList _a): Z :=
  lengthO (OCons (_, l)) := ((lengthE : @ evenList _a -> int) l).

Equations even {_'13680: Type} (x1: @ list _'13680): bool :=
  even [] := true;
  even (x :: l) := (odd l)
with odd {_'13680: Type} (x1: @ list _'13680): bool :=
  odd [] := false;
  odd (x :: l) := (even l).

Equations f (x1: Z): Z :=
  f x := ((g x)) + 10
with g (x1: Z): Z :=
  g x := x * 10.
