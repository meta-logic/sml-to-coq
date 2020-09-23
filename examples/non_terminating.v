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

Equations loop1 {_'13723: Type} (x1: Z): _'13723 :=
  loop1 x := (loop1 (x + 1)).

Equations loop2 {_'13733: Type} (x1: Z): _'13733 :=
  loop2 x := (loop2 (x - 1)).

Equations loop3 {_'13749: Type} {_'13750: Type} (x1: (@ list _'13749)) {H: (exists  y1  y2 , eq (x1) (y1 :: y2))}: _'13750 :=
  loop3 (x :: l) := (loop3 (l @ [x]));
  loop3 _ := _.

Equations fact (x1: Z): Z :=
  fact 0 := 1;
  fact n := n * (fact (n - 1)).

Equations collatz (x1: Z): (@ list Z) :=
  collatz 1 := [1];
  collatz n := n :: (
  match n mod 2 with
  | 0 => (collatz (n div 2))  
  | _ => (collatz (3 * n + 1))
  end).
