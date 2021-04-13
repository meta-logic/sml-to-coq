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

Equations posAdd (x1: (Z * Z)%type): Z :=
  posAdd (x, y) := (x + y).

Theorem posAdd_THM: forall ' ((x, y), b), (((posAdd (x, y) = b) /\ ((((x > 0) && (y > 0))) = true)) -> ((((b > x) && (b > y))) = true)).
Admitted.

Equations negAdd (x1: Z) (x2: Z): Z :=
  negAdd x y := (x + y).

Theorem negAdd_THM: forall ' (x, y, b), (((negAdd x y = b) /\ ((((x > 0) && (y > 0))) = true)) -> ((((b > x) && (b > y))) = true)).
Admitted.

Equations trueLen (x1: (@list Z)): Z :=
  trueLen [] := 0;
  trueLen (a :: l) := (1 + ((trueLen l))).

Equations len {_'13565: Type} (x1: (@list _'13565)): Z :=
  len [] := 0;
  len (x :: l') := (1 + ((len l'))).

Theorem len_THM: forall ' (l, result), (((len l = result) /\ ((((((List.length l))) >= 0)) = true)) -> (((result = (((trueLen l))))) = true)).
Admitted.
