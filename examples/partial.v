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

Fail Equations p_head {_'13414: Type} (x1: @ list _'13414) {H: (exists  y1  y2 , x1 = y1 :: y2)}: _'13414 :=
  p_head (x :: _) := (x : _'13414).

Fail Equations hd_sum (x1: @ list (Z * Z) % type) (x2: @ list (Z * Z) % type) (x3: Z) {H: ((((exists  y1  y2 , x1 = y1 :: y2) /\ (exists  y1  y2 , x2 = y1 :: y2)) \/ (exists  y1  y2 , x1 = y1 :: y2)) \/ (exists  y1  y2 , x2 = y1 :: y2))}: Z :=
  hd_sum ((a, b) :: l) ((a', b') :: l') init := init + a + b + a' + b';
  hd_sum ((a, b) :: l) l' init := init + a + b;
  hd_sum l ((a', b') :: l') init := init + a' + b'.

