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

Equations p_head {_'13801: Type} (x1: (@ list _'13801)) {H: (exists  y1  y2 , eq (x1) (y1 :: y2))}: _'13801 :=
  p_head (x :: _) := x;
  p_head _ := _.

Equations hd_sum (x1: (@ list (Z * Z) % type)) (x2: (@ list (Z * Z) % type)) {H: ((((exists  y1  y2 , eq (x1) (y1 :: y2)) /\ (exists  y1  y2 , eq (x2) (y1 :: y2))) \/ (exists  y1  y2 , eq (x1) (y1 :: y2))) \/ (exists  y1  y2 , eq (x2) (y1 :: y2)))}: Z :=
  hd_sum ((a, b) :: l) ((a', b') :: l') := a + b + a' + b';
  hd_sum ((a, b) :: l) l' := a + b;
  hd_sum l ((a', b') :: l') := a' + b';
  hd_sum _ _ := _.
