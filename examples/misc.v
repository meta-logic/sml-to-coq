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

Equations length `(x1: @list _'14188): Z :=
  length [] := 0;
  length (x :: l) := (1 + (length l)).

Record rid_2  := 
{
  rid_2_name : string;
  rid_2_age : Z
}.

Definition r := rid_2.

Equations isBob (x1: r): bool :=
  isBob 
{|
  rid_2_age  := _;
  rid_2_name  := "Bob"
|} := true;
  isBob 
{|
  rid_2_age  := _;
  rid_2_name  := _
|} := false.

Equations F (x1: (Z * Z)%type): Z :=
  F (x, y) := ((x * x) + y).

Definition opF := F.
Notation "x 'F' y" := (F (x, y)) (left associativity, at level 29).

Definition f := opF.

Definition x := (5 F 2).

Definition y := (opF (2, 3)).

Equations filter `(x1: @list _'14236) `(x2: _'14236 -> bool): @list _'14236 :=
  filter [] _ := [];
  filter (x :: l) p := 
  match ((p x)) with
  | true => (x :: (((filter l) p)))  
  | false => ((filter l) p)
  end.

Inductive evenList  {_a : Type} : Type := 
  | ENil  
  | ECons : (_a * @oddList _a)%type -> @evenList _a
with oddList  {_a : Type} : Type := 
  | OCons : (_a * @evenList _a)%type -> @oddList _a.

Equations lengthE `(x1: @evenList _a): Z :=
  lengthE ENil := 0;
  lengthE (ECons (_, l)) := (lengthO l)
with lengthO `(x1: @oddList _a): Z :=
  lengthO (OCons (_, l)) := (lengthE l).

Equations posAdd (x1: (Z * Z)%type): Z :=
  posAdd (x, y) := (x + y).

Theorem posAdd_THM: forall x y b, posAdd (x, y) = b /\ ((x > 0) && (y > 0)) = true -> ((b > x) && (b > y)) = true.
Admitted.

Equations hd_sum (x1: @list (Z * Z)%type) (x2: @list (Z * Z)%type) {H: exists y1 y2 , eq (x1) (y1 :: y2) /\ exists y1 y2 , eq (x2) (y1 :: y2) \/ exists y1 y2 , eq (x1) (y1 :: y2) \/ exists y1 y2 , eq (x2) (y1 :: y2)}: Z :=
  hd_sum ((a, b) :: l) ((a', b') :: l') := (((a + b) + a') + b');
  hd_sum ((a, b) :: l) l' := (a + b);
  hd_sum l ((a', b') :: l') := (a' + b');
  hd_sum _ _ := _.
Admit Obligations.

Module Type PAIR.

Parameter t1 : Type.

Parameter t2 : Type.

Definition t := (t1 * t2)%type.

Parameter default : unit -> t.
End PAIR.

Module IntString <: PAIR.

Definition t1 := Z.

Definition t2 := string.

Definition t := (t1 * t2)%type.

Equations default (x1: unit%type): (Z * string)%type :=
  default tt := (0, "").
End IntString.

Module Example ( Pair : PAIR ).

Definition a := 
  match (Pair.default tt) with
  (a, b) => a
  end.

Definition b := 
  match (Pair.default tt) with
  (a, b) => b
  end.
End Example.

Module S := !Example IntString.

Equations collatz (x1: Z): @list Z :=
  collatz 1 := [1];
  collatz n := (n :: (
  match (n mod 2) with
  | 0 => (collatz ((n div 2)))  
  | _ => (collatz (((3 * n) + 1)))
  end)).
