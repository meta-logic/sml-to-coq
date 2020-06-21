Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import Floats.
Require Import List.
Import ListNotations.

(* < , <= , > , >= *)
Class compInfixes A : Type :=
{
  ltb : A -> A -> bool;
  leb : A -> A -> bool;
  gtb : A -> A -> bool;
  geb : A -> A -> bool
}.
Infix "<"  := ltb (at level 70).
Notation "op<( x , y )" := (ltb x y) (at level 70).
Infix "<=" := leb (at level 70).
Notation "op<=( x , y )" := (leb x y) (at level 70).
Infix ">"  := gtb (at level 70).
Notation "op>( x , y )" := (gtb x y) (at level 70).
Infix ">=" := geb (at level 70).
Notation "op>=( x , y )" := (geb x y) (at level 70).

Instance compInfixesString : compInfixes string :=
{
  ltb := String.eqb; 
  leb := String.eqb;
  gtb := fun a b => Nat.ltb (String.length b) (String.length a);
  geb := fun a b => Nat.leb (String.length b) (String.length a)
}.

Instance compInfixesChar : compInfixes ascii :=
{
  ltb := fun a b => Nat.ltb (Ascii.nat_of_ascii(a)) (Ascii.nat_of_ascii(b));
  leb := fun a b => Nat.leb (Ascii.nat_of_ascii(a)) (Ascii.nat_of_ascii(b));
  gtb := fun a b => Nat.ltb (Ascii.nat_of_ascii(b)) (Ascii.nat_of_ascii(a));
  geb := fun a b => Nat.leb (Ascii.nat_of_ascii(b)) (Ascii.nat_of_ascii(a))
}.

Instance compInfixesInt : compInfixes Z :=
{
  ltb := Z.ltb;
  leb := Z.leb;
  gtb := fun a b => Z.ltb b a;
  geb := fun a b => Z.leb b a 
}.

Instance compInfixesReal : compInfixes float :=
{
  ltb := PrimFloat.ltb;
  leb := PrimFloat.leb;
  gtb := fun a b => PrimFloat.ltb b a;
  geb := fun a b => PrimFloat.leb b a 
}.

(*---------------------------------------------------------------------------*)

(* = , <> *)
Class eqInfixes A : Type :=
{
  eqb : A -> A -> bool;
  neq : A -> A -> bool
}.
Infix "="  := eqb (at level 70).
Notation "op=( x , y )" := (eqb x y) (at level 70).
Infix "<>"  := eqb (at level 70).
Notation "op<>( x , y )" := (neq x y) (at level 70).

Instance eqInfixesBool : eqInfixes bool :=
{
  eqb := Bool.eqb;
  neq := fun a b => if Bool.eqb a b then false else true
}.

Instance eqInfixesString : eqInfixes string :=
{
  eqb := fun a b => Nat.eqb (String.length a) (String.length b);
  neq := fun a b => if (Nat.eqb (String.length a) (String.length b))
                    then false else true
}.

Instance eqInfixesChar : eqInfixes ascii :=
{
  eqb := fun a b => Nat.eqb (Ascii.nat_of_ascii(a)) (Ascii.nat_of_ascii(b));
  neq := fun a b => if (Nat.eqb (Ascii.nat_of_ascii(a)) (Ascii.nat_of_ascii(b)))
                    then false else true
}.

Instance eqInfixesInt : eqInfixes Z :=
{
  eqb := Z.eqb;
  neq := fun a b => if Z.eqb a b then false else true
}.

(*---------------------------------------------------------------------------*)

(* + , * , - *)
Class arithInfixes A : Type :=
{
  add : A -> A -> A;
  mul : A -> A -> A;
  sub  : A -> A -> A;
  (* abs  : A -> A *)
}.
Infix "+"  := add.
Notation "op+( x , y )" := (add x y).
Infix "*"  := mul.
Notation "op*( x , y )" := (mul x y).
Infix "-"  := sub.
Notation "op-( x , y )" := (sub x y).

Instance arithInfixesInt : arithInfixes Z :=
{
  add  := Z.add;
  mul  := Z.mul;
  sub  := Z.sub;
  (* abs  := fun x => Z.max x (-x) *)
}.

Instance arithInfixesReal : arithInfixes float :=
{
  add  := PrimFloat.add;
  mul  := PrimFloat.mul;
  sub  := PrimFloat.sub;
  (* abs  := PrimFloat.abs *)
}.

Instance arithInfixesNat : arithInfixes nat :=
{
  add  := Nat.add;
  mul  := Nat.mul;
  sub  := Nat.sub;
  (* abs  := PrimFloat.abs *)
}.

(*---------------------------------------------------------------------------*)

(* abs *)
Class absInfix A : Type :=
{
  abs  : A -> A
}.

Instance absInfixInt : absInfix Z :=
{

  abs  := fun x => Z.max x (-x)
}.

Instance absInfixReal : absInfix float :=
{
  abs  := PrimFloat.abs
}.

(*---------------------------------------------------------------------------*)

(* mod *)
Class modInfix A : Type :=
{
  modulo : A -> A -> A
}.
Infix "mod" := modulo (at level 40, no associativity).

Instance modInfixInt : modInfix Z :=
{

  modulo  := Z.modulo
}.

Instance modInfixNat : modInfix nat :=
{
  modulo  := Nat.modulo
}.

(*---------------------------------------------------------------------------*)

(* / *)
Class divInfix A : Type :=
{
  dv : A -> A -> A
}.
Infix "/" := dv.

Instance divInfixReal : divInfix float :=
{

  dv  := PrimFloat.div
}.

Instance divInfixNat : divInfix nat :=
{
  dv  := Nat.div
}.

(*---------------------------------------------------------------------------*)

(* ^ *)
Class powAppInfix A : Type :=
{
  powApp : A -> A -> A
}.
Infix "^" := powApp.
Notation "op^( x , y )" := (powApp x y).

Instance powAppInfixReal : powAppInfix string :=
{
  powApp  := String.append
}.

Instance powAppInfixNat : powAppInfix nat :=
{
  powApp  := Nat.pow
}.

(*---------------------------------------------------------------------------*)

(* Other Notations *)
(* div , * , - *)

Definition div' (i1 i2: Z):Z := i1 / i2.
Infix "div" := (div') (at level 40, left associativity).

Definition append {A: Type} (l1:list A) (l2:list A):list A := List.app l1 l2.
Infix "@" := append (right associativity, at level 60).

Notation "op::( x , y )" := (x::y).