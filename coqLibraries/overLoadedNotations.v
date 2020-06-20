Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import Floats.

(* < , <= , > , >= *)
Class compInfixes A : Type :=
{
  ltb : A -> A -> bool;
  leb : A -> A -> bool;
  gtb : A -> A -> bool;
  geb : A -> A -> bool
}.
Infix "<"  := ltb (at level 70).
Infix "<=" := leb (at level 70).
Infix ">"  := gtb (at level 70).
Infix ">=" := geb (at level 70).

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

(* = *)
Class eqInfixes A : Type :=
{
  eqb : A -> A -> bool;
}.
Infix "="  := eqb (at level 70).

Instance eqInfixesBool : eqInfixes bool :=
{
  eqb := Bool.eqb
}.

Instance eqInfixesString : eqInfixes string :=
{
  eqb := fun a b => Nat.eqb (String.length a) (String.length b)
}.

Instance eqInfixesChar : eqInfixes ascii :=
{
  eqb := fun a b => Nat.eqb (Ascii.nat_of_ascii(a)) (Ascii.nat_of_ascii(b))
}.

Instance eqInfixesInt : eqInfixes Z :=
{
  eqb := Z.eqb
}.

(*---------------------------------------------------------------------------*)

(* + , * , - , abs *)
Class arithInfixes A : Type :=
{
  add : A -> A -> A;
  mul : A -> A -> A;
  sub  : A -> A -> A;
  abs  : A -> A
}.

Infix "+"  := add.
Infix "*"  := mul.
Infix "-"  := sub.

Instance arithInfixesInt : arithInfixes Z :=
{
  add  := Z.add;
  mul  := Z.mul;
  sub  := Z.sub;
  abs  := fun x => Z.max x (-x)
}.

Instance arithInfixesReal : arithInfixes float :=
{
  add  := PrimFloat.add;
  mul  := PrimFloat.mul;
  sub  := PrimFloat.sub;
  abs  := PrimFloat.abs
}.