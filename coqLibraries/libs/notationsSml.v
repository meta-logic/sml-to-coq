Require Import Floats.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import ZArith.

Require Import List.
Import ListNotations.

Axiom patternFailure: forall{a}, a.
Notation "# X" := (X % char) (at level 0).

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


(* These functions used in imolementing comparing two strings lexicographically,
 using the underlying ordering on the char type.*)
(*---------------------------------------------------------------------------*)

(*
  Sml: string -> char list
  Coq: string -> list ascii
*)
Local Definition explode (s:string): list ascii:= (String.list_ascii_of_string s).

Local Fixpoint collate' (f:ascii * ascii -> comparison) (l1 l2:list ascii): comparison:=
  match l1, l2 with
  | [],[] => Eq
  | [],_  => Lt
  | _ ,[] => Gt
  | x1::l1',x2::l2' => match f(x1,x2) with
                       | Eq     => collate' f l1' l2'
                       | other  => other
                       end
  end.

(*
  Sml: (char * char -> order) -> string * string -> order
  Coq: (ascii * ascii -> comparison) -> string * string -> comparison
*)
Local Definition collate (f:ascii * ascii -> comparison)
           '((s1, s2):string * string): comparison := 
            collate' f (explode s1) (explode s2).
(* 
  Sml: char -> int
  Coq: ascii -> Z
*)
Local Definition ord (c:ascii):Z := Z.of_nat(Ascii.nat_of_ascii(c)).

(* 
  Sml: char * char -> order
  Coq: ascii * ascii -> comparison
*)
Local Definition compareChar '((c, d):ascii * ascii):comparison := 
  Z.compare (ord c) (ord d).

(*
  Sml: string * string -> order
  Coq: string * string -> comparison
*)
Local Definition compare '((s1, s2):string * string):comparison :=
  collate compareChar (s1, s2).
(*---------------------------------------------------------------------------*)


Instance compInfixesString : compInfixes string :=
{
  ltb := fun a b => match compare(a, b) with | Lt => true | _  => false end;
  leb := fun a b => match compare(a, b) with | Gt => false | _  => true end;
  gtb := fun a b => match compare(a, b) with | Gt => true | _  => false end;
  geb := fun a b => match compare(a, b) with | Lt => false | _  => true end;
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

(* = , <>*)
Class eqInfixes A : Type :=
{
  eqb : A -> A -> bool;
  neq : A -> A -> bool
}.
Infix "="  := eqb (at level 70).
Notation "op=( x , y )" := (eqb x y) (at level 70).
Infix "<>"  := neq (at level 70).
Notation "op<>( x , y )" := (neq x y) (at level 70).

Instance eqInfixesBool : eqInfixes bool :=
{
  eqb := Bool.eqb;
  neq := fun a b => if Bool.eqb a b then false else true
}.

Instance eqInfixesString : eqInfixes string :=
{
  eqb := String.eqb;
  neq := fun a b => if String.eqb a b then false else true
}.

Instance eqInfixesChar : eqInfixes ascii :=
{
  eqb := Ascii.eqb;
  neq := fun a b => if Ascii.eqb a b then false else true
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
}.

Instance arithInfixesReal : arithInfixes float :=
{
  add  := PrimFloat.add;
  mul  := PrimFloat.mul;
  sub  := PrimFloat.sub;
}.

Instance arithInfixesNat : arithInfixes nat :=
{
  add  := Nat.add;
  mul  := Nat.mul;
  sub  := Nat.sub;
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
(* div, rem, @, ::, *+, *-, !=, ?=*)

Definition div' (i1 i2: Z):Z := i1 / i2.
Infix "div" := (div') (at level 40, left associativity).

Definition rem' '((i1, i2): Z * Z):Z := Z.modulo i1 i2.
Infix "rem" := rem' (at level 40, no associativity).

Definition append {A: Type} (l1:list A) (l2:list A):list A := List.app l1 l2.
Infix "@" := append (right associativity, at level 60).

Notation "op::( x , y )" := (x::y).

Definition mp (a b c:float):float := PrimFloat.add (PrimFloat.mul a b) c.
Notation "*+( x , y , z )" := (mp x y z) (at level 40, left associativity).

Definition ms (a b c:float):float := PrimFloat.sub (PrimFloat.mul a b) c.
Notation "*-( x , y , z )" := (ms x y z) (at level 40, left associativity).

Definition opne x y:bool := Bool.eqb false (PrimFloat.eqb y x). 
Infix "!=" := opne (at level 70).

Definition ope x y:bool := (PrimFloat.eqb x y) && (x != nan) && (y != nan) . 
Infix "==" := ope (at level 70).

Definition opne' x y:bool := (x == nan) || (y == nan) ||
                               Bool.eqb false (PrimFloat.eqb y x). 
Infix "?=" := opne' (at level 70).
