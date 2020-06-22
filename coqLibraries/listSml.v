Require Import Bool.
Require Import List.
Require Import ZArith.
Import ListNotations.

Module List.

  Variables (A : Type) (B : Type).

  Axiom  EmptyException : forall{a}, a.

  Axiom  SubscriptException : forall{a}, a.

  (*
    Sml: 'a list -> bool
    Coq: list A -> bool
  *)
  Definition null {A: Type} (l:list A):bool :=
    match l with
    | [] => true
    | _  => false
    end.

  (*
    Sml: 'a list -> int
    Coq: list A -> Z
  *)
  Definition length {A: Type} (l:list A):Z := Z.of_nat(List.length l).

  (*
    Sml: 'a list * 'a list -> 'a list
    Coq: list A * list A -> list A
  *)
  Definition append {A: Type} (l1:list A) (l2:list A):list A := List.app l1 l2.
  Infix "@" := append (right associativity, at level 60).

  (*
    Sml: 'a list -> 'a
    Coq: list A  -> A
    - It should raise an exception if you pass an empty list to it,
      but since Coq doesn't have exceptions then it will return the axiom 
      EmptyException
  *)
  Definition hd {A: Type} (l:list A):A := List.hd EmptyException l.

  (*
    Sml: 'a list -> 'a list
    Coq: list A -> list A
    - It should raise an exception if you pass an empty list to it,
      but since Coq doesn't have exceptions then it will return the axiom 
      EmptyException
  *)
  Definition tl {A: Type} (l:list A):list A :=
    match l with
    | [] => EmptyException
    | _  => List.tl l
    end.

  (*
    Sml: 'a list -> 'a
    Coq: list A -> A
    - It should raise an exception if you pass an empty list to it,
      but since Coq doesn't have exceptions then it will return the axiom 
      EmptyException
  *)
  Fixpoint last {A: Type} (l:list A):A := List.last l EmptyException.

  (*
    Sml: 'a list -> ('a * 'a list) option
    Coq: list A -> option ('a * 'a list)
  *)
  Definition getItem {A: Type} (l:list A):option (A * list A) :=
    match l with
    | [] => None
    | _  => Some (List.hd l, List.tl l)
    end.

  (*
    Sml: 'a list * int -> 'a
    Coq: list A * Z -> A
    - It should raise an exception if n < 0 or n >= length l.,
      but since Coq doesn't have exceptions then it will return the axiom 
      SubscriptException
  *)
  Definition nth {A: Type} '((l, n):list A * Z):A := 
    List.nth (Z.to_nat n) l SubscriptException.

  (*
    Sml: 'a list * int -> 'a list
    Coq: list A * Z -> list A
    - It should raise an exception if n < 0 or n >= length l.,
      but since Coq doesn't have exceptions then it will return the axiom 
      SubscriptException
  *)
  Definition take {A: Type} '((l, n):list A * Z):list A := 
    match (Z.ltb n 0) || (Z.ltb (length l) n) with 
    | true  => SubscriptException
    | false => List.firstn (Z.to_nat n) l
    end.

  (*
    Sml: 'a list * int -> 'a list
    Coq: list A * Z -> list A
    - It should raise an exception if n < 0 or n >= length l.,
      but since Coq doesn't have exceptions then it will return the axiom 
      SubscriptException
  *)
  Definition drop {A: Type} '((l, n):list A * Z):list A := 
    match (Z.ltb n 0) || (Z.ltb (length l) n) with 
    | true  => SubscriptException
    | false => List.skipn (Z.to_nat n) l
    end. 

  (*
    Sml: 'a list -> 'a list
    Coq: list A -> list A
  *)
  Definition rev {A: Type} (l:list A):list A              := List.rev l. 

  (*
    Sml: 'a list list -> 'a list
    Coq: list(list A) -> list A
  *)
  Definition concat {A: Type} (l:list(list A)):list A     := List.concat l.

  (*
    Sml: 'a list * 'a list -> 'a list
    Coq: list A * list A -> list A
  *)
  Definition revAppend {A: Type} '((l, l'):list A * list A):list A :=
     List.rev_append l l'.

  (*
    Sml: ('a -> unit) -> 'a list -> unit
    Coq: (A -> unit) -> list A -> unit
  *)
  Fixpoint app {A: Type} (f:A->unit) (l:list A): unit:= 
    match l with
    | [] => tt
    | a :: t => let _ := (f a) in app f t
    end.

  (*
    Sml: ('a -> 'b) -> 'a list -> 'b list
    Coq: (A -> B) -> list A -> list B
  *)
  Definition map {A B: Type} (f: A->B) (l:list A):list B := List.map f l.

  (*
    Sml: ('a -> 'b option) -> 'a list -> 'b list
    Coq: (A -> option B) -> list A -> list B
  *)
  Fixpoint mapPartial {A B: Type} (f: A-> option B) (l:list A):list B :=
    match l with
    | [] => []
    | x::l' => match f x with 
               | None   => mapPartial f l'
               | Some y => y::mapPartial f l'
               end
    end.

  (*
    Sml: ('a -> bool) -> 'a list -> 'a option
    Coq: (A -> bool) -> list A -> option A
  *)
  Definition find {A: Type} (f:A->bool) (l:list A):option A := List.find f l.

  (*
    Sml: ('a -> bool) -> 'a list -> 'a list
    Coq: (A -> bool) -> list A -> list A
  *)
  Definition filter {A: Type} (f:A->bool) (l:list A):list A := List.filter f l.

  (*
    Sml: ('a -> bool) -> 'a list -> 'a list * 'a list
    Coq: (A -> bool) -> list A -> list A * list A
  *)
  Definition partition {A: Type} (f:A->bool) (l:list A):list A * list A :=
     List.partition f l.

  (*
    Sml: ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
    Coq: (A * B -> B) -> B -> list A -> B
  *)
  Fixpoint foldl {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => foldl f (f(a,b0)) t
    end.

  (*
    Sml: ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
    Coq: (A * B -> B) -> B -> list A -> B
  *)
  Fixpoint foldr {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => f(a, foldr f b0 t)
    end.

  (*
    Sml: ('a -> bool) -> 'a list -> bool
    Coq: (A -> bool) list A -> bool
    - You can't have a function named exists
  *)
  Definition existsb {A: Type} (f:A->bool) (l:list A):bool := List.existsb f l.

  (*
    Sml: ('a -> bool) -> 'a list -> bool
    Coq: (A -> bool) list A -> bool
  *)
  Definition all {A: Type} (f:A->bool) (l:list A):bool     := List.forallb f l.

  Fixpoint tabulate' {A: Type} (time:nat) (n:Z)(f:Z->A) (l:list A) :=
    match time with  
    | 0 => l
    | S time' => if (Z.eqb n 0) then (f (0%Z)::l) 
                 else (tabulate' time' (n-1) f ((f n)::l))
    end.

  (*
    Sml:  int * (int -> 'a) -> 'a list
    Coq:  nat * (Z -> A) -> list A
  *)
  Definition tabulate {A: Type} '((n, f):Z * (Z->A)):list A :=
    tabulate' (Z.to_nat n) n f [].

  Fixpoint collate' {A: Type} (f:A * A -> comparison) (l1 l2:list A) :=
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
    Sml:  ('a * 'a -> order) -> 'a list * 'a list -> order
    Coq:  (A * A -> order) -> list A * list A -> comparison
  *)
  Definition collate (f:A * A -> comparison) 
             '((l1, l2):list A * list A):comparison := collate' f l1 l2 .

End List.