Require Import Bool.
Require Import List.
Import ListNotations.

Module List.

  Variables (A : Type) (B : Type).

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
    Coq: list A -> nat
  *)
  Definition length {A: Type} (l:list A):nat := List.length l.

  (*
    Sml: 'a list * 'a list -> 'a list
    Coq: list A * list A -> list A
  *)
  Definition append {A: Type} (l1:list A) (l2:list A):list A := List.app l1 l2.
  Infix "@" := append (right associativity, at level 60).

  (*
    Sml: 'a list -> 'a
    Coq: A -> list A  -> A
    - It will compile without default, However it will
      return the right type iff you pass a default value
    - We can pass a default while genrating the code after knowing the type of A
  *)
  Definition hd {A: Type} (default:A) (l:list A):A := List.hd default l.

  (*
    Sml: 'a list -> 'a list
    Coq: list A -> list A
  *)
  Definition tl {A: Type} (l:list A):list A := List.tl l.

  (*
    Sml: 'a list -> 'a
    Coq: list A -> A -> A
    - It will compile without default, However it will
      return the right type iff you pass a default value
    - We can pass a default while genrating the code after knowing the type of A
  *)
  Fixpoint last {A: Type} (l:list A) (default:A):A := List.last l default.

  (*
    Sml: 'a list -> ('a * 'a list) option
    Coq: list A -> A -> option ('a * 'a list)
    - It will compile without default, However it will
      return the right type iff you pass a default value
    - We can pass a default while genrating the code after knowing the type of A
  *)
  Definition getItem {A: Type} (l:list A) (default:A):option (A * list A) :=
    match l with
    | [] => None
    | _  => Some (List.hd default l, List.tl l)
    end.

  (*
    Sml: 'a list * int -> 'a
    Coq: list A * nat -> A -> A
    - It will compile without default, However it will
      return the right type iff you pass a default value
    - We can pass a default while genrating the code after knowing the type of A
  *)
  Definition nth {A: Type} '((l, n):list A * nat) (default:A):A := 
    List.nth n l default.

  (*
    Sml: 'a list * int -> 'a list
    Coq: list A * nat -> list A
  *)
  Definition take {A: Type} '((l, n):list A * nat):list A := List.firstn n l.

  (*
    Sml: 'a list * int -> 'a list
    Coq: list A * nat -> list A
  *)
  Definition drop {A: Type} '((l, n):list A * nat):list A := List.skipn n l.

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

  Fixpoint tabulate' {A: Type} (time n:nat)(f:nat->A) (l:list A) :=
    match time with  
    | 0 => l
    | S time' => 
      match n with
      | 0  => f 0::l
      | n' =>(tabulate' time' (n'-1) f ((f n)::l)) 
      end
    end.

  (*
    Sml:  int * (int -> 'a) -> 'a list
    Coq:  nat * (nat -> A) -> list A
  *)
  Definition tabulate {A: Type} '((n, f):nat * (nat->A)):list A :=
    tabulate' n n f [].

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