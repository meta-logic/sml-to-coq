Require Import Bool.
Require Import List.
Import ListNotations.


Module List.

  Variables (A : Type) (B : Type).

  Definition null {A: Type} (l:list A):bool :=
    match l with
    | [] => true
    | _  => false
    end.

  Definition length {A: Type} (l:list A):nat := List.length l.

  Definition append {A: Type} (l1:list A) (l2:list A):list A := List.app l1 l2.
  Infix "@" := append (right associativity, at level 60).

  (* It will compile without default, However it will
     return the right type iff you pass a default value *)
  (* We can pass a default while genrating the code after knowing the type of A*)
  Definition hd {A: Type} (default:A) (l:list A):A := List.hd default l.

  Definition tl {A: Type} (l:list A):list A := List.tl l.

  (* It will compile without default, However it will
     return the right type iff you pass a default value *)
  (* We can pass a default while genrating the code after knowing the type of A*)
  Fixpoint last {A: Type} (l:list A) (default:A):A := List.last l default.

  (* It will compile without default, However it will
     return the right type iff you pass a default value *)
  (* We can pass a default while genrating the code after knowing the type of A*)
  Definition getItem {A: Type} (l:list A) (default:A):option (A * list A) :=
    match l with
    | [] => None
    | _  => Some (List.hd default l, List.tl l)
    end.

  (* It will compile without default, However it will
     return the right type iff you pass a default value *)
  (* We can pass a default while genrating the code after knowing the type of A*)
  Definition nth {A: Type} '((n, l):nat * list A) (default:A):A := 
    List.nth n l default.

  Definition take {A: Type} '((n, l):nat * list A):list A := List.firstn n l.

  Definition drop {A: Type} '((n, l):nat * list A):list A := List.skipn n l.

  Definition rev {A: Type} (l:list A):list A              := List.rev l. 

  Definition concat {A: Type} (l:list(list A)):list A     := List.concat l.

  Definition revAppend {A: Type} '((l, l'):list A * list A):list A :=
     List.rev_append l l'.

  Fixpoint app {A: Type} (f:A->unit) (l:list A): unit:= 
    match l with
    | [] => tt
    | a :: t => let _ := (f a) in app f t
    end.

  Definition map {A B: Type} (f: A->B) (l:list A):list B := List.map f l.

  Fixpoint mapPartial {A B: Type} (f: A-> option B) (l:list A):list B :=
    match l with
    | [] => []
    | x::l' => match f x with 
               | None   => mapPartial f l'
               | Some y => y::mapPartial f l'
               end
    end.

  Definition find {A: Type} (f:A->bool) (l:list A):option A := List.find f l.

  Definition filter {A: Type} (f:A->bool) (l:list A):list A := List.filter f l.

  Definition partition {A: Type} (f:A->bool) (l:list A):list A * list A :=
     List.partition f l.

  Fixpoint foldl {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => foldl f (f(a,b0)) t
    end.

  Fixpoint foldr {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => f(a, foldr f b0 t)
    end.

  (*You can't have a function named exists*)
  Definition existsb {A: Type} (f:A->bool) (l:list A):bool := List.existsb f l.

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

  Definition collate (f:A * A -> comparison) 
             '((l1, l2):list A * list A):comparison := collate' f l1 l2 .

End List.