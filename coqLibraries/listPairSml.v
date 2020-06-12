Require Import List.
Import ListNotations.

Module ListPair.

  Variable (A:Type) (B:Type) (C:Type).

  Fixpoint zip' {A B:Type} (l1:list A) (l2:list B):list(A * B) :=
    match l1,l2 with
    | [], _  => []
    | _ , [] => []
    | x::l1', y::l2' => (x,y)::(zip' l1' l2' )
    end.

  Definition zip {A B:Type} '((l1, l2):list A * list B):list(A * B) :=
    zip' l1 l2.

  (* It should raise exception if l1 and l2 have different lengths, but 
    since Coq doen't have exceptions, it will return [] as a default value *)
  Definition zipEq {A B:Type} '((l1, l2):list A * list B):list(A * B) :=
    match (Nat.eqb (List.length l1) (List.length l2)) with
    | true  => zip' l1 l2
    | false => []
    end.

  Fixpoint unzip {A B:Type} (l:list (A * B)):list A * list B :=
    match l with
    | [] => ([],[])
    | (x,y)::l' => let (l1,l2) := unzip l' in (x::l1,y::l2)
     end.

  Fixpoint app' {A B:Type} (f:A*B->unit) (l1:list A) (l2:list B):unit :=
    match l1, l2 with
    | [], _  => tt
    | _ , [] => tt
    | x::l1', y::l2' => let _ := f(x,y) in (app' f l1' l2')
    end.

  Definition app {A B:Type} (f:A*B->unit) '((l1, l2):list A * list B):unit :=
    app' f l1 l2.

  (* It should raise exception if l1 and l2 have different sizes, but 
    since Coq doen't have exceptions, it will return unit as a default value*)
  Definition appEq {A B:Type} (f:A*B->unit) '((l1, l2):list A * list B):unit :=
    app' f l1 l2.

  Definition map {A B C:Type} (f:A*B->C) '((l1, l2):list A * list B):list C :=
    List.map f (zip (l1, l2)).

  (* It should raise exception if l1 and l2 have different sizes, but 
    since Coq doen't have exceptions, it will return [] as a default value *)
  Definition mapEq {A B C:Type} (f:A*B->C) '((l1, l2):list A*list B):list C :=
    match (Nat.eqb (List.length l1) (List.length l2)) with
    | true  =>  List.map f (zipEq (l1, l2))
    | false => []
    end.

  Fixpoint foldl' {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => foldl' f (f(a,b0)) t
    end.

  Fixpoint foldr' {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => f(a, foldr' f b0 t)
    end.

  Definition foldl {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
              foldl' (fun '((a,b),c)=>f(a,b,c)) init (zip (l1, l2)).

  (* It should raise exception if l1 and l2 have different sizes, but 
    since Coq doen't have exceptions, it will return init as a default value *)
  Definition foldlEq {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
             match (Nat.eqb (List.length l1) (List.length l2)) with
             | true  => foldl' (fun '((a,b),c)=>f(a,b,c)) init (zipEq (l1, l2))
             | false => init
             end.

  Definition foldr {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
              foldr' (fun '((a,b),c)=>f(a,b,c)) init (zip (l1, l2)).

  (* It should raise exception if l1 and l2 have different sizes, but 
    since Coq doen't have exceptions, it will return init as a default value *)
  Definition foldrEq {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
             match (Nat.eqb (List.length l1) (List.length l2)) with
             | true  => foldr' (fun '((a,b),c)=>f(a,b,c)) init (zipEq (l1, l2))
             | false => init
             end.

  Definition all {A B:Type} (f:A*B->bool) '((l1,l2):list A * list B):bool :=
    List.forallb f (zip (l1,l2)).

  Definition allEq {A B:Type} (f:A*B->bool) '((l1,l2):list A * list B):bool :=
    match (List.forallb f (zip (l1,l2))), 
          (Nat.eqb (List.length l1) (List.length l2)) with
    | true, true => true
    | _   , _    => false
    end.

  (*You can't have a function named exists*)
  Definition existsb {A B: Type} (f:A*B->bool) '((l1,l2):list A * list B):bool :=
      List.existsb f (zip (l1,l2)).

End ListPair.