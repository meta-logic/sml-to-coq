Require Export List.
Export ListNotations.

Module ListPair.

  Axiom  UnequalLengthsException : forall{a}, a.

  Local Fixpoint zip' {A B:Type} (l1:list A) (l2:list B):list(A * B) :=
    match l1,l2 with
    | [], _  => []
    | _ , [] => []
    | x::l1', y::l2' => (x,y)::(zip' l1' l2' )
    end.

  (*
    Sml: 'a list * 'b list -> ('a * 'b) list
    Coq: list A * list A -> list (A * B)
  *)
  Definition zip {A B:Type} '((l1, l2):list A * list B):list(A * B) :=
    zip' l1 l2.

  (*
    Sml: 'a list * 'b list -> ('a * 'b) list
    Coq: list A * list A -> list (A * B)
    - It should raise exception if l1 and l2 have different lengths, but 
      since Coq doen't have exceptions, it will return the axiom [] 
      UnequalLengthsException 
  *)
  Definition zipEq {A B:Type} '((l1, l2):list A * list B):list(A * B) :=
    match (Nat.eqb (List.length l1) (List.length l2)) with
    | true  => zip' l1 l2
    | false => UnequalLengthsException
    end.

  Local Fixpoint unzip' {A B:Type} (l:list (A * B)):list A * list B :=
    match l with
    | [] => ([],[])
    | (x,y)::l' => let (l1,l2) := unzip' l' in (x::l1,y::l2)
     end.

  (*
    Sml: ('a * 'b) list -> 'a list * 'b list
    Coq: list (A * B) -> list A * list A
  *)
  Definition unzip {A B:Type} (l:list (A * B)):list A * list B := unzip' l.

  Local Fixpoint app' {A B:Type} (f:A*B->unit) (l1:list A) (l2:list B):unit :=
    match l1, l2 with
    | [], _  => tt
    | _ , [] => tt
    | x::l1', y::l2' => let _ := f(x,y) in (app' f l1' l2')
    end.

  (*
    Sml: ('a * 'b -> unit) -> 'a list * 'b list -> unit
    Coq: (A * B -> unit) -> list A * list B -> unit
  *)
  Definition app {A B:Type} (f:A*B->unit) '((l1, l2):list A * list B):unit :=
    app' f l1 l2.

  (*
    Sml: ('a * 'b -> unit) -> 'a list * 'b list -> unit
    Coq: (A * B -> unit) -> list A * list B -> unit
    - It should raise exception if l1 and l2 have different lengths, but 
      since Coq doen't have exceptions, it will return the axiom [] 
      UnequalLengthsException 
  *)
  Definition appEq {A B:Type} (f:A*B->unit) '((l1, l2):list A * list B):unit :=
    match (Nat.eqb (List.length l1) (List.length l2)) with
    | true  => app' f l1 l2
    | false => UnequalLengthsException
    end.

  (*
    Sml: ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
    Coq: (A * B -> C) -> list A * list B -> list C
  *)
  Definition map {A B C:Type} (f:A*B->C) '((l1, l2):list A * list B):list C :=
    List.map f (zip (l1, l2)).

  (*
    Sml: ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
    Coq: (A * B -> C) -> list A * list B -> list C
    - It should raise exception if l1 and l2 have different lengths, but 
      since Coq doen't have exceptions, it will return the axiom [] 
      UnequalLengthsException 
  *)
  Definition mapEq {A B C:Type} (f:A*B->C) '((l1, l2):list A*list B):list C :=
    match (Nat.eqb (List.length l1) (List.length l2)) with
    | true  =>  List.map f (zipEq (l1, l2))
    | false => UnequalLengthsException
    end.

  Local Fixpoint foldl' {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => foldl' f (f(a,b0)) t
    end.

  Local Fixpoint foldr' {A B: Type} (f:A * B ->B) (b0:B) (l:list A):B :=
    match l with
    | nil => b0
    | cons a t => f(a, foldr' f b0 t)
    end.

  (*
    Sml: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
    Coq: (A * B * C -> C) -> C -> list A * list B -> C
  *)
  Definition foldl {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
              foldl' (fun '((a,b),c)=>f(a,b,c)) init (zip (l1, l2)).

  (*
    Sml: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
    Coq: (A * B * C -> C) -> C -> list A * list B -> C
    - It should raise exception if l1 and l2 have different lengths, but 
      since Coq doen't have exceptions, it will return the axiom [] 
      UnequalLengthsException 
  *)
  Definition foldlEq {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
             match (Nat.eqb (List.length l1) (List.length l2)) with
             | true  => foldl' (fun '((a,b),c)=>f(a,b,c)) init (zipEq (l1, l2))
             | false => UnequalLengthsException
             end.

  (*
    Sml: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
    Coq: (A * B * C -> C) -> C -> list A * list B -> C
  *)
  Definition foldr {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
              foldr' (fun '((a,b),c)=>f(a,b,c)) init (zip (l1, l2)).

  (*
    Sml: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
    Coq: (A * B * C -> C) -> C -> list A * list B -> C
    - It should raise exception if l1 and l2 have different lengths, but 
      since Coq doen't have exceptions, it will return the axiom [] 
      UnequalLengthsException
  *)
  Definition foldrEq {A B C:Type} (f:A*B*C->C) (init:C) 
             '((l1, l2):list A * list B):C :=
             match (Nat.eqb (List.length l1) (List.length l2)) with
             | true  => foldr' (fun '((a,b),c)=>f(a,b,c)) init (zipEq (l1, l2))
             | false => UnequalLengthsException
             end.

  (*
    Sml: ('a * 'b -> bool) -> 'a list * 'b list -> bool
    Coq: (A * B -> bool) -> list A * list B -> bool
  *)
  Definition all {A B:Type} (f:A*B->bool) '((l1,l2):list A * list B):bool :=
    List.forallb f (zip (l1,l2)).

  (*
    Sml: ('a * 'b -> bool) -> 'a list * 'b list -> bool
    Coq: (A * B -> bool) -> list A * list B -> bool
  *)
  Definition allEq {A B:Type} (f:A*B->bool) '((l1,l2):list A * list B):bool :=
    match (List.forallb f (zip (l1,l2))), 
          (Nat.eqb (List.length l1) (List.length l2)) with
    | true, true => true
    | _   , _    => false
    end.

  (*
    Sml: ('a * 'b -> bool) -> 'a list * 'b list -> bool
    Coq: (A * B -> bool) -> list A * list B -> bool
    - You can't have a function named exists
  *)
  Definition existsb {A B: Type} (f:A*B->bool) '((l1,l2):list A * list B):bool :=
      List.existsb f (zip (l1,l2)).

End ListPair.