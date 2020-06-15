
Module Option.

  Variable (A:Type) (B:Type) (C:Type).

  (*
    Sml: 'a option * 'a -> 'a
    Coq: option A * A -> A
  *)
  Definition getOPt {A:Type} '((opt, a):option A * A):A := 
    match opt with
    | None   => a
    | Some v => v
    end.

  (*
    Sml: 'a option -> bool
    Coq: option A -> bool
  *)
  Definition isSome {A:Type} (opt:option A):bool :=
    match opt with
    | None   => false
    | Some v => true
    end.

  (*
    Sml: 'a option -> A
    Coq: option A -> A -> A
    - It will compile without default, However it will
      return the right type iff you pass a default value
    - We can pass a default while genrating the code after knowing the type of A
  *)
  Definition ValOf {A:Type} (opt:option A) (default:A):A := 
    getOPt(opt, default).

  (*
    Sml: ('a -> bool) -> 'a -> 'a option
    Coq: (A -> bool) -> A -> option A
  *)
  Definition filter {A:Type} (f:A->bool) (a:A):option A := 
    match f(a) with
    | true  => Some a
    | false => None
    end.

  (*
    Sml: 'a option option -> 'a option
    Coq: option(option A) -> option A
  *)
  Definition join {A:Type} (opt:option (option A)):option A :=
    match opt with
    | None   => None
    | Some v => v
    end.

  (*
    Sml: ('a -> unit) -> 'a option -> unit
    Coq: (A -> unit) -> option A -> unit
  *)
  Definition app {A:Type} (f:A->unit) (opt:option A):unit :=
    match opt with
    | None   => tt
    | Some v => let _:= f(v) in tt
    end.

  (*
    Sml: ('a -> 'b) -> 'a option -> 'b option
    Coq: (A -> B) -> option A -> option B
  *)
  Definition map {A B:Type} (f:A->B) (opt:option A):option B := 
    match opt with
    | None   => None
    | Some v => Some(f v) 
    end.

  (*
    Sml: ('a -> 'b option) -> 'a option -> 'b option
    Coq: (A -> option B) -> option A -> option B
  *)
  Definition mapPartial {A B:Type} (f:A->option B) (opt:option A):option B :=
    match opt with
    | None   => None
    | Some v => f v 
    end.

  (*
    Sml: ('a -> 'b) * ('c -> 'a option) -> 'c -> 'b option
    Coq: (A -> B) * (C -> option A) -> C -> option B
  *)
  Definition compose {A B C:Type} '((f, g):(A->B)*(C->option A)) 
    (a:C):option B :=
    match g(a) with
    | None   => None
    | Some v => Some(f v)
    end.

  (*
    Sml: ('a -> 'b option) * ('c -> 'a option) -> 'c -> 'b option
    Coq: (A -> option B) * (C -> option A) -> C -> option B
  *)
  Definition composePartial {A B C:Type} '((f, g):(A->option B)*(C->option A)) 
    (a:C):option B :=
    match g(a) with
    | None   => None
    | Some v => f v
    end.

End Option.