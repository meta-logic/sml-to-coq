
Module Option.

  Variable (A:Type) (B:Type) (C:Type).
  Definition getOPt {A:Type} '((opt, a):option A * A):A := 
    match opt with
    | None   => a
    | Some v => v
    end.

  Definition isSome {A:Type} (opt:option A):bool :=
    match opt with
    | None   => false
    | Some v => true
    end.

  (* It will compile without default, However it will
     return the right type iff you pass a default value *)
  (* We can pass a default while genrating the code after knowing the type of A*)
  Definition ValOf {A:Type} (opt:option A) (default:A):A := 
    getOPt(opt, default).

  Definition filter {A:Type} (f:A->bool) (a:A):option A := 
    match f(a) with
    | true  => Some a
    | false => None
    end.

  Definition join {A:Type} (opt:option (option A)):option A :=
    match opt with
    | None   => None
    | Some v => v
    end.

  Definition app {A:Type} (f:A->unit) (opt:option A):unit :=
    match opt with
    | None   => tt
    | Some v => let _:= f(v) in tt
    end.

  Definition map {A B:Type} (f:A->B) (opt:option A):option B := 
    match opt with
    | None   => None
    | Some v => Some(f v) 
    end.

  Definition mapPartial {A B:Type} (f:A->option B) (opt:option A):option B :=
    match opt with
    | None   => None
    | Some v => f v 
    end.

  Definition compose {A B C:Type} '((f, g):(A->B)*(C->option A)) 
    (a:C):option B :=
    match g(a) with
    | None   => None
    | Some v => Some(f v)
    end.

  Definition composePartial {A B C:Type} '((f, g):(A->option B)*(C->option A)) 
    (a:C):option B :=
    match g(a) with
    | None   => None
    | Some v => f v
    end.

End Option.









