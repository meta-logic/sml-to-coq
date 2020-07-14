Require Export Ascii.
Require Export String.
Require Export ZArith.
Open Scope Z_scope.

Module Int.

  (* 
    Sml: int -> LargeInt.int
    Coq: Z -> Z
  *)
  Definition toLarge (i: Z):Z   := i.

  (* 
    Sml: Large.int -> int
    Coq: Z -> Z
  *)
  Definition fromLarge (i: Z):Z := i.

  (* 
    Sml: int -> Int.int
    Coq: Z -> Z
  *)
  Definition toInt (i: Z):Z     := i.

  (* 
    Sml: Int.int -> int
    Coq: Z -> Z
  *)
  Definition fromInt (i: Z):Z   := i.

  (* 
    Sml: Int.int option
    Coq: option Z
  *)
  Definition precision:option Z := Some 31.

  (* 
    Sml: int option
    Coq: option Z
  *)
  Definition minInt:option Z    := Some (-1073741824).

  (* 
    Sml: int option
    Coq: option Z
  *)
  Definition maxInt:option Z    := Some 1073741823.

  (* Already defined as *)
  (*
   Definition + : Z * Z -> Z
   Definition - : Z * Z -> Z
   Definition * : Z * Z -> Z
   Definition mod: Z * Z -> Z
  *)

  (* 
    Sml: int * int -> int
    Coq: Z * Z -> Z
  *)
  Definition div '((i1, i2): Z * Z):Z := i1 / i2.
  (*Definition div' (i1 i2: Z):Z := i1 / i2.
  Infix "div" := (div') (at level 40, left associativity). *)

  (* 
    Sml: int * int -> int
    Coq: Z * Z -> Z
  *)
  Definition quot '((i1, i2): Z * Z):Z := (i1 -(i1 mod 12)) / i2.

  (* 
    Sml: int * int -> int
    Coq: Z * Z -> Z
  *)
  Definition rem '((i1, i2): Z * Z):Z := i1 mod i2.
(*   Infix "rem" := rem (at level 40, no associativity). *)

  (* 
    Sml: int * int -> order
    Coq: Z * Z -> comparison
  *)
  Definition compare '((i1, i2): Z * Z):comparison :=  
    match (i1 =? i2) with
    | true  => Eq
    | false => match (i1 <? i2) with
               | true  => Lt
               | false => Gt
                end
   end.

  (* Already defined as *)
  (*
    ~  : -
  *)

  (* 
    Sml: int * int -> bool
    Coq: Z * Z -> bool
  *)
  (* Definition opeq i1 i2:bool := i1 =? i2.
  Notation "op=( x , y )" := (Z.eqb x y) (at level 70, no associativity) : Z_scope.
  Infix "=" := opeq : Z_scope. *)

  (* 
    Sml: int * int -> bool
    Coq: Z * Z -> bool
  *)
(*   Definition oplt i1 i2:bool := i1 <? i2.
  Notation "op<( x , y )" := (Z.ltb x y) (at level 70, no associativity) : Z_scope.
  Infix "<" := oplt : Z_scope. *)

  (* 
    Sml: int * int -> bool
    Coq: Z * Z -> bool
  *)
(*   Definition ople i1 i2:bool := i1 <=? i2.
  Notation "op<=( x , y )" := (Z.leb x y) (at level 70, no associativity) : Z_scope.
  Infix "<=" := ople : Z_scope. *)

  (* 
    Sml: int * int -> bool
    Coq: Z * Z -> bool
  *)
(*   Definition opgt i1 i2:bool := i1 >? i2.
  Notation "op>( x , y )" := (Z.gtb x y) (at level 70, no associativity) : Z_scope.
  Infix ">" := opgt : Z_scope. *)

  (* 
    Sml: int * int -> bool
    Coq: Z * Z -> bool
  *)
(*   Definition opge i1 i2:bool := i1 >=? i2.
  Notation "op>=( x , y )" := (Z.geb x y) (at level 70, no associativity) : Z_scope.
  Infix ">=" := opge : Z_scope. *)

  (* 
    Sml: int -> int 
    Coq: Z -> Z
  *)
  Definition abs (i: Z): Z := if (i >=? 0) then i else -1 * i.

  (* 
    Sml: int * int -> int
    Coq: Z * Z -> Z
  *)
  Definition min '((i1, i2): Z * Z):Z := 
    match (i1 <=? i2) with
    | true  => i1
    | false => i2
    end.

  (* 
    Sml: int * int -> int
    Coq: Z * Z -> Z
  *)
  Definition max '((i1, i2): Z * Z):Z := 
    match (i1 >=? i2) with
    | true  => i1
    | false => i2
    end.

  (* 
    Sml: int -> Int.int
    Coq: Z -> Z
  *)
  Definition sign (i: Z): Z :=
    match (i <? 0) with
    | true  => -1
    | fasle => match (i >? 0) with
               | true  => 1
               | false => 0
               end
    end.

  (* 
    Sml: int * int -> bool
    Coq: Z * Z -> bool
  *)
  Definition sameSign '((i1, i2): Z * Z):bool := sign i1 =? sign i2.

  (*Sml Spacific*)
  (* 
    Definition fmt.
    scan
  *)

  Local Open Scope char_scope.

  Local Definition digitToZ (c: ascii) : option Z :=
    match c with
    | "-" => Some 10
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | _ => None
    end.

  Local Open Scope string_scope. 

  Local Fixpoint readZ (s: string) (acc: Z) : option Z :=
  match s with
  | "" => Some acc
  | String c s' => match digitToZ c with
                   | Some 10 => match (readZ s' acc) with
                               | Some n => Some (-n)
                               | None => None
                               end
                   | Some n => readZ s' (10 * acc + n)
                   | None => None
                   end
  end.

  (* 
    Sml: string -> int option
    Coq: string -> option Z
  *)
  Definition fromString (s: string): option Z := 
    if (String.eqb "" s) then None else readZ s 0.

  Local Open Scope nat_scope.

  Local Definition natToDigit (n: nat) : ascii :=
    match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
    end.

  Local Fixpoint writeNat (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNat time' n' acc'
      end
  end.

  Local Definition toString' (n : nat) : string := writeNat n n "".

  Local Open Scope Z_scope.

  (* 
    Sml: int -> string
    Coq: Z -> string
  *)
  Definition toString (n: Z): string := 
    let n' := Z.abs_nat(n) in 
    match (sameSign(n, (-1)))  with
    | true  => "-" ++ (toString' n')
    | false => (toString' n')
    end.

End Int.