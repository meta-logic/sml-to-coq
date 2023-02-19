Require Import Ascii.
Require Import String.
From stringCvtSml Require Import stringCvtSml.
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

  (* Not Implemented *)
  (* 
    scan
  *)

(*   Local Open Scope char_scope. *)

  Local Definition digitToZ (c: ascii) : option Z :=
    match c with
    | "0"%char => Some 0
    | "1"%char => Some 1
    | "2"%char => Some 2
    | "3"%char => Some 3
    | "4"%char => Some 4
    | "5"%char => Some 5
    | "6"%char => Some 6
    | "7"%char => Some 7
    | "8"%char => Some 8
    | "9"%char => Some 9
    | _ => None
    end.

  (* Local Open Scope string_scope.  *)

  Local Fixpoint readZ (s: string) (acc: Z) : option Z :=
  match s with
  | ""%string => Some acc
  | String c s' => match digitToZ c with
                   | Some n => readZ s' (10 * acc + n)
                   | None => None
                   end
  end.

  (* 
    Sml: string -> int option
    Coq: string -> option Z
  *)
  Definition fromString (s: string): option Z := 
    match s with
    | ""%string => None
    | String c s' => match Ascii.eqb c "-" with
                     | true  => match (readZ s' 0) with
                                | Some n => Some (-n)
                                | None   => None
                                end
                     | false => readZ s 0
                     end
    end.

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
    | 9 => "9"
    | 10 => "A"
    | 11 => "B"
    | 12 => "C"
    | 13 => "D"
    | 14 => "E"
    | _ => "F"
    end.

  Local Fixpoint writeBin (time n: nat) (acc: string): string := 
    let acc' := String (natToDigit (n mod 2)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 2 with
      | 0 => acc'
      | n' => writeBin time' n' acc'
      end
    end.

  Local Fixpoint writeOct (time n: nat) (acc: string): string := 
    let acc' := String (natToDigit (n mod 8)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 8 with
      | 0 => acc'
      | n' => writeOct time' n' acc'
      end
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

  Local Fixpoint writeHex (time n: nat) (acc: string): string := 
    let acc' := String (natToDigit (n mod 16)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 16 with
      | 0 => acc'
      | n' => writeHex time' n' acc'
      end
    end.



  Local Definition toBinStr' (time n : nat) : string := writeBin time n "".

  Local Definition toOctStr' (time n : nat) : string := writeOct time n "".

  Local Definition toString' (n : nat) : string := writeNat n n "".

  Local Definition toHexStr' (time n : nat) : string := writeHex time n "".

  Local Close Scope nat_scope.

  Local Definition toBinStr (n: Z): string :=
    let n' := Z.abs_nat(n) in
    let time := (Nat.add (Nat.log2 n') 1) in
    match (sameSign(n, (-1)))  with
    | true  => "-" ++ (toBinStr' time n')
    | false => (toBinStr' time n')
    end.

  Local Definition toOctStr (n: Z): string :=
    let n' := Z.abs_nat(n) in
    let time := (Nat.add (Nat.div (Nat.log2 n') (Nat.log2 8)) 1) in
    match (sameSign(n, (-1)))  with
    | true  => "-" ++ (toOctStr' time n')
    | false => (toOctStr' time n')
    end.

  (* 
    Sml: int -> string
    Coq: Z -> string
  *)
  Definition toString1 (n: Z): string := 
    let n' := Z.abs_nat(n) in 
    match (sameSign(n, (-1)))  with
    | true  => "-" ++ (toString' n')
    | false => (toString' n')
    end.

  Local Definition toHexStr (n: Z): string :=
    let n' := Z.abs_nat(n) in
    let time := (Nat.add (Nat.div (Nat.log2 n') (Nat.log2 16)) 1) in
    match (sameSign(n, (-1)))  with
    | true  => "-" ++ (toHexStr' time n')
    | false => (toHexStr' time n')
    end.

  (*
    Sml: StringCvt.radix -> int -> string
    Coq: StringCvt.radix -> Z -> string
  *)
  Definition fmt (radix: StringCvt.radix) (i:Z): string := 
    match radix with 
    | StringCvt.BIN => toBinStr i
    | StringCvt.DEC => toString1 i
    | StringCvt.OCT => toOctStr i
    | StringCvt.HEX => toHexStr i
    end.

End Int.