Require Import ZArith.
Open Scope Z_scope. 


Module Int.
  Definition toLarge (i: Z):Z   := i.

  Definition fromLarge (i: Z):Z := i.

  Definition toInt (i: Z):Z     := i.

  Definition fromInt (i: Z):Z   := i.

  Definition precision:option Z := Some 31.

  Definition minInt:option Z    := Some (-1073741824).

  Definition maxInt:option Z    := Some 1073741823.

  (*
   Definition + : Z * Z -> Z
   Definition - : Z * Z -> Z
   Definition * : Z * Z -> Z
  *)

  Definition div '((i1, i2): Z * Z):Z := i1 / i2.
  Infix "div" := div (at level 40, left associativity).

  (* Definition mod: Z * Z -> Z*)

  Definition quot '((i1, i2): Z * Z):Z := (i1 -(i1 mod 12)) / i2.

  Definition rem '((i1, i2): Z * Z):Z := i1 mod i2.
  Infix "rem" := rem (at level 40, no associativity).

  (*un-curry*)
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
    <  : <?
    <= : <=?
    >  : >?
    >= : <=?
    ~  : -
  *)

  Definition abs (i: Z): Z := -1 * i.

  Definition min '((i1, i2): Z * Z):Z := 
    match (i1 <=? i2) with
    | true  => i1
    | false => i2
    end.

  Definition max '((i1, i2): Z * Z):Z := 
    match (i1 >=? i2) with
    | true  => i1
    | false => i2
    end.

  Definition sign (i: Z): Z :=
    match (i <? 0) with
    | true  => -1
    | fasle => match (i >? 0) with
               | true  => 1
               | false => 0
               end
    end.

  Definition sameSign '((i1, i2): Z * Z):bool := sign i1 =? sign i2.

  (*Sml Spacific*)
  (* 
    Definition fmt.
    scan
  *)

  Require Import Ascii.
  Open Scope char_scope.

  Definition digitToZ (c: ascii) : option Z :=
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

  Require Import String.
  Open Scope string_scope. 

  Fixpoint readZ (s: string) (acc: Z) : option Z :=
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

  Definition fromString (s: string): option Z := readZ s 0.

  Open Scope nat_scope.
  Definition natToDigit (n: nat) : ascii :=
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

  Fixpoint writeNat (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNat time' n' acc'
      end
  end.

  Definition toString' (n : nat) : string := writeNat n n "".

  Open Scope Z_scope.
  Definition toString (n: Z): string := 
    let n' := Z.abs_nat(n) in 
    match (sameSign(n, (-1)))  with
    | true  => "-" ++ (toString' n')
    | false => (toString' n')
    end.

End Int.


