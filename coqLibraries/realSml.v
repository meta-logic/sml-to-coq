Require Import Bool.
Require Import ZArith.
Require Import Floats.
Open Scope float_scope.

Module Real.

  Definition radix        := two.

  Definition precision    := prec.

  Definition maxFinite    := 1.79769313486E308%float.

  Definition minPos       := 4.94065645841E-324%float.

  Definition minNormalPos := 2.22507385851E-308%float.

  Definition posInf       := infinity .

  Definition negInf       := neg_infinity .

  (*
   already defined Notations
   + : +
   - : -
   * : *
   / : /
   ~ : -
  *)

  (* Definition rem  is defined down*)

  Definition mp (a b c:float):float := a*b+c.
  Notation "*+( x , y , z )" := (mp x y z) (at level 40, left associativity).

  Definition mm (a b c:float):float := a*b-c.
  Notation "*-( x , y , z )" := (mm x y z) (at level 40, left associativity).

  Definition abs (r:float):float := abs r.

  Definition min '((r1,r2):float*float):float :=
    if r1 < r2 then r1 else r2.

  Definition max '((r1,r2):float*float):float :=
    if r1 < r2 then r2 else r1.

  (* It should raise exception if nan is passed to it, but since 
     Coq doesn't support exceptions, then it will return 0 *)
  Definition sign (r:float):float := 
    if (is_zero r) || (is_nan r) then zero else
    match (get_sign r) with
    | true  => (-one)%float
    | false => one
    end.

  Definition signBit (r:float):bool := get_sign r.

  Definition sameSign '((r1, r2):float*float):bool := 
    Bool.eqb (signBit r1) (signBit r2).

  Definition copySign '((r1, r2):float*float):float :=
    if sameSign(r1,r2) then r1 else 
    if sameSign(r2,1)  then abs r1 else -1 * r1.

  Definition compareReal '((r1, r2):float*float):float_comparison :=
    compare r1 r2.

  (* It should raise exception for unordered arguments, but since 
     Coq doesn't support exceptions, then it will return Eq *)
  Definition compare '((r1, r2):float*float):comparison :=
    match (compare r1 r2) with
    | FLt => Lt
    | FGt => Gt
    | _   => Eq
    end.

  (*
  already defined notations
   == : ==
   < : <
   <= :<=
  *)

  Notation "op<( x , y )" := (ltb x y) (at level 70, no associativity) : float_scope.

  Notation "op<=( x , y )" := (leb x y) (at level 70, no associativity) : float_scope.

  Definition opgt x y:bool := ltb y x. 
  Notation "op>( x , y )" := (opgt x y) (at level 70, no associativity) : float_scope.
  Infix ">" := opgt (at level 70) : float_scope.

  Definition opge x y:bool := leb y x. 
  Notation "op>=( x , y )" := (opge x y) (at level 70, no associativity) : float_scope.
  Infix ">=" := opge (at level 70) : float_scope.

  Definition opne x y:bool := Bool.eqb false (eqb y x). 
  Infix "!=" := opne (at level 70) : float_scope.

  Definition opne' x y:bool := (x == nan) || (y == nan) ||
                               Bool.eqb false (eqb y x). 
  Infix "?=" := opne' (at level 70) : float_scope.

  Definition unordered '((x,y):float*float):bool := (is_nan x) || (is_nan y).

  Definition isFinite (r:float):bool := is_finite r.

  Definition isNan (r:float):bool := is_nan r.

  Definition isNormal (r:float):bool := 
    (isFinite r) && (r != zero) && (abs(r) >= minNormalPos) .

  Definition class (r:float):float_class := classify r.

  (* Translating this will be annoying *)
  Record flt : Set := mkflt { man : float; exp : BinNums.Z}.

  (* Translating this will be annoying *)
  Definition toManExp (r:float):flt:= 
    let (man, exp) := (frexp r) in (mkflt (man) (exp)).

  (* Translating this will be annoying *)
  Definition fromManExp '(r:flt):float := 
    let (man, exp) := r in ldexp man exp.

  Definition maxInt := 4503599627370496.0.

  Definition whole' (x:float):float := 
    match (x > 0.0) with
    | true  => x-0.5+maxInt-maxInt
    | false => match (x < 0.0) with
               | true  => x+0.5-maxInt+maxInt
               | false => x end
    end.

  (* It returns x-1 if x is positive whole number 
     or x+1 is negative whole number *)
  Definition exWhole' (x:float):float := 
    match (x > 0.0) with
    | true  => match (x > 0.5) with
               | true  => x-0.5+maxInt-maxInt
               | false => whole'(x+1.0)-1.0 end
    | false => match (x < 0.0) with
               | true  => match (x < -0.5) with
                         | true  => x+0.5-maxInt+maxInt
                         | false => whole'(x-1.0)+1.0 end
               | false => x end
    end.

  (* Translating this will be annoying *)
  Record nmbr : Set := mknmbr { whole : float; frac : float}.

  Definition split (x:float):nmbr := 
    let w := exWhole' x in let f := x-w in
	  match (abs f) == 1.0 with
    | true  => (mknmbr (w+f) (0.0))
    | false => (mknmbr (w) (f))
    end.

  Definition realMod (x:float):float :=
    let f := x - exWhole' x in 
    match (abs f) == 1.0 with
    | true  => 0.0
    | false => f
    end.

  Definition exWhole (x:float) := if (realMod x) == 0 then x else exWhole' x.

  Definition rem '((x, y):float*float):float :=
    if (x == posInf) || (y == zero) then nan else
    if (y == posInf) then x else
    let n := (x/y) - realMod(x/y) in x - (n * y).

  Definition nextAfter '((r, t):float*float):float := 
    match ((isNan r) || (isNan t)) with
    | true  => nan
    | false => match ((r == posInf) || (r == negInf)) with
               | true  => r
               | flase => match (r < t) with
                          | true  => next_up r
                          | false => next_down r
                          end
               end
    end.

  (* It should raise Overflow if x is an infinity, and raises Div if x is NaN.
     But, since Coq doesn't have exceptions then it will just return them.  *)
  Definition checkFloat (r:float):float := r.

  Definition realFloor (r:float):float := 
    if (r < 0) then (if (realMod r) == 0 then r else (r - (realMod r)) -1) else
    (r - (realMod r)).

  Definition realCeil (r:float):float :=
    if (r < 0) then (r - (realMod r)) else 
    if (realMod r) == 0 then r else (r - (realMod r)) + 1.

  Definition realTrunc (r:float):float := (exWhole r).

  Definition realRound (r:float):float := 
    match (r < 0) with
    | true  => if (((exWhole r) - r) >= 0.5) then realFloor r else realCeil r
    | flase => if (r - ((exWhole r)) >= 0.5) then realCeil r else realFloor r
    end.

  Definition f2zDigit (f:float):Z :=
    if (f == zero) then 0%Z else
    if (f == one) then 1%Z else
    if (f == two) then 2%Z else
    if (f == 3) then 3%Z else 
    if (f == 4) then 4%Z else
    if (f == 5) then 5%Z else
    if (f == 6) then 6%Z else
    if (f == 7) then 7%Z else
    if (f == 8) then 8 else
    if (f == 9) then 9 else 0%Z.

  Inductive rounding_mode :=
    | TO_NEAREST
    | TO_NEGINF
    | TO_POSINF
    | TO_ZERO.
Compute f2zDigit 2.
Compute realTrunc(215 / 10).

  Fixpoint toInt' (f:float) (time:nat) (acc:float) :float :=
    match time with
    | 0       => acc
    | S time' => let m := f - (10 * realTrunc(f / 10)) in 
                 toInt' (realTrunc(f / 10)) time' ( 10 * acc +  m)
    end.

  Fixpoint toInt'' (f:float) (time:nat) (acc:Z) :Z :=
    match time with
    | 0       => acc
    | S time' => let m := f - (10 * realTrunc(f / 10)) in 
                 toInt'' (realTrunc(f / 10)) time' ( 10 * acc + (f2zDigit m))
    end.

Compute toInt'' (toInt' 1234567 7 0) 7 0.
  (* Fixpoint numDigits (f:float):nat :=
    if (f==0) then (0%nat) else 1 + numDigits(realTrunc(f / 10)) n. *)

  (* For now The user should give me how many digits, until we fix numdigits,
     It's also so inefficient *)
  (* It should also raise an exception for infinity and nan but since Coq 
     doesn't support exceptions then it will return 0 *)
  Definition toInt (m:rounding_mode) (f:float) (nd:nat):Z :=
    match m with 
    | TO_NEAREST => if (f < 0) then -1 * (toInt'' (toInt' (abs(realRound f)) nd 0) nd 0)
                    else toInt'' (toInt' (realRound f) nd 0) nd 0
    | TO_NEGINF  => if (f < 0) then -1 * (toInt'' (toInt' (abs(realFloor f)) nd 0) nd 0)
                    else toInt'' (toInt' (realFloor f) nd 0) nd 0
    | TO_POSINF  => if (f < 0) then -1 * (toInt'' (toInt' (abs(realCeil f)) nd 0) nd 0)
                    else toInt'' (toInt' (realCeil f) nd 0) nd 0
    | TO_ZERO    => if (f < 0) then -1 * (toInt'' (toInt' (abs(realCeil f)) nd 0) nd 0)
                    else toInt'' (toInt' (realFloor f) nd 0) nd 0
     end.

  (* For now The user should give me how many digits, until we fix numdigits,
     It's also so inefficient *)
  (* It should also raise an exception for infinity and nan but since Coq 
     doesn't support exceptions then it will return 0 *)
  Definition toLargeInt (m:rounding_mode) (f:float) (nd:nat):Z := toInt m f nd.

  (* For now The user should give me how many digits, until we fix numdigits,
     It's also so inefficient *)
  (* It should also raise an exception for infinity and nan but since Coq 
     doesn't support exceptions then it will return 0 *)
  Definition floor (r:float) (nd:nat):Z := toInt TO_NEGINF (realFloor r) nd.

  (* For now The user should give me how many digits, until we fix numdigits,
     It's also so inefficient *)
  (* It should also raise an exception for infinity and nan but since Coq 
     doesn't support exceptions then it will return 0 *)
  Definition ceil (r:float) (nd:nat):Z := toInt TO_POSINF (realCeil r) nd.

  (* For now The user should give me how many digits, until we fix numdigits,
     It's also so inefficient *)
  (* It should also raise an exception for infinity and nan but since Coq 
     doesn't support exceptions then it will return 0 *)
  Definition trunc (r:float) (nd:nat):Z := toInt TO_ZERO (realTrunc r) nd.

  (* For now The user should give me how many digits, until we fix numdigits,
     It's also so inefficient *)
  (* It should also raise an exception for infinity and nan but since Coq 
     doesn't support exceptions then it will return 0 *)
  Definition round (r:float) (nd:nat):Z := toInt TO_NEAREST (realRound r) nd.

  Definition fromInt (i:Z):float := of_int63 (Int63.of_Z(i)).

  Definition fromLargeInt (i:Z):float := of_int63 (Int63.of_Z(i)).

  Definition toLarge (r:float):float := r.

  Definition fromLarge (m:rounding_mode) (f:float):float := f.

(* Not implemented yet, and Sml spacific
   fmt
   toString
   scan
   fromString
   toDecimal
   fromDecimal
 *)

End Real.