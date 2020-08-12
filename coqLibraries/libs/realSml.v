Require Import Bool.
Require Import intSml.
Close Scope Z_scope.
Require Import Ascii.
Require Import stringSml.
Require Export Floats.
Require Import listSml.
Require Import stringCvtSml.
Require Import IEEERealSml.

Module Real.

  Open Scope float_scope.

  Axiom  DomainException : forall{a}, a.

  Axiom  UnorderedException : forall{a}, a.

  Axiom  OverflowException : forall{a}, a.

  Axiom  DivException : forall{a}, a.

  Axiom  SizeException : forall{a}, a.

  (*
    Sml: int
    Coq: Z
  *)
  Definition radix        := 2%Z.

  (*
    Sml: int
    Coq: Z
  *)
  Definition precision    := prec.

  (*
    Sml: real
    Coq: float
  *)
  Definition maxFinite    := 1.79769313486E308%float.

  (*
    Sml: real
    Coq: float
  *)
  Definition minPos       := 4.94065645841E-324%float.

  (*
    Sml: real
    Coq: float
  *)
  Definition minNormalPos := 2.22507385851E-308%float.

  (*
    Sml: real
    Coq: float
  *)
  Definition posInf       := infinity .

  (*
    Sml: real
    Coq: float
  *)
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

  (*
    Sml: real * real * real -> real
    Coq: float * float * float -> float
  *)
  Local Definition mp (a b c:float):float := a*b+c.
  Local Notation "*+( x , y , z )" := (mp x y z) (at level 40, left associativity).

  (*
    Sml: real * real * real -> real
    Coq: float * float * float -> float
  *)
  Local Definition ms (a b c:float):float := a*b-c.
  Local Notation "*-( x , y , z )" := (ms x y z) (at level 40, left associativity).

  (*
    Sml: real -> real
    Coq: float -> float
  *)
  Definition abs (r:float):float := abs r.

  (*
    Sml: real * real -> real
    Coq: float * float -> float
  *)
  Definition min '((r1,r2):float*float):float :=
    if r1 < r2 then r1 else r2.

  (*
    Sml: real * real -> real
    Coq: float * float -> float
  *)
  Definition max '((r1,r2):float*float):float :=
    if r1 < r2 then r2 else r1.

  (*
    Sml: real -> int
    Coq: float -> Z
    - It should raise exception if nan is passed to it, but since 
      Coq doesn't support exceptions, then it will return the axiom
      DomainException
  *)
  Definition sign (r:float):Z := 
    if (is_zero r) then 0%Z else
    if (is_nan r) then DomainException else
    match (get_sign r) with
    | true  => (-1)%Z
    | false => 1%Z
    end.

  (*
    Sml: real -> bool
    Coq: float -> bool
  *)
  Definition signBit (r:float):bool := get_sign r.

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Definition sameSign '((r1, r2):float*float):bool := 
    Bool.eqb (signBit r1) (signBit r2).

  (*
    Sml: real * real -> float
    Coq: float * float -> float
  *)
  Definition copySign '((r1, r2):float*float):float :=
    if sameSign(r1,r2) then r1 else 
    if sameSign(r2,1)  then abs r1 else -1 * r1.

  (*
    Sml: real * real -> IEEEReal.real_order
    Coq: float * float -> IEEEReal.float_comparison
  *)
  Definition compareReal '((r1, r2):float*float):IEEEReal.real_order :=
    match compare r1 r2 with
    | FLt => IEEEReal.LESS
    | FGt => IEEEReal.GREATER
    | FEq => IEEEReal.EQUAL
    | _   => IEEEReal.UNORDERED
    end.

  (*
    Sml: real * real -> IEEEReal.real_order
    Coq: float * float -> float_comparison
    - It should raise exception for unordered arguments, but since 
      Coq doesn't support exceptions, then it will return the axiom
      UnorderedException   
  *)
  Definition compare '((r1, r2):float*float):comparison :=
    if (is_nan r1) || (is_nan r2) then UnorderedException else
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

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Local Notation "op<( x , y )" := (ltb x y) (at level 70, no associativity) : float_scope.

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Local Notation "op<=( x , y )" := (leb x y) (at level 70, no associativity) : float_scope.

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Local Definition opgt x y:bool := ltb y x. 
  Local Notation "op>( x , y )" := (opgt x y) (at level 70, no associativity) : float_scope.
  Local Infix ">" := opgt (at level 70) : float_scope.

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Local Definition opge x y:bool := leb y x. 
  Local Notation "op>=( x , y )" := (opge x y) (at level 70, no associativity) : float_scope.
  Local Infix ">=" := opge (at level 70) : float_scope.

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Local Definition opne x y:bool := Bool.eqb false (eqb y x). 
  Local Infix "!=" := opne (at level 70) : float_scope.

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Local Definition opne' x y:bool := (x == nan) || (y == nan) ||
                               Bool.eqb false (eqb y x). 
(*   Infix "?=" := opne' (at level 70) : float_scope. *)

  (*
    Sml: real * real -> bool
    Coq: float * float -> bool
  *)
  Definition unordered '((x,y):float*float):bool := (is_nan x) || (is_nan y).

  (*
    Sml: real -> bool
    Coq: float -> bool
  *)
  Definition isFinite (r:float):bool := is_finite r.

  (*
    Sml: real -> bool
    Coq: float -> bool
  *)
  Definition isNan (r:float):bool := is_nan r.

  (*
    Sml: real -> bool
    Coq: float -> bool
  *)
  Definition isNormal (r:float):bool := 
    (isFinite r) && (r != zero) && (abs(r) >= minNormalPos) .

  (*
    Sml: real -> IEEEReal.float_class
    Coq: float -> IEEEReal.float_class
  *)
  Definition class (r:float):IEEEReal.float_class := 
    match classify r with
    | PNormal => IEEEReal.NORMAL
    | NNormal => IEEEReal.NORMAL
    | PSubn => IEEEReal.SUBNORMAL
    | NSubn => IEEEReal.SUBNORMAL
    | PZero => IEEEReal.ZERO
    | NZero => IEEEReal.ZERO
    | PInf => IEEEReal.INF
    | NInf => IEEEReal.INF
    | NAN => IEEEReal.NAN
    end.

  Record flt : Set := mkflt { man : float; exp : BinNums.Z}.

  (*
    Sml: real -> {man : real, exp : int}
    Coq: float -> Real.flt
    - Translating this will be annoying 
  *)
  Definition toManExp (r:float):Real.flt:= 
    let (man, exp) := (frexp r) in (mkflt (man) (exp)).

  (*
    Sml: {man : real, exp : int} -> real
    Coq: Real.flt -> float
    - Translating this will be annoying 
  *)
  Definition fromManExp '(r:Real.flt):float := 
    let (man, exp) := r in ldexp man exp.

  Definition maxInt := 4503599627370496.0.

  Local Definition whole' (x:float):float := 
    match (x > 0.0) with
    | true  => x-0.5+maxInt-maxInt
    | false => match (x < 0.0) with
               | true  => x+0.5-maxInt+maxInt
               | false => x end
    end.

  (* It returns x-1 if x is positive whole number 
     or x+1 is negative whole number *)
  Local Definition exWhole' (x:float):float := 
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

  Record nmbr : Set := mknmbr { whole : float; frac : float}.

  (*
    Sml: real -> {whole : real, frac : real}
    Coq: float -> Real.nmbr
  *)
  Definition split (x:float): Real.nmbr := 
    let w := exWhole' x in let f := x-w in
    match (abs f) == 1.0 with
    | true  => (mknmbr (w+f) (0.0))
    | false => (mknmbr (w) (f))
    end.

  (*
    Sml: real -> real
    Coq: float -> float
  *)
  Definition realMod (x:float):float :=
    let f := x - exWhole' x in 
    match (abs f) == 1.0 with
    | true  => 0.0
    | false => f
    end.

  Local Definition exWhole (x:float) := if (realMod x) == 0 then x else exWhole' x.

  (*
    Sml: real * real -> real
    Coq: float * float -> float
  *)
  Definition rem '((x, y):float*float):float :=
    if (x == posInf) || (y == zero) then nan else
    if (y == posInf) then x else
    let n := (x/y) - realMod(x/y) in x - (n * y).

  (*
    Sml: real * real -> real
    Coq: float * float -> float
  *)
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

  (*
    Sml: real -> real
    Coq: float -> float
    - It should raise Overflow if x is an infinity, and raises Div if x is NaN.
      But, since Coq doesn't have exceptions then it will return the axioms
      OverflowException, and DivException
  *)
  Definition checkFloat (r:float):float := 
    if (r != infinity) then OverflowException else
    if (isNan r) then DivException else r.

  (*
    Sml: real -> real
    Coq: float -> float
  *)
  Definition realFloor (r:float):float := 
    if (r < 0) then (if (realMod r) == 0 then r else (r - (realMod r)) -1) else
    (r - (realMod r)).

  (*
    Sml: real -> real
    Coq: float -> float
  *)
  Definition realCeil (r:float):float :=
    if (r < 0) then (r - (realMod r)) else 
    if (realMod r) == 0 then r else (r - (realMod r)) + 1.

  (*
    Sml: real -> real
    Coq: float -> float
  *)
  Definition realTrunc (r:float):float := (exWhole r).

  (*
    Sml: real -> real
    Coq: float -> float
  *)
  Definition realRound (r:float):float := 
    match (r < 0) with
    | true  => if (((exWhole r) - r) >= 0.5) then realFloor r else realCeil r
    | flase => if (r - ((exWhole r)) >= 0.5) then realCeil r else realFloor r
    end.

  Local Definition f2zDigit (f:float):Z :=
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

  Local Fixpoint toInt' (f:float) (time:nat) (acc:float) :float :=
    match time with
    | 0       => acc
    | S time' => let m := f - (10 * realTrunc(f / 10)) in 
                 toInt' (realTrunc(f / 10)) time' ( 10 * acc +  m)
    end.

  Local Fixpoint toInt'' (f:float) (time:nat) (acc:Z) :Z :=
    match time with
    | 0       => acc
    | S time' => let m := f - (10 * realTrunc(f / 10)) in 
                 toInt'' (realTrunc(f / 10)) time' ( 10 * acc + (f2zDigit m))
    end.

  (*  (*
    requires : f >= 0
  *)
  Fixpoint numDigits' (f: spec_float) (acc: nat): option nat :=
    match f with
    | S754_nan => None
    | S754_infinity(s) => None
    | S754_zero(s) => Some acc
    | S754_finite s m e => 
      if (SF2Prim f) >= 0 then Some acc else 
      numDigits' (Prim2SF((SF2Prim f) / 10)) (Nat.add acc 1)
    end.

  Definition numDigits (f:float):nat :=
    numDigits' (Prim2SF f) (0%nat). *)

  (*
    Sml: IEEEReal.rounding_mode -> real -> int
    Coq: rounding_mode -> float -> nat -> Z
    - For now The user should give me how many digits, until we fix numdigits,
      It's also kind of inefficient.
    - It should also raise an exception for infinity and nan but since Coq 
      doesn't support exceptions then it will return the axioms
      OverflowException, and DivException
    *)
  Definition toInt (m: IEEEReal.rounding_mode) (f:float) (nd:nat):Z :=
    if (f == infinity) then OverflowException else
    if (isNan f) then DivException else
    match m with 
    | IEEEReal.TO_NEAREST => if (f < 0) then -1 * (toInt'' (toInt' (abs(realRound f)) nd 0) nd 0)
                    else toInt'' (toInt' (realRound f) nd 0) nd 0
    | IEEEReal.TO_NEGINF  => if (f < 0) then -1 * (toInt'' (toInt' (abs(realFloor f)) nd 0) nd 0)
                    else toInt'' (toInt' (realFloor f) nd 0) nd 0
    | IEEEReal.TO_POSINF  => if (f < 0) then -1 * (toInt'' (toInt' (abs(realCeil f)) nd 0) nd 0)
                    else toInt'' (toInt' (realCeil f) nd 0) nd 0
    | IEEEReal.TO_ZERO    => if (f < 0) then -1 * (toInt'' (toInt' (abs(realCeil f)) nd 0) nd 0)
                    else toInt'' (toInt' (realFloor f) nd 0) nd 0
     end.

  (*
    Sml: rounding_mode -> real -> LargeInt.int
    Coq: rounding_mode -> float -> nat -> Z
    - For now The user should give me how many digits, until we fix numdigits,
      It's also kind of inefficient.
    - It should also raise an exception for infinity and nan but since Coq 
      doesn't support exceptions then it will return the axioms
      OverflowException, and DivException
    *)
  Definition toLargeInt (m:IEEEReal.rounding_mode) (f:float) (nd:nat):Z := toInt m f nd.

  (*
    Sml: real -> int
    Coq: float -> nat -> Z
    - For now The user should give me how many digits, until we fix numdigits,
      It's also kind of inefficient.
    - It should also raise an exception for infinity and nan but since Coq 
      doesn't support exceptions then it will return the axioms
      OverflowException, and DivException
    *)
  Definition floor (r:float) (nd:nat):Z := toInt (IEEEReal.TO_NEGINF) (realFloor r) nd.

  (*
    Sml: real -> int
    Coq: float -> nat -> Z
    - For now The user should give me how many digits, until we fix numdigits,
      It's also kind of inefficient.
    - It should also raise an exception for infinity and nan but since Coq 
      doesn't support exceptions then it will return the axioms
      OverflowException, and DivException
    *)
  Definition ceil (r:float) (nd:nat):Z := toInt (IEEEReal.TO_POSINF) (realCeil r) nd.

  (*
    Sml: real -> int
    Coq: float -> nat -> Z
    - For now The user should give me how many digits, until we fix numdigits,
      It's also kind of inefficient.
    - It should also raise an exception for infinity and nan but since Coq 
      doesn't support exceptions then it will return the axioms
      OverflowException, and DivException
    *)
  Definition trunc (r:float) (nd:nat):Z := toInt (IEEEReal.TO_ZERO) (realTrunc r) nd.

  (*
    Sml: real -> int
    Coq: float -> nat -> Z
    - For now The user should give me how many digits, until we fix numdigits,
      It's also kind of inefficient.
    - It should also raise an exception for infinity and nan but since Coq 
      doesn't support exceptions then it will return the axioms
      OverflowException, and DivException
    *)
  Definition round (r:float) (nd:nat):Z := toInt (IEEEReal.TO_NEAREST) (realRound r) nd.

  (*
    Sml: int -> real
    Coq: Z -> float
  *)
  Definition fromInt (i:Z):float := of_int63 (Int63.of_Z(i)).

  (*
    Sml: LargeInt.int -> real
    Coq: Z -> float
  *)
  Definition fromLargeInt (i:Z):float := of_int63 (Int63.of_Z(i)).

  (*
    Sml: real -> LargeReal.real
    Coq: float -> float
  *)
  Definition toLarge (r:float):float := r.

  (*
    Sml: IEEEReal.rounding_mode -> LargeReal.real -> real
    Coq: IEEEReal.rounding_mode -> float -> float
  *)
  Definition fromLarge (m:IEEEReal.rounding_mode) (f:float):float := f.


  Local Definition FToDigit (f: float) : string :=
    if PrimFloat.eqb f 0 then "0" else
    if PrimFloat.eqb f 1 then "1" else
    if PrimFloat.eqb f 2 then "2" else
    if PrimFloat.eqb f 3 then "3" else
    if PrimFloat.eqb f 4 then "4" else
    if PrimFloat.eqb f 5 then "5" else
    if PrimFloat.eqb f 6 then "6" else
    if PrimFloat.eqb f 7 then "7" else
    if PrimFloat.eqb f 8 then "8" else "9".


  Local Fixpoint writeFloat (time: nat) (n: float) (acc :string) :string :=
    let acc' := String.append (FToDigit (rem(n, 10))) acc in
    match time with
    | 0 => acc'
    | S time' =>
      if PrimFloat.eqb (exWhole(n / 10)) 0 then acc' else
      writeFloat time' (exWhole(n / 10)) acc'
    end.


  Local Fixpoint writeFloat_dec (time: nat) (n: float) (acc :string) :string :=
    let acc' :=  String.append acc (FToDigit (exWhole(n*10))) in
    match time with
      | 0 => acc'
      | S time' =>
        if PrimFloat.eqb (realMod(n*10)) 0 then acc' else
        writeFloat_dec time' (realMod(n*10)) acc'
    end.

  (* 
    Sml: real -> string
    Coq: float -> nat -> string
    - For now The user should give me how many digits, until we fix numdigits.
  *)
  Definition toString (r: float) (nd: nat): string:= 
    let r' := split r in 
    match r' with 
    | {| whole := w; frac := f|} => 
      let s' := (writeFloat nd (abs w) "") in
      match (sameSign(r, (-1)))  with
      | true  => "-" ++ s' ++ "." ++
                 (writeFloat_dec (Nat.sub nd (String.length s')) (abs f) "")
      | false => s' ++ "." ++ 
                 (writeFloat_dec (Nat.sub nd (String.length s')) (abs f) "")
      end
   end.


  (* 
    Sml: real -> IEEEReal.decimal_approx
    Coq: float -> nat -> IEEEReal.decimal_approx
  *)
  Definition toDecimal (f: float) (nd: nat): IEEEReal.decimal_approx :=
    match IEEEReal.fromString (toString f nd) with
    | None => {| IEEEReal.class:=IEEEReal.NAN;  IEEEReal.sign:=false;
                 IEEEReal.digits:=[]; IEEEReal.exp:=0%Z|}
    | Some x => x
    end.

  Local Fixpoint compDigits (d: list Z) (acc: float) (i: Z) :=
    match d with
    | [] => Some acc
    | x::d' => if Z.ltb x 0 || Z.gtb x 9 then None else
      compDigits d' (acc + ((fromInt x) / fromInt(Z.pow 10%Z i))) (Z.add i 1)
    end.

  (* 
    Sml: IEEEReal.decimal_approx -> real option
    Coq: IEEEReal.decimal_approx -> option float
  *)
  Definition fromDecimal (d: IEEEReal.decimal_approx): option float :=
    match d with  
    | {| IEEEReal.class:=c;  IEEEReal.sign:=s;
      IEEEReal.digits:=d; IEEEReal.exp:=e|} =>
      match c with
      | IEEEReal.NAN => Some ((if s then -1 else 1) * nan)
      | IEEEReal.INF => Some ((if s then -1 else 1) * infinity)
      | IEEEReal.ZERO => Some ((if s then -1 else 1) * zero)
      | _ => 
        match (compDigits d (0%float) (1%Z)) with
        | None => None
        | Some x => Some ((if s then -1 else 1) * x * (fromInt(Z.pow 10%Z e)))
        end
      end
    end.

  Local Definition digitToF (c: ascii) : option float :=
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

  Local Fixpoint readF_dec (s: string) (acc: float) : option float :=
    match s with
    | ""%string => Some acc
    | String c s' => match digitToF c with
                     | Some n => readF_dec s' (10 * acc + n)
                     | None => None
                     end
    end.

  Local Fixpoint readF (s: string) (acc: float) : option float :=
  match s with
  | ""%string => Some acc
  | String c s' => 
    match c with
    | "."%char => 
      let n' := readF_dec s' 0 in
      match n' with
      | Some n'' => 
          Some (acc + (n'' / fromInt(Z.pow 10%Z (Z.of_nat(String.length s')))))
      | None => None
      end
    | _ => 
      match digitToF c with
      | Some n => readF s' (10 * acc + n)
      | None => None
      end
    end
  end.

  (* 
    Sml: string -> real option
    Coq: string -> option float
  *)
  Fixpoint fromString (s: string): option float :=  
    match s with
    | ""%string => None
    | String c s' => match Ascii.eqb c "-" with
                     | true  => match (readF s' 0) with
                                | Some n => Some (-n)
                                | None   => None
                                end
                     | false => readF s 0
                     end
    end.

  Local Fixpoint compDigits' (d: list Z) (acc: float) (i: Z) :=
    match d with
    | [] => acc
    | x::d' =>
      compDigits' d' (acc + ((fromInt x) / fromInt(Z.pow 10%Z i))) (Z.add i 1)
    end.

  Local Fixpoint remZeros (l: list Z): list Z :=
    match l with
    | nil => nil
    | x::l' => if Z.eqb x 0 then remZeros l' else x::l'
    end.

  Local Definition fmtSCI (arg: option Z) (f: float) (nd: nat) :=
    match toDecimal f nd with 
    {| IEEEReal.class:=c;  IEEEReal.sign:=s;
    IEEEReal.digits:=d; IEEEReal.exp:=e|} =>
      let dLen := List.length d in
      let d' := remZeros d in
      let dLen' := List.length d' in
      let e' := Z.sub e 1 in
      match arg with
      | None   =>
        let s' := 
        (toString (((compDigits' (match Z.compare dLen' 7%Z with
        | Lt => d' ++ (List.tabulate(Z.sub 7%Z dLen', (fun x => 0%Z)))
        | Gt => List.take(d', 7%Z)
        | Eq => d' end) 0 1) + (if (Z.gtb dLen' 7%Z) then
        if (Z.gtb (List.nth(d',7%Z)) 4%Z) then (1/1e6) else 0 else 0))*10) nd) in
        let lex := String.size (Int.toString e') in
        let j := Z.add 7%Z lex in
        (String.append (String.substring(s', 0%Z, j))
        (String.append "E"%string  (Int.toString e')))
      | Some x =>
        let s' := 
        (toString (((compDigits' (match Z.compare dLen' (Z.add 1 x) with
        | Lt => d' ++ (List.tabulate(Z.sub (Z.add 1 x) dLen', (fun i => 0%Z)))
        | Gt => List.take(d', Z.sub dLen' (Z.add 1 x))
        | Eq => d' end) 0 1) + (if (Z.gtb dLen' (Z.add 1 x)) then
        if (Z.gtb (List.nth(d',(Z.add 1 x))) 4%Z)
        then (1 / fromInt(Z.pow 10%Z x)) else 0 else 0)) * 10) nd) in
        let lex := String.size (Int.toString e') in
        let j := Z.add (Z.add 1%Z x) lex in
        (String.append (String.substring(s', 0%Z, j))
        (String.append "E"%string  (Int.toString e')))
      end
    end.

  Local Fixpoint getDecPointInd (s: string) (pos: Z) :=
    match s with
    | ""%string => pos
    | String c s' => match Ascii.eqb c "." with
                     | true => pos
                     | false => getDecPointInd s' (Z.add pos 1)
                     end
    end.

  Local Definition digitToZ (c: ascii): Z :=
    match c with
    | "0"%char => 0%Z
    | "1"%char => 1%Z
    | "2"%char => 2%Z
    | "3"%char => 3%Z
    | "4"%char => 4%Z
    | "5"%char => 5%Z
    | "6"%char => 6%Z
    | "7"%char => 7%Z
    | "8"%char => 8%Z
    | "9"%char => 9%Z
    | _ => 10%Z
    end.

  Local Definition valOf (x: option float): float :=
    match x with
    | Some s => s
    | None   => UnorderedException
    end.

  Local Definition fmtFIX (arg: option Z) (f: float) (nd: nat) :=
    let s := toString f nd in
    let i := getDecPointInd s 0 in
    let numDec := Z.sub (String.size s) (Z.add i 1) in
    match arg with
    | None => 
      match Z.compare numDec 6%Z with
      | Lt => 
        String.append s 
        (String.implode(List.tabulate(Z.sub 6%Z numDec,(fun i=>"0"%char))))
      | Gt =>
        let j  := Z.sub (String.size s)(numDec - 6%Z) in
        let s' := String.substring(s,0%Z,j) in
        let l  := (String.length s') in
        if Z.ltb (digitToZ(String.sub(s,j))) 5 then
        s' else 
        String.substring(
          toString(valOf(fromString s)+(1/fromInt(Z.pow 10%Z 6%Z))) l, 0%Z, j)
      | Eq => s
      end
    | Some x =>
      match Z.compare numDec x with
      | Lt => 
        String.append s 
        (String.implode(List.tabulate(Z.sub x numDec,(fun i=>"0"%char))))
      | Gt =>
        let j  := Z.sub (String.size s)(numDec - x) in
        let s' := String.substring(s,0%Z,j) in
        let l  := (String.length s') in
        if Z.ltb (digitToZ(String.sub(s,j))) 5 then
        s' else 
        String.substring(
          toString(valOf(fromString s)+(1/fromInt(Z.pow 10%Z x))) l, 0%Z, j)
      | Eq => s 
      end
    end.

  (*
    Sml: StringCvt.radix -> real -> string
    Coq: StringCvt.radix -> float -> nat -> string

    - For now The user should give me how many digits, until we fix numdigits.

  *)
  Definition fmt (radix: StringCvt.realfmt) (f: float) (nd: nat): string:=
    match radix with
    | StringCvt.SCI arg => 
      match arg with
      | None   => fmtSCI arg f nd
      | Some i => if Z.ltb i 0 then SizeException else fmtSCI arg f nd
      end
    | StringCvt.FIX arg => 
      match arg with
      | None   => fmtFIX arg f nd
      | Some i => if Z.ltb i 0 then SizeException else fmtFIX arg f nd
      end
    | StringCvt.GEN arg =>
      match arg with
      | None   =>
        let FIX := (fmtFIX arg f nd) in
        let SCI := (fmtSCI arg f nd) in
        match Z.compare (String.size FIX) (String.size SCI) with
        | Lt => SCI
        | _  => FIX
        end
      | Some i => if Z.ltb i 1 then SizeException else
        let FIX := (fmtFIX arg f nd) in
        let SCI := (fmtSCI arg f nd) in
        match Z.compare (String.size FIX) (String.size SCI) with
        | Lt => SCI
        | _  => FIX
        end
      end
    | StringCvt.EXACT   => toString f nd
    end.

End Real.

(* These Functions could be called without the prefix "Real." *)
(* ---------------------------------------------------------------------------*)

(*
  Sml: int -> real
  Coq: Z -> float
*)
Definition fromInt (i:Z):float := Real.fromInt i.

(*
  Sml: real -> int
  Coq: float -> nat -> Z
  - For now The user should give me how many digits, until we fix numdigits,
    It's also so inefficient.
  - It should also raise an exception for infinity and nan but since Coq 
    doesn't support exceptions then it will return the axioms
    OverflowException, and DivException
*)
Definition trunc (r:float) (nd:nat):Z := Real.trunc r nd.

(*
  Sml: real -> int
  Coq: float -> nat -> Z
  - For now The user should give me how many digits, until we fix numdigits,
    It's also so inefficient.
  - It should also raise an exception for infinity and nan but since Coq 
    doesn't support exceptions then it will return the axioms
    OverflowException, and DivException
*)
Definition floor (r:float) (nd:nat):Z := Real.floor r nd.

(*
  Sml: real -> int
  Coq: float -> nat -> Z
  - For now The user should give me how many digits, until we fix numdigits,
    It's also so inefficient.
  - It should also raise an exception for infinity and nan but since Coq 
    doesn't support exceptions then it will return the axioms
    OverflowException, and DivException
*)
Definition ceil (r:float) (nd:nat):Z := Real.ceil r nd.

(*
  Sml: real -> int
  Coq: float -> nat -> Z
  - For now The user should give me how many digits, until we fix numdigits,
    It's also so inefficient.
  - It should also raise an exception for infinity and nan but since Coq 
    doesn't support exceptions then it will return the axioms
    OverflowException, and DivException
*)
Definition round (r:float) (nd:nat):Z := Real.round r nd.

(*----------------------------------------------------------------------------*)