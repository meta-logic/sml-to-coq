From boolSml Require Import boolSml.
From stringSml Require Import stringSml.
From intSml Require Import intSml.
From charSml Require Import charSml.
From listSml Require Import listSml.
From stringCvtSml Require Import stringCvtSml.

Module IEEEReal.

  Local Axiom UnorderedException: forall{a}, a.

  Inductive real_order :=
    | LESS
    | EQUAL
    | GREATER
    | UNORDERED.

  Inductive float_class := 
    | NAN
    | INF
    | ZERO
    | NORMAL
    | SUBNORMAL.

  Inductive rounding_mode := 
    | TO_NEAREST
    | TO_NEGINF
    | TO_POSINF
    | TO_ZERO.

  (*Not implemented yet (imperative behavior (side effects))
    Definition setRoundingMode : rounding_mode -> unit
    Definition getRoundingMode : unit -> rounding_mode
  *)

  Record decimal_approx := 
    {
      class : float_class;
      sign : bool;
      digits : list Z;
      exp : Z
    }.

  Definition toString1 (d: decimal_approx): string :=
    match d with
    | {|class := fc; sign := b; digits := lz; exp := z|} => 
      match fc with
      | ZERO => "0.0"
      | INF => "inf"
      | NAN => "nan"
      | _ => 
        match b with
        | true  => 
          match z with 
          | 0%Z => "-" ++ (List.foldr (fun '(a, b) => 
                   String.append (Int.toString1 a) b) (""%string) lz)
          | _   => "-" ++ (List.foldr (fun '(a, b) => 
                   String.append (Int.toString1 a) b) (""%string) lz)
                       ++ "E" ++ (Int.toString1 z)
          end
        | false => 
          match z with 
          | 0%Z => (List.foldr (fun '(a, b) => 
                   String.append (Int.toString1 a) b) (""%string) lz)
          | _   => (List.foldr (fun '(a, b) => 
                   String.append (Int.toString1 a) b) (""%string) lz)
                       ++ "E" ++ (Int.toString1 z)
          end
        end
      end
    end.

  (* scan : Not implemented yet*)

  Local Definition getSign (s: string) :=
    match s with
    | ""%string   => None
    | String c s' => match c with
                     | #"-" => Some(true, s')
                     | #"~" => Some(true, s')
                     | #"+" => Some(false, s')
                     | _ => Some(false, s)
                     end
    end.

  Local Definition digitToZ (c: ascii): option Z :=
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

  Local Fixpoint readD_exp (s: string) (exp: Z): option Z :=
    match s with
    | ""%string => Some exp
    | String c s' => match digitToZ c with
                     | Some n => readD_exp s' (10 * exp + n)
                     | None => None
                     end
    end.

  Local Fixpoint readD_dec (s: string) (fl: list Z): option(list Z * Z) :=
    match s with
    | ""%string => Some(fl, 0)
    | String c s' =>
      match c with
      | "e"%char  | "E"%char =>
        match getSign s' with
        | None           => None
        | Some(sign, s'') =>
          let n' := readD_exp s'' 0 in
          match n' with
          | Some exp => Some(fl,if sign then -exp else exp)
          | None => None
          end
        end
      | _ => 
        match digitToZ c with
        | Some n => readD_dec s' (n::fl)
        | None => None
        end
      end
    end.

  Local Fixpoint readD (s: string) (il: list Z): option (list Z * list Z * Z):=
  match s with
  | ""%string => Some(List.rev il, [], 0)
  | String c s' => 
    match c with
    | "."%char => 
      let n' := readD_dec s' [] in
      match n' with
      | Some(fl, exp) => Some(List.rev il, List.rev fl, exp)
      | None => None
      end
    | _ => 
      match digitToZ c with
      | Some n => readD s' (n::il)
      | None => None
      end
    end
  end.

 Local Fixpoint remZeros (l: list Z): list Z :=
   match l with
   | nil => nil
   | x::l' => if Z.eqb x 0 then remZeros l' else x::l'
   end.

  Definition fromString (s: string): option decimal_approx :=
    match getSign s with
    | None           => None
    | Some(sign, s') =>
      match s' with
      | ""%string  => None
      | "nan"      => Some {|class:=NAN; sign:=sign; digits:=[]; exp:=0|}
      | "inf"      => Some {|class:=NAN; sign:=sign; digits:=[]; exp:=0|}
      | "infinity" => Some {|class:=INF; sign:=sign; digits:=[]; exp:=0|}
      | _ => 
        match readD s' [] with
        | None              => None
        | Some(il, fl, exp) => 
          let '(il',fl') := (remZeros il, List.rev (remZeros (List.rev fl))) in
          Some (match (List.null il'), (List.null fl') with
          | true, true  => {|class:=ZERO; sign:=sign; digits:=[]; exp:=0|}
          | false, _    => {|class:=NORMAL; sign:=sign; digits:= il' ++ fl';
                             exp:=exp + (List.length il')|}
          | true, false => {|class:=NORMAL; sign:=sign; digits:=il' ++ fl';
                              exp:=exp - ((List.length fl)-(List.length (remZeros fl)))|}
          end)
        end
      end
    end.

End IEEEReal.