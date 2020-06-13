Require Import String.
Require Import Ascii.
Open Scope char_scope. 
Require Import List.
 


Module Char.

  Definition minChar:ascii := "000"%char.

  Definition maxChar:ascii := "255"%char.

  Definition maxOrd:nat     := 255.

  Definition ord (c:ascii):nat := Ascii.nat_of_ascii(c).

  Definition chr (n:nat):ascii := Ascii.ascii_of_nat(n).

  Definition succ (c:ascii):ascii := chr(ord c + 1).

  Definition pred (c:ascii):ascii := chr(ord c - 1).

  Definition compare '((c, d):ascii * ascii):comparison := 
    Nat.compare (ord c) (ord d).

  Definition opeq s1 s2:bool := Nat.eqb (ord s1) (ord s2). 
  Notation "op=( x , y )" := (opeq x y) (at level 70) : nat_scope.
  Infix "=" := opeq  : char_scope.

  Definition oplt s1 s2:bool := Nat.ltb (ord s1) (ord s2). 
  Notation "op<( x , y )" := (oplt x y) (at level 70) : nat_scope.
  Infix "<" := oplt (at level 70) : char_scope.

  Definition ople s1 s2:bool := Nat.leb (ord s1) (ord s2). 
  Notation "op<=( x , y )" := (ople x y) (at level 70) : nat_scope.
  Infix "<=" := ople (at level 70) : char_scope.

  Definition opgt s1 s2:bool := Nat.ltb (ord s2) (ord s1). 
  Notation "op>( x , y )" := (opgt x y) (at level 70) : nat_scope.
  Infix ">" := opgt (at level 70) : char_scope.

  Definition opge s1 s2:bool := Nat.leb (ord s2) (ord s1). 
  Notation "op>=( x , y )" := (opge x y) (at level 70) : nat_scope.
  Infix ">=" := opge (at level 70) : char_scope.

  Definition contains (s:string) (c:ascii):bool :=
    Nat.ltb 0 (List.length(List.filter (fun x=> x =? c)
              (String.list_ascii_of_string(s)))).

  Definition notContains (s:string) (c:ascii):bool := 
    match contains s c with
    | true  => false
    | false => true
    end.

  Definition isAscii (c:ascii):bool := 
    match (Nat.leb 0 (ord c)), (Nat.leb (ord c) 127) with
    | true, true => true
    | _   , _    => false
    end.

  Definition isUpper (c:ascii):bool := 
    match ("A" <=? c), (c <=? "Z") with
    | true, true => true
    | _   , _    => false
    end.

  Definition isLower (c:ascii):bool := 
    match ("a" <=? c), (c <=? "z") with
    | true, true => true
    | _   , _    => false
    end.

  Definition isDigit (c:ascii):bool := 
    match ("0" <=? c), (c <=? "9") with
    | true, true => true
    | _   , _    => false
    end.

  Definition isAlpha (c:ascii):bool := 
    match (isUpper c), (isLower c) with
    | false, false => false
    | _    , _     => true
    end.

  Definition isAlphaNum (c:ascii):bool := 
    match (isAlpha c), (isDigit c) with
    | false, false => false
    | _    , _     => true
    end.

  Definition isHexDigit (c:ascii):bool := 
    match (isDigit c), ("a" <=? c), (c <=? "f"), 
    ("A" <=? c), (c <=? "F") with
    | false, false, _, false, _ => false
    | flase, _, false, _, false => false
    | false, _, false, false, _ => false
    | flase, false, _, _, false => false
    | _, _, _, _, _ => true
    end.

  Definition isGraph (c:ascii):bool := 
    match ("!" <=? c), (c <=? "~") with
    | true, true => true
    | _   , _    => false
    end.

  Definition isPrint (c:ascii):bool := 
    match (isGraph c), (c =? " ") with
    | false, false => false
    | _    , _     => true
    end.

  Definition isPunct (c:ascii):bool := 
    match (isGraph c), (isAlphaNum c) with
    | true, false => true
    | _   , _     => false
    end.

  Definition isCntrl (c:ascii):bool := 
    match (isPrint c) with
    | false => true
    | true  => false
    end.

  Definition isSpace (c:ascii):bool := 
    match  ("009"%char <=? c),(c <=? "013"%char),(c =? " "%char) with
    | false, _, false => false
    | _, false, false => false
    | _, _, _  => true
    end.

  Definition toLower (c:ascii):ascii :=
    match isUpper c with
    | true  => chr(ord c + 32)
    | false => c
    end.

  Definition toUpper (c:ascii):ascii :=
    match isLower c with
    | true  => chr(ord c - 32)
    | false => c
    end.

  Definition toString (c:ascii):string := String c "".

  Import ListNotations.
  (* Partially correct *)
  Definition fromString (s:string):option ascii := 
    match (String.length s) with
    | 1 => (let c := String.list_ascii_of_string(s) in match c with
                                                     | [] => None
                                                     | c::l => Some c
                                                      end)
    | _ => None
    end.

  (* Sml Spacific 

    scan
    toCString
 *)

End Char.