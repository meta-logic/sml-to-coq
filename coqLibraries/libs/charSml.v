Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import ZArith.

Module Char.

  Open Scope char_scope.

  (* 
    Sml: char
    Coq: ascii
  *)
  Definition minChar:ascii := "000"%char.

  (* 
    Sml: char
    Coq: ascii
  *)
  Definition maxChar:ascii := "255"%char.

  (* 
    Sml: char
    Coq: ascii
  *)
  Definition maxOrd:Z     := 255%Z.

  (* 
    Sml: char -> int
    Coq: ascii -> Z
  *)
  Definition ord (c:ascii):Z := Z.of_nat(Ascii.nat_of_ascii(c)).

  (* 
    Sml: int -> char
    Coq: nat -> ascii
  *)
  Definition chr (n:Z):ascii := Ascii.ascii_of_nat(Z.to_nat(n)).

  (* 
    Sml: char -> char
    Coq: ascii -> ascii
  *)
  Definition succ (c:ascii):ascii := chr(ord c + 1).

  (* 
    Sml: char -> char
    Coq: ascii -> ascii
  *)
  Definition pred (c:ascii):ascii := chr(ord c - 1).

  (* 
    Sml: char * char -> order
    Coq: ascii * ascii -> comparison
  *)
  Definition compare '((c, d):ascii * ascii):comparison := 
    Z.compare (ord c) (ord d).

  (* 
    Sml: char * char -> bool
    Coq: ascii * ascii -> bool
  *)
  Definition opeq s1 s2:bool := Z.eqb (ord s1) (ord s2). 
  Notation "op=( x , y )" := (opeq x y) (at level 70) : nat_scope.
  Infix "=" := opeq  : char_scope.

  (* 
    Sml: char * char -> bool
    Coq: ascii * ascii -> bool
  *)
  Definition oplt s1 s2:bool := Z.ltb (ord s1) (ord s2). 
  Notation "op<( x , y )" := (oplt x y) (at level 70) : nat_scope.
  Infix "<" := oplt (at level 70) : char_scope.

  (* 
    Sml: char * char -> bool
    Coq: ascii * ascii -> bool
  *)
  Definition ople s1 s2:bool := Z.leb (ord s1) (ord s2). 
  Notation "op<=( x , y )" := (ople x y) (at level 70) : nat_scope.
  Infix "<=" := ople (at level 70) : char_scope.

  (* 
    Sml: char * char -> bool
    Coq: ascii * ascii -> bool
  *)
  Definition opgt s1 s2:bool := Z.ltb (ord s2) (ord s1). 
  Notation "op>( x , y )" := (opgt x y) (at level 70) : nat_scope.
  Infix ">" := opgt (at level 70) : char_scope.

  (* 
    Sml: char * char -> bool
    Coq: ascii * ascii -> bool
  *)
  Definition opge s1 s2:bool := Z.leb (ord s2) (ord s1). 
  Notation "op>=( x , y )" := (opge x y) (at level 70) : nat_scope.
  Infix ">=" := opge (at level 70) : char_scope.

  (*
    Sml: string -> char -> bool
    Coq: string -> ascii -> bool
  *)
  Definition contains (s:string) (c:ascii):bool :=
    Nat.ltb 0 (List.length(List.filter (fun x=> x = c)
              (String.list_ascii_of_string(s)))).

  (*
    Sml: string -> char -> bool
    Coq: string -> ascii -> bool
  *)
  Definition notContains (s:string) (c:ascii):bool := 
    match contains s c with
    | true  => false
    | false => true
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isAscii (c:ascii):bool := 
    match (Z.leb 0 (ord c)), (Z.leb (ord c) 127) with
    | true, true => true
    | _   , _    => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isUpper (c:ascii):bool := 
    match ("A"%char <= c), (c <= "Z"%char) with
    | true, true => true
    | _   , _    => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isLower (c:ascii):bool := 
    match ("a"%char <= c), (c <= "z"%char) with
    | true, true => true
    | _   , _    => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isDigit (c:ascii):bool := 
    match ("0"%char <= c), (c <= "9"%char) with
    | true, true => true
    | _   , _    => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isAlpha (c:ascii):bool := 
    match (isUpper c), (isLower c) with
    | false, false => false
    | _    , _     => true
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isAlphaNum (c:ascii):bool := 
    match (isAlpha c), (isDigit c) with
    | false, false => false
    | _    , _     => true
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isHexDigit (c:ascii):bool := 
    match (isDigit c), ("a"%char <= c), (c <= "f"%char), 
    ("A"%char <= c), (c <= "F"%char) with
    | false, false, _, false, _ => false
    | flase, _, false, _, false => false
    | false, _, false, false, _ => false
    | flase, false, _, _, false => false
    | _, _, _, _, _ => true
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isGraph (c:ascii):bool := 
    match ("!"%char <= c), (c <= "~"%char) with
    | true, true => true
    | _   , _    => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isPrint (c:ascii):bool := 
    match (isGraph c), (c = " "%char) with
    | false, false => false
    | _    , _     => true
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isPunct (c:ascii):bool := 
    match (isGraph c), (isAlphaNum c) with
    | true, false => true
    | _   , _     => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isCntrl (c:ascii):bool := 
    match (isPrint c) with
    | false => true
    | true  => false
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition isSpace (c:ascii):bool := 
    match  ("009"%char <= c),(c <= "013"%char),(c = " "%char) with
    | false, _, false => false
    | _, false, false => false
    | _, _, _  => true
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition toLower (c:ascii):ascii :=
    match isUpper c with
    | true  => chr(ord c + 32)
    | false => c
    end.

  (* 
    Sml: char -> bool
    Coq: ascii -> bool
  *)
  Definition toUpper (c:ascii):ascii :=
    match isLower c with
    | true  => chr(ord c - 32)
    | false => c
    end.

  Definition toControl (c:ascii):string := 
    "\\^" ++ String (chr(ord c + ord "@"%char)) "".

  Definition toAscii (c:ascii):string := 
    "\\" ++ (String (chr(Z.div (ord c) 100 + ord "0"%char)) "")
         ++ (String (chr(Z.div (Z.modulo (ord c) 100) 10 + ord "0"%char)) "")
         ++ (String (chr(Z.modulo (ord c) 10 + ord "0"%char)) "").

  Definition toOctAscii (c:ascii):string := 
    "\\" ++ (String (chr(Z.div (ord c) 64 + ord "0"%char)) "")
         ++ (String (chr(Z.div (Z.modulo (ord c) 64) 8 + ord "0"%char)) "")
         ++ (String (chr(Z.modulo (ord c) 8 + ord "0"%char)) "").

  (* 
    Sml: char -> string
    Coq: ascii -> string
  *)
  Definition toString (c:ascii):string := 
    match c with 
    | "092"%char => "\\\\"
    | "034"%char => """"
    | "007"%char => "\\a"
    | "008"%char => "\\b"
    | "009"%char => "\\t"
    | "010"%char => "\\n"
    | "011"%char => "\\v"
    | "012"%char => "\\f"
    | "013"%char => "\\r"
    | c     => if Z.ltb (ord c) 32 then toControl c 
               else if Z.ltb 126 (ord c) then toAscii c 
               else String c "" 
    end.

  (* 
    Sml: char -> String.string
    Coq: ascii -> string
  *)
  Definition toCString (c:ascii):string := 
    match c with 
    | "092"%char => "\\\\"
    | "034"%char => """"
    | "063"%char => "\\?"
    | "039"%char => "\\'"
    | "007"%char => "\\a"
    | "008"%char => "\\b"
    | "009"%char => "\\t"
    | "010"%char => "\\n"
    | "011"%char => "\\v"
    | "012"%char => "\\f"
    | "013"%char => "\\r"
    | c     => if isPrint c then String c "" else toOctAscii c
    end.

  Definition value c := 
    Z.to_nat(ord(toUpper c)) - 
    (if c < "A"%char then Z.to_nat(ord "0"%char) else Z.to_nat(ord "A"%char) - 10).

  Import ListNotations.

  Definition scanAscii (cl:list ascii):option (ascii * string) :=
    match cl with
    | [] => None 
    | c1::[] => None
    | c1::c2::[] => None
    | c1::c2::c3::cl' => 
      if (isDigit(c1)&&isDigit(c2)&&isDigit(c3)) then
      ( let i := 100*value c1 + 10*value c2 + value c3 in 
        if Nat.leb i 255 then Some(chr (Z.of_nat i),String.string_of_list_ascii(cl'))
        else None ) else None
    end.

  Definition scanUnicode (cl:list ascii):option (ascii * string) :=
    match cl with
    | [] => None 
    | c1::[] => None
    | c1::c2::[] => None
    | c1::c2::c3::[] => None
    | c1::c2::c3::c4::cl' => 
      if (isHexDigit(c1)&&isHexDigit(c2)&&isHexDigit(c3)&&isHexDigit(c4)) then
      ( let i := 4096*value c1 + 256*value c2 + 16*value c3 + value c4 in 
        if Nat.leb i 255 then Some(chr (Z.of_nat i),String.string_of_list_ascii(cl'))
        else None ) else None
    end.

  Definition scanControl (cl:list ascii):option (ascii * string) :=
    match cl with
    | [] => None
    | c::cl' => 
      if (Z.leb 64 (ord c)) && (Z.leb (ord c) 96) 
      then Some(chr(ord c - 64),String.string_of_list_ascii(cl') ) else
      None
    end.


  Definition scanEscape (cl:list ascii):option (ascii * string) :=
    match cl with
    | [] => None 
    | c::l => if isDigit c then scanAscii cl else 
              if isSpace c then None else
              match c with
              | "a"%char   => Some("007"%char, String.string_of_list_ascii(l))
              | "b"%char   => Some("008"%char, String.string_of_list_ascii(l))
              | "t"%char   => Some("009"%char, String.string_of_list_ascii(l))
              | "n"%char   => Some("010"%char, String.string_of_list_ascii(l))
              | "v"%char   => Some("011"%char, String.string_of_list_ascii(l))
              | "f"%char   => Some("012"%char, String.string_of_list_ascii(l))
              | "r"%char   => Some("013"%char, String.string_of_list_ascii(l))
              | "092"%char => Some("092"%char, String.string_of_list_ascii(l))
              | """"%char  => Some("034"%char, String.string_of_list_ascii(l))
              | "^"%char   => scanControl cl
              | "u"%char   => scanUnicode cl
              | _     => None
              end
    end.

  Definition scan' (cl:list ascii):option (ascii * string) :=
    match cl with
    | [] => None
    | c::[] => Some(c,""%string)
    | c1::c2::cl' => match (c1 = "\"%char) && (c2 = "\"%char) with
                     | true => scanEscape cl'
                     | flase => if isPrint c1 
                     then Some(c1,String.string_of_list_ascii(c2::cl')) 
                     else None
                     end
    end.

  (*
    Sml: (Char.char, 'a) StringCvt.reader -> (char, 'a) StringCvt.reader
    Coq: ascii -> string -> option (ascii * string) 
  *)
  Definition scan (c:ascii) (s:string):option (ascii * string) :=
    let cl := String.list_ascii_of_string(s) in scan' cl.

  (* 
    Sml: String.string -> char option
    Coq: string -> option ascii  
  *)

  Definition fromString (s:string):option ascii := 
    let c := scan " " s in
    match c with 
    | None => None
    | Some (x, str) => Some x 
    end.

End Char.

(* These Functions could be called without the prefix "Char." *)
(* ---------------------------------------------------------------------------*)

(* 
  Sml: char -> int
  Coq: ascii -> Z
*)
Definition ord (c:ascii):Z := Char.ord c.

(* 
  Sml: int -> char
  Coq: nat -> ascii
*)
Definition chr (n:Z):ascii := Char.chr n.

(* ---------------------------------------------------------------------------*)