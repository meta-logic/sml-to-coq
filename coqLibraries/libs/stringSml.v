Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope string_scope.

Module String.

  Axiom  SubscriptException : forall{a}, a.

  Axiom  SizeException : forall{a}, a.

  (*
    Sml: int
    Coq: Z
  *)
  Definition maxSize:Z :=  16777215%Z.

  (*
    Sml: string -> int
    Coq: string -> Z
  *)
  Definition size (s:string): Z := Z.of_nat(String.length s).

  (*
    Sml: string * int -> char
    Coq: string * Z -> ascii
    - It should raise an exception if n < 0 or n >= length l.,
      but since Coq doesn't have exceptions then it will return the axiom 
      SubscriptException
  *)
  Definition sub '((s, n):string * Z):ascii:=
    if (Z.ltb n 0) || (Z.leb (size s) n) then SubscriptException else
    match (String.get (Z.to_nat n) s) with
    | None => "0"%char
    | Some x => x
    end.

  (*
    Sml: string * int * int option -> string
    Coq: string * Z * option Z -> string
    - It should raise an exception if n < 0, n >= length l, m < 0,
      or length l < n+m, but since Coq doesn't have exceptions then
      it will return the axiom SubscriptException
  *)
  Definition extract '((s, n, no):string * Z * option Z):string:= 
    if (Z.ltb n 0) || (Z.ltb (size s) n) then SubscriptException else
    match no with
    |None   => String.substring (Z.to_nat n) ((String.length s)-(Z.to_nat n)) s
    |Some m =>
     if (Z.ltb m 0) || (Z.ltb (size s) (m+n)) then SubscriptException else
     String.substring (Z.to_nat n) (Z.to_nat m) s end.

  (*
    Sml: string * int * int -> string
    Coq: string * Z * Z -> string
  *)
  Definition substring '((s, n, m):string * Z * Z):string :=  
    extract(s, n, Some m).
  (*
    Sml: string * string -> string
    Coq: string * string -> string
    - It should raise an exception if |s1|+|s2| > maxsize, but since Coq 
      doesn't have exceptions then it will return the axiom SizeException
  *)
  Definition append (s1 s2:string):string := 
    if Z.ltb maxSize (size s1 + size s2) 
    then SizeException else String.append s1 s2.
  Notation "op^( x , y )" := (append x y) (at level 70, no associativity) : Z_scope.
  Infix "^" := append :string_scope.

  (*
    Sml: string -> string list -> string
    Coq: string -> list string -> string
    - It should raises an exception if the size of the resulting string
      would be greater than maxSize. , but since Coq doesn't have 
      exceptions then it will return the axiom SizeException
  *)
  Definition concatWith (s:string) (sl:list string): string :=
    let r := String.concat s sl in 
    if Z.ltb maxSize (size r) then SizeException else r .

  (*
    Sml: string list -> string
    Coq: list string -> string
    - It should raises an exception if the size of the resulting string
      would be greater than maxSize. , but since Coq doesn't have 
      exceptions then it will return the axiom SizeException
  *)
  Definition concat (sl:list string): string :=
    let r := String.concat "" sl in
    if Z.ltb maxSize (size r) then SizeException else r .

  (*
    Sml: char -> string
    Coq: ascii -> string
  *)
  Definition str (c:ascii): string := String c "".

  (*
    Sml: char list -> string
    Coq: list ascii -> string
    - It should raises an exception if the size of the resulting string
      would be greater than maxSize. , but since Coq doesn't have 
      exceptions then it will return the axiom SizeException
  *)
  Definition implode (l:list ascii): string :=  concat (List.map str l).

  (*
    Sml: string -> char list
    Coq: string -> list ascii
  *)
  Definition explode (s:string): list ascii:= (String.list_ascii_of_string s).

  (*
    Sml: (char -> char) -> string -> string
    Coq: (ascii -> ascii) -> string -> string
  *)
  Definition map (f:ascii->ascii) (s:string): string := 
    implode(List.map f (explode s)).

  (*
    Sml: (char -> string) -> string -> string
    Coq: (ascii -> string) -> string -> string
  *)
  Definition translate (f:ascii->string) (s:string): string := 
    concat(List.map f (explode s)).

  Fixpoint fields' (f:ascii->bool) (s:string) (i j:Z) (time:nat): list string := 
    match time with
    | 0       => (substring(s, i, (Z.sub j 1)))::[]
    | S time' => match (f (sub(s, j))) with
               | true  => (substring(s, i, (Z.sub j 1)))::(fields' f s (j+1) (j+10) time')
               | false => fields' f s i (j+1) time'
                end
    end.

  (*
    Sml: (char -> bool) -> string -> string list
    Coq: (ascii -> bool) -> string -> list string
  *)
  Definition fields (f:ascii->bool) (s:string): list string := 
    fields' f s 0 0 (Z.to_nat (size s)).

  (*
    Sml: (char -> bool) -> string -> string list
    Coq: (ascii -> bool) -> string -> list string
  *)
  Definition tokens (f:ascii->bool) (s:string): list string := 
     List.filter (fun s => Bool.eqb false (s =? "")) (fields f s).

  (*
    Sml: string -> string -> bool
    Coq: string -> string -> bool
  *)
  Definition isPrefix (s1 s2:string): bool := String.prefix s1 s2.

  (*
    Sml: string -> string -> bool
    Coq: string -> string -> bool
  *)
  Definition isSubstring  (s1 s2:string): bool := 
     match (String.index 0 s1 s2) with
     | Some x => true
     | None   => false
     end.
Compute isSubstring "ab" "abcd".
  (*
    Sml: string -> string -> bool
    Coq: string -> string -> bool
  *)
  Definition isSuffix (s1 s2:string): bool := 
    String.prefix (implode(List.rev (explode s1))) (implode(List.rev (explode s2))).

  Fixpoint collate' (f:ascii * ascii -> comparison) (l1 l2:list ascii): comparison:=
    match l1, l2 with
    | [],[] => Eq
    | [],_  => Lt
    | _ ,[] => Gt
    | x1::l1',x2::l2' => match f(x1,x2) with
                         | Eq     => collate' f l1' l2'
                         | other  => other
                         end
   end.

  (*
    Sml: (char * char -> order) -> string * string -> order
    Coq: (ascii * ascii -> comparison) -> string * string -> comparison
  *)
  Definition collate (f:ascii * ascii -> comparison)
             '((s1, s2):string * string): comparison := 
              collate' f (explode s1) (explode s2).

  (* 
    Sml: char -> int
    Coq: ascii -> Z
  *)
  Definition ord (c:ascii):Z := Z.of_nat(Ascii.nat_of_ascii(c)).

  (* 
    Sml: char * char -> order
    Coq: ascii * ascii -> comparison
  *)
  Definition compareChar '((c, d):ascii * ascii):comparison := 
    Z.compare (ord c) (ord d).

  (*
    Sml: string * string -> order
    Coq: string * string -> comparison
  *)
  Definition compare '((s1, s2):string * string):comparison :=
    collate compareChar (s1, s2).

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition opeq s1 s2:bool := Z.eqb (size s1) (size s2). 
  Notation "op=( x , y )" := (opeq x y) (at level 70) : nat_scope.
  Infix "=" := opeq (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition oplt s1 s2:bool := Z.ltb (size s1) (size s2). 
  Notation "op<( x , y )" := (oplt x y) (at level 70) : nat_scope.
  Infix "<" := oplt (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition ople s1 s2:bool := Z.leb (size s1) (size s2). 
  Notation "op<=( x , y )" := (ople x y) (at level 70) : nat_scope.
  Infix "<=" := ople (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition opgt s1 s2:bool := Z.ltb (size s2) (size s1). 
  Notation "op>( x , y )" := (opgt x y) (at level 70) : nat_scope.
  Infix ">" := opgt (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition opge s1 s2:bool := Z.leb (size s2) (size s1). 
  Notation "op>=( x , y )" := (opge x y) (at level 70) : nat_scope.
  Infix ">=" := opge (at level 70) : string_scope.

  (* SML spacific *)

  (*
    Sml: string -> String.string
    Coq: string -> string
  *)
  Definition toString (s:string):string           := s.

  (*
    Sml: String.string -> string option
    Coq: string -> option string
  *)
  Definition fromString (s:string):option string  := Some s.

  (*
    Sml: string -> String.string
    Coq: string -> string
  *)
  Definition toCString  (s:string):string         := s.

  (*
    Sml: String.string -> string option
    Coq: string -> soption tring
  *)
  Definition fromCString (s:string):option string := Some s. 
  (* Definition scan := . *) 

End String.

(* These Functions could be called without the prefix "String." *)
(* ---------------------------------------------------------------------------*)

(*
  Sml: string -> int
  Coq: string -> Z
*)
Definition size (s:string): Z := String.size s.

(*
  Sml: char -> string
  Coq: ascii -> string
*)
Definition str (c:ascii): string := String.str c.

(*
  Sml: string list -> string
  Coq: list string -> string
  - It should raises an exception if the size of the resulting string
    would be greater than maxSize. , but since Coq doesn't have 
    exceptions then it will return the axiom SizeException
*)
Definition concat (sl:list string): string := String.concat sl.

(*
  Sml: char list -> string
  Coq: list ascii -> string
  - It should raises an exception if the size of the resulting string
    would be greater than maxSize. , but since Coq doesn't have 
    exceptions then it will return the axiom SizeException
*)
Definition implode (l:list ascii): string :=  String.implode l.

(*
  Sml: string -> char list
  Coq: string -> list ascii
*)
Definition explode (s:string): list ascii:= String.explode s.
  
(*
  Sml: string * int * int -> string
  Coq: string * Z * Z -> string
*)
Definition substring '((s, n, m):string * Z * Z):string := 
    String.substring(s, n, m).

(*----------------------------------------------------------------------------*)
