Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Open Scope string_scope.

Module String.

  (*
    Sml: int
    Coq: nat
  *)
  Definition maxSize:nat :=  16777215.

  (*
    Sml: string -> int
    Coq: string -> nat
  *)
  Definition size (s:string): nat:= String.length s.

  (*
    Sml: string * int -> char
    Coq: string * nat -> ascii
  *)
  Definition sub '((s, n):string * nat):ascii:=  
    match (String.get n s) with
    | None => "0"%char
    | Some x => x
    end.

  (*
    Sml: string * int * int option -> string
    Coq: string * nat * option nat -> string
  *)
  Definition extract '((s, n, no):string * nat * option nat):string:= 
    match no with
    |None   => String.substring n ((String.length s) - n) s
    |Some m => String.substring n m s
    end.

  (*
    Sml: string * int * int -> string
    Coq: string * nat * nat -> string
  *)
  Definition substring '((s, n, m):string * nat * nat):string := 
    String.substring n m s.

  (*
    Sml: string * string -> string
    Coq: string * string -> string
  *)
  Definition append (s1 s2:string):string := String.append s1 s2.
  Notation "op^( x , y )" := (append x y) (at level 70, no associativity) : Z_scope.
  Infix "^" := append :string_scope.

  (*
    Sml: string -> string list -> string
    Coq: string -> list string -> string
  *)
  Definition concatWith (s:string) (sl:list string): string :=
    String.concat s sl.

  (*
    Sml: string list -> string
    Coq: list string -> string
  *)
  Definition concat (sl:list string): string := String.concat "" sl.

  (*
    Sml: char -> string
    Coq: ascii -> string
  *)
  Definition str (c:ascii): string := String c "".

  (*
    Sml: char list -> string
    Coq: list ascii -> string
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

  
  Fixpoint fields' (f:ascii->bool) (s:string) (i j time:nat): list string := 
    match time with
    | 0       => (substring(s, i, (j-1)))::[]
    | S time' => match (f (sub(s, j))) with
               | true  => (substring(s, i, j-i))::(fields' f s (j+1) (j+1) time')
               | false => fields' f s i (j+1) time'
                end
    end.

  (*
    Sml: (char -> bool) -> string -> string list
    Coq: (ascii -> bool) -> string -> list string
  *)
  Definition fields (f:ascii->bool) (s:string): list string := 
    fields' f s 0 0 (size s).

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

  (*
    Sml: string -> string -> bool
    Coq: string -> string -> bool
  *)
  Definition isSuffix (s1 s2:string): bool := 
    String.prefix (implode(List.rev (explode s1))) (implode(List.rev (explode s2))).

  (*
    Sml: string * string -> order
    Coq: string * string -> comparison
  *)
  Definition compare '((s1, s2):string * string):comparison :=
    Nat.compare (size s1) (size s2).

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
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition opeq s1 s2:bool := Nat.eqb (size s1) (size s2). 
  Notation "op=( x , y )" := (opeq x y) (at level 70) : nat_scope.
  Infix "=" := opeq (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition oplt s1 s2:bool := Nat.ltb (size s1) (size s2). 
  Notation "op<( x , y )" := (oplt x y) (at level 70) : nat_scope.
  Infix "<" := oplt (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition ople s1 s2:bool := Nat.leb (size s1) (size s2). 
  Notation "op<=( x , y )" := (ople x y) (at level 70) : nat_scope.
  Infix "<=" := ople (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition opgt s1 s2:bool := Nat.ltb (size s2) (size s1). 
  Notation "op>( x , y )" := (opgt x y) (at level 70) : nat_scope.
  Infix ">" := opgt (at level 70) : string_scope.

  (*
    Sml: string * string -> bool
    Coq: string * string -> bool
  *)
  Definition opge s1 s2:bool := Nat.leb (size s2) (size s1). 
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