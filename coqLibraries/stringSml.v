Require Import Bool.
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Open Scope string_scope.


Module String.

  Definition maxSize:nat :=  16777215.

  Definition size (s:string): nat:= String.length s.

  Definition sub '((s, n):string * nat):ascii:=  
    match (String.get n s) with
    | None => "0"%char
    | Some x => x
    end.

  Definition extract '((s, n, no):string * nat * option nat):string:= 
    match no with
    |None   => String.substring n ((String.length s) - n) s
    |Some m => String.substring n m s
    end.

  Definition substring '((s, n, m):string * nat * nat):string := 
    String.substring n m s.

  (*
     ^ : ++ 
  *)
  Definition append '((s1, s2):string * string):string := String.append s1 s2.
  Infix "++" := append (right associativity, at level 60). 

  Definition concatWith (s:string) (sl:list string): string :=
    String.concat s sl.

  Definition concat (sl:list string): string := String.concat "" sl.

  Definition str (c:ascii): string := String c "".

  Definition implode (l:list ascii): string :=  concat (List.map str l).

  Definition explode (s:string): list ascii:= (String.list_ascii_of_string s).

  Definition map (f:ascii->ascii) (s:string): string := 
    implode(List.map f (explode s)).

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

  Definition fields (f:ascii->bool) (s:string): list string := 
    fields' f s 0 0 (size s).

  Definition tokens (f:ascii->bool) (s:string): list string := 
     List.filter (fun s => Bool.eqb false (s =? "")) (fields f s).

  Definition isPrefix (s1 s2:string): bool := String.prefix s1 s2.

  Definition isSubstring  (s1 s2:string): bool := 
     match (String.index 0 s1 s2) with
     | Some x => true
     | None   => false
     end.

  Definition isSuffix (s1 s2:string): bool := 
    String.prefix (implode(List.rev (explode s1))) (implode(List.rev (explode s2))).

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

  Definition collate (f:ascii * ascii -> comparison)
             '((s1, s2):string * string): comparison := 
              collate' f (explode s1) (explode s2).

  (*  
      =   : =?
      <   : <?
      <=  : <=?
      >   : >?
      >=  : >=?
  *)

  Definition opeq s1 s2:bool := Nat.eqb (size s1) (size s2). 
  Notation "op=( x , y )" := (opeq x y) (at level 70) : nat_scope.
  Infix "=?" := opeq (at level 70) : nat_scope.

  Definition oplt s1 s2:bool := Nat.ltb (size s1) (size s2). 
  Notation "op<( x , y )" := (oplt x y) (at level 70) : nat_scope.
  Infix "<?" := oplt (at level 70) : nat_scope.

  Definition ople s1 s2:bool := Nat.leb (size s1) (size s2). 
  Notation "op<=( x , y )" := (ople x y) (at level 70) : nat_scope.
  Infix "<=?" := ople (at level 70) : nat_scope.

  Definition opgt s1 s2:bool := Nat.ltb (size s2) (size s1). 
  Notation "op>( x , y )" := (opgt x y) (at level 70) : nat_scope.
  Infix ">?" := opgt (at level 70) : nat_scope.

  Definition opge s1 s2:bool := Nat.leb (size s2) (size s1). 
  Notation "op>=( x , y )" := (opge x y) (at level 70) : nat_scope.
  Infix ">=?" := opge (at level 70) : nat_scope.

  (* SML spacific *)
  Definition toString (s:string):string           := s.
  Definition fromString (s:string):option string  := Some s.
  Definition toCString  (s:string):string         := s.
  Definition fromCString (s:string):option string := Some s. 
  (* Definition scan := . *) 

End String.