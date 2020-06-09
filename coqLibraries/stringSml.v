Require Import Bool.
Require Import String.
Require Import List.
Import ListNotations.
Open Scope string_scope.




Module String.

  Definition maxSize:nat :=  16777215.

  Definition size (s:string): nat:= String.length s.

  Definition sub '((s, n):string * nat):string:=  
    match (String.get n s) with
    | None => ""
    | Some x => String.string_of_list_ascii([x])
    end.

  Definition extract '((s, n, no):string * nat * option nat):string:= 
    match no with
    |None   => String.substring n ((String.length s) - n) s
    |Some m => String.substring n m s
    end.

  Definition substring '((s, n, m):string * nat * nat):string := 
    String.substring n m s.

  (* ^ is already defined*)
  Definition append '((s1, s2):string * string):string := String.append s1 s2.
  Infix "++" := append (right associativity, at level 60). 

  Definition concatWith (s:string) (sl:list string): string :=
    String.concat s sl.

  (**Char is not defined yet, it's just a single string*)
  Definition implode (sl:list string): string := String.concat "" sl.

  Definition concat (sl:list string): string := String.concat "" sl.

  (*Char is not defined yet, it's just a singlr string*)
  Definition str (c:string): string := c.

  (**Char is not defined yet, it's just a singlr string*)
  Definition explode (s:string): list string:= 
    List.map (fun x=>String.string_of_list_ascii([x])) (String.list_ascii_of_string s).

  Definition map (f:string->string) (s:string): string := 
    implode(List.map f (explode s)).

  Definition translate (f:string->string) (s:string): string := 
    concat(List.map f (explode s)).

  
  Fixpoint fields' (f:string->bool) (s:string) (i j time:nat): list string := 
    match time with
    | 0       => (substring(s, i, (j-1)))::[]
    | S time' => match (f (sub(s, j))) with
               | true  => (substring(s, i, j-i))::(fields' f s (j+1) (j+1) time')
               | false => fields' f s i (j+1) time'
                end
    end.

  Definition fields (f:string->bool) (s:string): list string := 
    fields' f s 0 0 (size s).

  Definition tokens (f:string->bool) (s:string): list string := 
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

  Fixpoint collate' (f:string * string -> comparison) (l1 l2:list string): comparison:=
    match l1, l2 with
    | [],[] => Eq
    | [],_  => Lt
    | _ ,[] => Gt
    | x1::l1',x2::l2' => match f(x1,x2) with
                         | Eq     => collate' f l1' l2'
                         | other  => other
                         end
   end.

  Definition collate (f:string * string -> comparison)
             '((s1, s2):string * string): comparison:= 
              collate' f (explode s1) (explode s2).

  (* the notations already exist !! *)
  (*  
  val op<  = op<  : string * string -> bool
  val op<= = op<= : string * string -> bool
  val op>  = op>  : string * string -> bool
  val op>= = op<= : string * string -> bool
  *)
  
  (* SML spacific *)
  Definition toString (s:string):string           := s.
  Definition fromString (s:string):option string  := Some s.
  Definition toCString  (s:string):string         := s.
  Definition fromCString (s:string):option string := Some s. 
  (* Definition scan := . *) 

End String.