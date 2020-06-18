Require Import Bool.
Require Import String.
Require Import Ascii.
Open Scope string_scope.

Module Bool.

  (* 
    Sml: bool -> bool 
    Coq: bool -> bool
  *)
  Definition not (b:bool):bool :=
    match b with
    | true  => false
    | false => true
    end.

  (* 
    Sml: bool -> string
    Coq: bool -> string
  *)
  Definition toString (b:bool):string :=
    match b with
    | true  => "true"
    | false => "false"
    end.

  (* SML Spacific *)
  (* Definition scan. *)

  (* 
    Sml: string -> bool option
    Coq: string -> option bool
  *)
  Definition fromString (s:string):option bool := 
    match s with
    | "true"  => Some true
    | "false" => Some false
    | _       => None
    end.

  (*
    Sml: (Char.char, 'a) StringCvt.reader -> (bool, 'a) StringCvt.reader
    Coq: ascii -> string -> option (bool * string) 
  *)
  Definition scan (c:ascii) (s:string):option (bool * string) :=
    match String.substring 0 4 s with
    | "true" => Some (true, String.substring 4 ((String.length s) - 4) s)
    |  _     => match String.substring 0 5 s with
                | "false" => Some (true, String.substring 5 ((String.length s)-5) s)
                | _       => None
                end
    end.

End Bool.