Require Import Bool.
Require Import String.
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

End Bool.