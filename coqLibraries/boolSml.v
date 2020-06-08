Require Import Bool.
Require Import String.
Open Scope string_scope.

Module Bool.

  Definition not (b:bool):bool :=
    match b with
    | true  => false
    | false => true
    end.  

  Definition toString (b:bool):string :=
    match b with
    | true  => "true"
    | false => "false"
    end.

  (* SML Spacific *)
  (* Definition scan. *)

  Definition fromString (s:string):option bool := 
    match s with
    | "true"  => Some true
    | "false" => Some false
    | _       => None
    end.
    
End Bool.