
(* Value declarations with/without pattern matching in multiple scopes *)

val x = 5;

val (h :: t) = [6,2,4];

fun f x = let val x = 6 in x end;

fun f x = let val (h :: t) = x in h end;
