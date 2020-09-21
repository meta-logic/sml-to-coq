(* Value declarations with/without pattern matching in multiple scopes *)

val z = 5

val L = [8]

val x :: l = [1,2,3]

val (a, b) = (5.5, 3.2)

fun six x = let val x = 6 in x end

fun head x = let val (h :: t) = x in h end
