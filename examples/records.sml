(* Records *)
type r = { name : string, 
           age : int,
           height : real }

fun isBob ({name = "Bob", ...}: r) = true
  | isBob {...} = false
