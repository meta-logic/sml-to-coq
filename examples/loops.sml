(* Non terminating functions *)

fun loop1 x = loop1 (x+1) (* loops on ints and nats *)
fun loop2 x = loop2 (x-1) (* loops on ints, terminates on nats *)
fun loop3 [x::l] = loop3 (l @ [x])

