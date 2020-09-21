(* Non terminating functions *)

fun loop1 x = loop1 (x+1) (* loops on ints and nats *)
fun loop2 x = loop2 (x-1) (* loops on ints, terminates on nats *)
fun loop3 [x::l] = loop3 (l @ [x])

(* fact and collatz not terminate for negative numbers *)
fun fact 0 = 1
  | fact n = n * fact (n-1)

(* Non top level match expression *)
fun collatz 1 = [1]
  | collatz n = n :: (case n mod 2 of
      0 => collatz (n div 2)
    | _ => collatz (3*n + 1) )
;
