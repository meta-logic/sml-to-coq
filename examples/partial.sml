(* Partial functions *)

fun p_head (x::_) = x

fun hd_sum ((a,b)::l) ((a',b')::l') init = 
    init + a + b + a' + b'
  | hd_sum ((a,b)::l) l' init =
    init + a + b
  | hd_sum l ((a',b')::l') init = 
    init + a' + b'
;
