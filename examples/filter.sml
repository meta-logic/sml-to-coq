
(* Nested pattern matching *)
fun filter [] _ = []
  | filter (x :: l) p = case (p x) 
    of true => x :: (filter l p)
     | false => filter l p
