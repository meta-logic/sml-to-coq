(* Mutually recursive datatypes and functions *)

datatype 'a evenList = ENil
                     | ECons of 'a * 'a oddList
and 'a oddList = OCons of 'a * 'a evenList

fun lengthE (ENil: 'a evenList): int = 0
  | lengthE (ECons (_, l)) = lengthO l
and lengthO (OCons (_, l)) = lengthE l

fun even [] = true
  | even (x :: l) = odd l
and odd [] = false
  | odd (x :: l) = even l

(* "Fake" mutual recursion *)
fun f x = (g x) + 10
and g x = x * 10
