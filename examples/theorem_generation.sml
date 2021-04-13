(*Basic/simple uncurried example*)
(!! 
  posAdd(x, y) ==> b;
  REQUIRES: x > 0 andalso y > 0;
  ENSURES: b > x andalso b > y; 
!!)
fun posAdd(x, y) = x + y;


(* Typed curried basic example [explicit types] *)
(!! 
  negAdd (x: int) (y: int) ==> (b:int);
  REQUIRES: x < 0 andalso y < 0;
  ENSURES: b < x andalso b < y; 
!!)
fun negAdd x y = x + y;

(* Generic types in *)
(* To do *)


(* Referencing other functions in contracts *)
fun trueLen ([]: int list) =0
  | trueLen (a::l) = 1 + trueLen l

(!!
    len (l: int list) ==> (result: int);
    REQUIRES: (List.length l) >= 0;
    ENSURES: result = (trueLen l);
!!)
fun len [] = 0
  | len (x::l') = 1 + len l';