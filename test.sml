(*val m = ~5
val x = "4";
val q = 4.2;
val y = (3,4,5);
val z = true andalso false;
val l = [1,2,3];
val b = #"b"
val k = if true andalso false then true else false*)
(*val i = 0xA5;
val r = 0w541;
val rx = 0wx541;*)

(*val e = {first = "John", last = "Doe", age = 150, balance = 0.12}*)

(*val y = 2;*)

(*val (x,y) = (3,4);*)

(*val a = case a of
    _ => b5;
*)
  
(*datatype tree = Empty 
              | Node of tree * string * tree;*)


(*fun negb (b:bool): bool =
  case b of
    true => false
  | false => true;*)

(*val a:string = "halawallah";*)
(*val t : bool = true;*)
(*val l = [];*)


(*val x::f = [1,2,3];*)
(*val (t,e)  = (true,false) ;*)

(*
val a = let
    val (t,e) = (true,false)
  in
    t andalso false
  end;
*)

(*------------------------------------------------------------*)

(*val x = 5;*)

(*val (h :: t) = [6,2,4]; Record patterns not yet implemented! *)


(*
Recursive value bindings are not yet implemented

fun f x = let val x = 6 in x end;
fun f x = let val (h :: t) = x in h end;

fun filter [] _ = []
  | filter (x :: l) p = case (p x) 
    of true => x :: (filter l p)
     | false => filter l p
          
fun id x = x;

fun loop1 x = loop1 (x+1)  loops on ints and nats 
fun loop2 x = loop2 (x-1)  loops on ints, terminates on nats 
fun loop3 [x::l] = loop3 (l @ [x])
*)

(*val y = [9];*)

(*
Recursive value bindings are not yet implemente
fun permutations l = case l 
  of [] => []
  | [x] => [x]
  | _ => List.foldl (fn (acc, x) => let
      val l_no_x = List.filter (fn e => e <> x) l
      val ps = permutations l_no_x
    in
      acc @ List.map (fn p => x :: p) ps
    end
    ) [] l

*)

(*datatype 'a evenList = ENil
                  | ECons of 'a * 'a oddList * 'a evenList;
and 'a oddList = OCons of 'a * 'a evenList * 'a oddList; *)