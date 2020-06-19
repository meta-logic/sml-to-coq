(*Testing *)

(*Inductive*)

(*types names might be different int is Z in Coq*)
datatype tree = Empty 
              | Node of tree * int * tree; 

datatype 'a evenList = ENil
                  | ECons of 'a * 'a oddList * 'a evenList
and 'a oddList = OCons of 'a * 'a evenList * 'a oddList; 

(*Definition*)
val int:int = "sdasd";
(*val r = ("abcd" > "asdsd") andalso (5 > 3);*)
val t = #"\^U";
val x = op< (4,5);
val a = ~5
val b = "4";
val c = 4.2;
val d = (3,4,5);
val e = true andalso false;
val f = [1,2,3];
val g = #"b"
val h = if true andalso false then true else false
val i = 0xA5;
val (j,k) = (3,4);
val m = let
    val (n,p) = (true,false)
  in
    n andalso p andalso true andalso false
  end;
