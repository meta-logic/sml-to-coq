(* Example to show generated induction
    principle  *)

datatype ('a, 'b) tree = Leaf1 of 'a
                    | Leaf2 of 'b
                    | Node of ('a, 'b) tree * 'a * 'b * ('a, 'b) tree


fun treeSum (Leaf1 x) = x
    | treeSum (Leaf2 x) = x
    | treeSum (Node (t1,a,b,t2)) = treeSum t1 + a + b + treeSum t2 


fun treeSumCont' k (Leaf1 x) =  k x
    |   treeSumCont' k (Leaf2 x) = k x
    |   treeSumCont' k (Node(t1,a,b,t2)) = treeSumCont' (fn x => treeSumCont' (fn y => k (x + a + b + y)) t2) t1

fun treeSumCont t = treeSumCont' (fn x => x) t;
