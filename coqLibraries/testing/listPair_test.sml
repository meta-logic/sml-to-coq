val a = ListPair.zip([1,2,3], [4,5,6]);
val b = ListPair.zip([1,2,3], [4,5]);
val c = ListPair.zipEq([1,2,3], [4,5,6]);
val d = ListPair.zipEq([1,2,3], [4,5]);
val e = ListPair.unzip [(1,2), (3,4), (5,6)];
val f = ListPair.unzip ([]: (int * int) list);

(*app, appEq, map, mapEq, foldl, foldlEq, foldr, foldrEq, all, allEq, exists*)