val a = List.null ([]:int list);
val b = List.null [1];
val c = List.length ([]:int list);
val d = List.length [4,2,5,6,4,7];
val e = List.hd [4,2,5,6,4,7];
val f = List.hd ([]:int list);
val g = List.hd [1];
val h = List.tl [4,2,5,6,4,7];
val i = List.tl [4];
val j = List.tl ([]:int list);
val k = List.last [4,2,5,6,4,7];
val l = List.last [4];
val m = List.last ([]:int list);
val n = List.getItem ([]:int list);
val p = List.getItem [1];
val q = List.getItem [1,2,3];
val r = List.nth([1,2,3],~1);
val s = List.nth([1,2,3],3);
val v = List.nth([1,2,3],1);
val u = List.nth([1,2,3],2);
val t = List.take([1,2,3],~1);
val w = List.take([1,2,3],4);
val x = List.take([1,2,3],3);
val y = List.take([1,2,3],2);
val z = List.drop([1,2,3],~1);
val a' = List.drop([1,2,3],4);
val b' = List.drop([1,2,3],3);
val c' = List.drop([1,2,3],2);
val d' = List.rev ([]:int list);
val e' = List.rev [1];
val f' = List.rev [1,2];
val g' = List.concat[([]:int list),([]:int list),([]:int list)];
val h' = List.concat[[1,2],[3],[4,5,6]];
val i' = List.concat([]:(int list) list);
val j' = List.revAppend([1,2,3],[4,5,6]);
(* app, map, mapPartial, find, filter, partition, 
  foldl, foldr, exists, all, tabulate, collate *)


