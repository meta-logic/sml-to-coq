val a = Option.getOpt(SOME 1, 0);

val b = Option.getOpt(NONE, 0);

val c = getOpt(NONE, 0);

val d = Option.isSome(SOME 2);

val e = Option.isSome(NONE);

val f = isSome(SOME 2) andalso e;

val g = Option.valOf(SOME 1);

val h = Option.valOf(NONE);

val i = valOf(SOME 7);

val l = Option.join(SOME(SOME 5));

val m = Option.join(NONE);

(* Function expressions not yet implemented! *)
(* Tested directly in Coq for now *)
(*filter , app, map, mapPartial, compose, composePartial *)