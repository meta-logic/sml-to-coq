val a = String.maxSize;

val b = String.size("abcd");

val c = String.size "";

val d = String.sub("abcdefg",5);

val e = String.sub("sdfs", 4);

val f = String.sub("sdf", 0);

val g = String.sub("sdf", ~1);

val h = String.sub("sdf", 4);

val i = String.extract("abcdef", 0 , SOME 3);

val j = String.extract("abcdef", ~1 , SOME 3);

val k = String.extract("abcdef", 0 , NONE);

val l = String.substring("abcdef", 0 , 3);

val m = String.substring("abcdef", 0 , 6);

val n = String.substring("abcdef", 0 , 7);

(*val p = "abcd" ^ "efg";*)

(*val q  = "" ^ "";*)

val r = String.concat ["a", "b", "c"];

val s = String.concat ["a"];

val t = String.concat [];

val u = String.concatWith "/" ["a", "b", "c"];

val v = String.concatWith "" ["a", "b", "c"];

val w = String.concatWith "/" ["a"];

val x = String.concatWith "/" [];

val y = String.str #"a";

val z = String.str #"\128";

val a' = String.str #"\r";

val b' = String.implode [#"A", #" ", #"\r", #"b"];

val c' = String.explode "ab cd efg hij";

(* Function expressions not yet implemented! *)
(* map, translate, tokens, fields, compare *)

val d' = String.isPrefix "ab" "abcd";

val e' = String.isPrefix "" "abcd";

val f' = String.isPrefix "ab" "a";

val g' = String.isPrefix "ab" "ab";

val h' = String.isSubstring "ab" "abcd"; (* w *)

val i' = String.isSubstring "" "abcd";

val j' = String.isSubstring "ab" "dsfsdfab"; (* w *)

val k' = String.isSubstring "ab" "asdaabbasdabd"; (* w *)

val l' = String.isSuffix "ab" "abcd";

val m' = String.isSuffix "" "abcd";

val n' = String.isSuffix "ab" "dsfsdfab";

val p' = String.isSuffix "ab" "asdaabbasdabd";

val r' = String.compare("abcd", "abcd");

val s' = String.compare("abdc", "abcd");

val t' = String.compare("abc", "abcd");

val u' = String.compare("", "abcd");

val v' = String.compare("", "");
