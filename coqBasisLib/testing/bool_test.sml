val a = true;

val b = not a;

val b' = Bool.not a;

val c = Bool.toString b;

val d = Bool.fromString "true";

val e = Bool.fromString "false";

val f = Bool.fromString "sdfsdf";

val g = Bool.fromString "";

val h = case d of
          SOME x => ( case e of
                        SOME y => x andalso y
                      | NONE => x orelse false )
        | NONE   => ( case e of
                        SOME y => y orelse true
                      | NONE => false );

val i = Bool.scan " " "true";

val j = Bool.scan " " "false";

val k = Bool.scan " " "sdfs";