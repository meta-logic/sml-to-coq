(* THIS FILE HAD NO COMMENTS WHEN PASSED TO THE PARSE FUNCTION *)

(* This is the only line that was in the file when passed 
    to the parse function *)
val a = 5;

(* These are the sequence of commands that produced the AST *)
(*

CM.make "core.cm";

val f = TextIO.openIn ("Parse/test.sml");

val source = 
Source.newSource ("stdIn", f, true, ErrorMsg.defaultConsumer());

structure SmlFile = SmlFile;

val ast' = SmlFile.parse source;

//Or alternatively (probably the parses up to the first semicolon only)
val SOME ast' = SmlFile.parseOne source ();

*)


(* This is the ast produced by SMLFile.parse 
  where almost every constructor here is defined in Parse/ast.sml *)

val ast' =
  SeqDec [ (* Sequence of declarations *)
    MarkDec ( (* Mark of a declaration: pair of declaration and region where it occurs *)
      ValDec ( 
        [
          MarkVb (  (* Mark of a variable binding: the binding and region where it occurs *)
            Vb { (* Variable binding *)
              exp=FlatAppExp [{fixity=NONE,item=MarkExp (IntExp ("5",5),(10,11)),region=(10,11)}],
              lazyp = false, (* Indicates that something is lazy??? *)
              pat = (* pattern *)
                MarkPat ( (* Mark of the pattern (region) *)
                  FlatAppPat [ (* "patterns prior to fixity parsing" -- fixity is infix,prefix,posfix and associativity info *) 
                    { fixity = SOME (SYMBOL (0wx339,"a")),
                      item = MarkPat (VarPat [SYMBOL (0wx331,"a")],(6,7)),
                      region = (6,7)
                    } (* type: pat fixitem *)
                  ] (* type: pat fixitem list *)
                  ,
                  (6,7) (* The pattern in this case is simply 'a' which occurs at position 6, and has length 1 *)
                )
            }
            ,
            (6,11) (* Region of the binding: characters 6 to 11 (starts at 'a', finishes at the ';') *) 
          )
        ] (* Variable declaration list *)
        ,
        [] (* No type declarations *)
      )
      ,
      (2,11) (* Region of the declaration: from characters 2 to 11 *)
    )
  ]

 (* Probably the only relevant information is "a" and "5" and one of those
 constructors that implies that this is just a non-recursive variables*)
