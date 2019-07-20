(* THIS FILE HAD NO COMMENTS WHEN PASSED TO THE PARSE FUNCTION *)

(* This is the only line that was in the file when passed 
    to the parse function *)
(*type ingr = real * string*)


datatype age = Newborn | Years of int * real * age
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

