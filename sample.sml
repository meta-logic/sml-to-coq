(* THIS FILE HAD NO COMMENTS WHEN PASSED TO THE PARSE FUNCTION *)

(* This is the only line that was in the file when passed 
    to the parse function *)
(*type ingr = real * string*)
(*type color = int * int * int
datatype skinColor = Dark of color | Light of color
datatype age = Newborn | Years of int

datatype person = Silly of skinColor * age 
				| Greedy of skinColor * age
				| Mysterious of skinColor * age
				| Creepy of skinColor * age
				| Nerd of skinColor * age
				| Happy of skinColor * age*)

datatype person = Person of int -> string				
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

