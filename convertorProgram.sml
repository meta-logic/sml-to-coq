(*
 * Converting hamlet/syntax/SyntaxProgramFn.sml 
 * For each function we provide the following:
 * FROM: hamlet file source code line numbers
 * TO:   gallina.sml source code line numbers
 * FROM SECTION: section and page number in Hamlet's documentation (if appliicable)
 * KEYWORD: keyword in Hamlet's documentation (if applicable)
 * TO SECTION: section and page number in Coq's documentation (if applicable)
 * KEYWORD: keyword in Coq's documentation (if applicable)
 *)
structure ConvertorProgram = 
struct
    open SyntaxProgram    	
	open ConvertorModule
    local 
		structure G = Gallina
		infix @@		
	in
	(* FROM: SyntaxProgramFn.sml: 28
	 * TO:   Gallina.sml : 121 -> 128
	 * FROM SECTION: Appendix C.2 page 106
	 * KEYWORD: program
	 * TO SECTION: Section 4.1.4 Page 120
	 * KEYWORD: sentence
	 *)	
	fun program2sents (Program(prog, prog2) @@ _ : Program) : G.sentence list
		  =
			(topDec2sents  prog) @ (? (program2sents) prog2)
	end
end
