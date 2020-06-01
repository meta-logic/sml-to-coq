(*
 * Converting hamlet/syntax/SyntaxModuleFn.sml 
 * For each function we provide the following:
 * FROM: hamlet file source code line numbers
 * TO:   gallina.sml source code line numbers
 * FROM SECTION: section and page number in Hamlet's documentation (if appliicable)
 * KEYWORD: keyword in Hamlet's documentation (if applicable)
 * TO SECTION: section and page number in Coq's documentation (if applicable)
 * KEYWORD: keyword in Coq's documentation (if applicable)
 *)
structure ConvertorModule = 
struct
    open SyntaxModule	
	open ConvertorCore
    local 
		structure G = Gallina
		infix @@		
	in
	(* FROM: SyntaxModuleFn.sml: 72 -> 76
	 * TO:   Gallina.sml : 121 -> 128
	 * FROM SECTION: Appendix C.2 page 106
	 * KEYWORD: strdec
	 * TO SECTION: Section 3.1.4 Page 30
	 * KEYWORD: sentence
	 *)	
	fun strDec2sents (DECStrDec(strDec) @@ _ : StrDec) : G.sentence =
	    dec2sent strDec
		| 	strDec2sents _ = raise Fail "Unimplemented structure declaration \n"


  (* FROM: SyntaxModuleFn.sml: 142 -> 145
	 * TO:   Gallina.sml : 121 -> 128
   * FROM SECTION: Appendix C.2 page 106
	 * KEYWORD: topdec
	 * TO SECTION: Section 3.1.4 Page 30
	 * KEYWORD: sentence
	 *)	
	fun topDec2sents (STRDECTopDec(dec, topDec2) @@ _ : TopDec) : G.sentence list =
	    (strDec2sents dec) :: (?(topDec2sents) topDec2)
		| topDec2sents _  = raise Fail "Unimplemented top declaration \n"
	end
end
