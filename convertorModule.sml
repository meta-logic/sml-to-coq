structure ConvertorModule = 
struct
    open SyntaxModule	
	open ConvertorCore
    local 
		structure G = Gallina
		infix @@		
	in
	    fun strDec2sents (DECStrDec(strDec) @@ _ : StrDec) : G.sentence =
	    	dec2sent strDec
		| 	strDec2sents _ = raise Fail "Unimplemented structure declaration \n"



	    fun topDec2sents (STRDECTopDec(dec, topDec2) @@ _ : TopDec) 
	    											: G.sentence list =
	    	(strDec2sents dec) :: (?(topDec2sents) topDec2)
		| topDec2sents _  = raise Fail "Unimplemented top declaration \n"
	end
end