structure ConvertorProgram = 
struct
    open SyntaxProgram    	
	open ConvertorModule
    local 
		structure G = Gallina
		infix @@		
	in
	    fun program2sents (Program(prog, prog2) @@ _ : Program) : G.sentence list
		=
			(topDec2sents prog) @ (?program2sents prog2)
	end
end