(* Converts an sml AST to a gallina AST *)

signature CONVERTOR =
sig
	val tyvarToBinder : Ast.tyvar -> Gallina.binder
	val tyvarToTerm : Ast.tyvar -> Gallina.term
	val tyvarToArg : Ast.tyvar -> Gallina.arg 
	val tyToArg : Ast.ty -> Gallina.arg 
	val tyToTerm : Ast.ty -> Gallina.term 
	val getClause : Gallina.term -> (Ast.symbol * Ast.ty option) ->	Gallina.clause
	val tbToSent : Ast.tb -> Gallina.sentence
	val decToSentence : Ast.dec -> Gallina.sentence
    val dbToIndbody : Ast.db -> Gallina.indBody
end    				  
				  
				  
				  
    				  
