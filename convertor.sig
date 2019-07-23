(* Converts an sml AST to a gallina AST *)

signature CONVERTOR =
sig
	val decToSentence : Ast.dec -> Gallina.sentence
    val convertDecs : Ast.dec -> Gallina.sentences
    val dbToIndbody : Ast.db -> Gallina.indBody
  (*    val convertTb : Ast.tb -> ? *)
end    				  
				  
				  
				  
    				  
