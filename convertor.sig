(* Converts an sml AST to a gallina AST *)

signature CONVERTOR =
sig
    val convertDec' : Ast.dec -> Gallina.sentences
    val convertDec : Ast.dec -> Gallina.sentence
    val convertDb : Ast.db -> Gallina.indBody
  (*    val convertTb : Ast.tb -> ? *)
end    				  
				  
				  
				  
    				  
