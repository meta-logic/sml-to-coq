(* Converts an sml AST to a gallina AST *)

signature CONVERTOR =
sig
    val getId : Ast.symbol -> Gallina.ident
    val convertDec : Ast.dec -> Gallina.sentences
    val convertDec : Ast.dec -> Gallina.sentence
    val convertDb : Ast.db -> Gallina.indBody
  (*    val convertTb : Ast.tb -> ? *)
    				  
				  
				  
				  
    				  
				
