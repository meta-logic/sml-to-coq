(* Helper functions for the convertor structure,
   the main convertor is in convertor.sml *)

signature CONVERTORUTIL =
sig
	val symbolToId : Ast.symbol -> Gallina.ident
	val symbolToName : Ast.symbol -> Gallina.name
	val mkSortTerm : int -> Gallina.term
end