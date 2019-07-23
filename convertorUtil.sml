structure ConvertorUtil : CONVERTORUTIL =
struct
structure G = Gallina


	(* Sml symbol to Gallina ident. If ident starts with ' it converts it to _
   	Doesn't take care of Gallina reserved words *)
  	fun symbolToId (s : Ast.symbol) : G.ident = 
    let val s = Symbol.name s in 
    if String.isPrefix "'" s then "_" ^ String.extract(s,1, NONE) else s end

    fun symbolToName (s : Ast.symbol) : G.name = G.Name (symbolToId s)

    fun mkSortTerm (i : int) : G.term = 
    	let val typ = case i of  0 => G.Prop
    							| 1 => G.Type
    							| 2 => G.Set
    	in (G.SortTerm typ) end

end    	
