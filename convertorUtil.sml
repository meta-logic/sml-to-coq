structure ConvertorUtil =
struct
    structure G = Gallina
    open SyntaxCore
    open SyntaxModule
    open SyntaxProgram    
    open Annotation;

    infix @@;
	(* Sml symbol to Gallina ident. If ident starts with ' it converts it to _
   	Doesn't take care of Gallina reserved words *)
    fun tycon2id (tycon : TyCon.Id) : G.ident = TyCon.toString tycon
    fun ltycon2id (tycon : LongTyCon.longId) : G.ident = LongTyCon.toString tycon

    fun ?exec NONE         = []
      | ?exec (SOME phrase) = exec phrase

    fun $ (Seq l)      = l

    fun ~ (x @@ y) = x
    (*fun symbolToName (s : Ast.symbol) : G.name = G.Name (symbolToId s)*)

    fun mkSortTerm (i : int) : G.term = 
    	let val typ = case i of  0 => G.Prop
    							| 1 => G.Type
    							| 2 => G.Set
    	in (G.SortTerm typ) end

    fun mkName (s : string) : G.name = G.Name s

end    	
