structure ConvertorUtil =
struct
    structure G = Gallina
    open Annotation;

    local
        open SyntaxCore
    in

        infix @@;
    	(* Sml symbol to Gallina ident. If ident starts with ' it converts it to _
       	Doesn't take care of Gallina reserved words *)
        fun checkLegal (s : string) : G.ident = 
            if String.isPrefix "'" s then "_" ^ String.extract(s,1, NONE) else s            

        fun tycon2id (tycon : TyCon.Id) : G.ident = checkLegal(TyCon.toString tycon)
        fun ltycon2id (tycon : LongTyCon.longId) : G.ident = checkLegal(LongTyCon.toString tycon)
        fun vidcon2id (tycon : VId.Id) : G.ident = checkLegal(VId.toString tycon)


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

        fun mkArrowTerm (input : G.term, output : G.term) : G.term =
            G.ArrowTerm (input, output)
        fun mkName (s : string) : G.name = G.Name s

        fun updateTerm (_ : G.ident) (clause as G.Clause(_, _, NONE) : G.clause) : G.clause
            = clause
            | updateTerm name (clause as G.Clause(id, bL, SOME typ)) = 
                G.Clause (id, bL, SOME(mkArrowTerm (typ, G.IdentTerm name) ) )


    end    	
end