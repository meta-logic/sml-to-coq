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

        (* Converting SML's ids to Gallina id *)
        fun tycon2id (tycon : TyCon.Id) : G.ident = checkLegal(TyCon.toString tycon)
        fun ltycon2id (tycon : LongTyCon.longId) : G.ident = checkLegal(LongTyCon.toString tycon)
        fun vid2id (tycon : VId.Id) : G.ident = checkLegal(VId.toString tycon)
        fun lvid2id (tycon : LongVId.longId) : G.ident = checkLegal(LongVId.toString tycon)

        (* ? : ('a -> 'b list) * 'a option -> 'b list
           ? f o returns [] if o = NONE and f val if o = SOME val *)
        fun ?exec NONE         = []
          | ?exec (SOME phrase) = exec phrase

        (* $ : 'a SyntaxCore.Seq' -> 'a list *)
        fun $ (Seq l)      = l


        (* ~ : returns the syntax and drops the annotation *)
        fun ~ (x @@ y) = x

        fun % f l = List.map (fn a => f(~a)) l
        (* mkSortTerm returns a Prop, Set or Type Gallina terms *)
        fun mkSortTerm (i : int) : G.term = 
        	let val typ = case i of  0 => G.Prop
        							| 1 => G.Type
        							| 2 => G.Set
        	in (G.SortTerm typ) end

        (* mkArrowTerm returns a Gallina term representing input -> output *)
        fun mkArrowTerm (input : G.term, output : G.term) : G.term =
            G.ArrowTerm (input, output)

        (* mkName makes a Gallina name *)
        fun mkName (s : string) : G.name = G.Name (checkLegal s)


        fun mkApplyTem (i : int) ("tuple" : G.ident) (term :G.term) : G.term = 
            G.ApplyTerm (G.IdentTerm "tuple" , [G.Arg (G.NumTerm (Int.toString i)), G.Arg term])
            | mkApplyTem _ id term = G.ApplyTerm (G.IdentTerm ("_"^id) , [G.Arg term])


        fun mkExplicitTerm ((G.IdentTerm term1): G.term) (terms : G.term list) : G.term =
            G.ExplicitTerm (term1, terms)

        fun updateTerm (_ : G.ident) (_: G.binder list) (clause as G.Clause(_, _, NONE) : G.clause) : G.clause
            = clause
            | updateTerm name parametersVal (clause as G.Clause(id, bL, SOME typ)) = 
            let
                val terms = List.map (fn (G.SingleBinder{name = G.Name name, ...} )=> G.IdentTerm name) parametersVal
                val output = mkExplicitTerm (G.IdentTerm name) terms
            in
                G.Clause (id, bL, SOME(mkArrowTerm (typ, output) ) )
            end

        fun mkBinders (terms : G.term list) : G.binder list = 
            let
                fun term2binder (G.IdentTerm id) = 
                    G.SingleBinder {name = G.Name id, typ = SOME (G.IdentTerm "Type"), inferred = true}
            in
                List.map term2binder terms
            end



        (*fun idFromFixbody (Fixbody (fixbody) : G.fixbody) : G.ident = #id fixbody*)

    end    	
end