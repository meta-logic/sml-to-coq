structure ConvertorUtil =
struct

    structure G = Gallina
    structure Sort = Quicksort
    structure Key = ListOrdered(StringOrdered)
    structure LT = SplayDict (structure Key = Key) (* LabelsTracker *)
    structure TT = SplaySet(structure Elem = StringOrdered) (* Tyvar tracker *)
    open Annotation;

    local
        open SyntaxCore
    in
        infix @@;
        val rid_ctr = ref 0 (* record id counter *)
    	(* Sml symbol to Gallina ident. If ident starts with ' it converts it to _
        	Doesn't take care of Gallina reserved words *)
        fun checkLegal (s : string) : G.ident =
            if String.isPrefix "'" s then "_" ^ String.extract(s,1, NONE) else s

        (* Converting SML's ids to Gallina id *)
        fun tycon2id (tycon : TyCon.Id) : G.ident = checkLegal(TyCon.toString tycon)
        fun ltycon2id (tycon : LongTyCon.longId) = checkLegal(LongTyCon.toString tycon)
        fun vid2id (tycon : VId.Id) = checkLegal(VId.toString tycon)
        fun lvid2id (tycon : LongVId.longId) = checkLegal(LongVId.toString tycon)
        fun strid2id (strid : StrId.Id) = checkLegal(StrId.toString strid)
        fun lstrid2id (lstrid : LongStrId.longId) = checkLegal(LongStrId.toString lstrid)
        fun sigid2id (sigid : SigId.Id) = checkLegal(SigId.toString sigid)
        fun funid2id (funid : FunId.Id) = checkLegal(FunId.toString funid)

        (* ? : ('a -> 'b list) * 'a option -> 'b list
           ? f o returns [] if o = NONE and f val if o = SOME val *)
        fun ?exec NONE         = []
          | ?exec (SOME phrase) = exec phrase

        (* $ : 'a SyntaxCore.Seq' -> 'a list *)
        fun $ (Seq l)      = l


        (* ~ : returns the syntax and drops the annotation *)
        fun ~ (x @@ y) = x

        fun % f l = List.map (fn a => f(~a)) l

        fun mkMatchNotationTerm (matcher : G.matchItem,  matchees: G.pattern) (body : G.term, exhaustive : bool) =
            G.MatchNotationTerm {matchItem = matcher, body = G.Equation(matchees, body), exhaustive = exhaustive}
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

        fun mkEbinders (_ :  int, [] : G.term list) : G.ebinder list = []
          | mkEbinders (n, typ::typs) = G.ESingleBinder { name = mkName("x"^(Int.toString n)), typ = typ, inferred = false} :: mkEbinders(n+1, typs)


        fun extractTyp (G.SingleBinder {name = G.Name id, ...} : G.binder) : G.term = G.IdentTerm id
          | extractTyp _ = raise Fail "Unexpected binder \n"

        fun genIdent () = (rid_ctr := !rid_ctr + 1; "rid_" ^ (Int.toString (!rid_ctr)))

        fun gentyps (n : int) = let 
            fun mkSingleBinder i =
                G.SingleBinder {name = G.Name ("_ty"^ (Int.toString i)),
                                 typ = SOME (G.IdentTerm "Type"), inferred = true}
        in
            List.tabulate (n, mkSingleBinder)
        end

        fun opetize (SOME Op : Op option) (id : G.ident) : G.ident = "op" ^ id
          | opetize _ id = id

        fun updateSigBody (G.SigBody(sents)) (id, binders, ty) : G.signatureBody =
            let fun updateSent(sent) =
                    case sent of G.SeqSentences(sents) => G.SeqSentences(List.map updateSent sents)
                               | G.AssumptionSentence(G.Assumption(keyword, id', body)) => 
                                 if id' = id
                                 then G.DefinitionSentence(G.DefinitionDef{localbool = false, id = id, binders = binders, body = ty, typ = NONE})
                                 else sent
                               | _ => sent
            in
                G.SigBody(List.map updateSent sents)
            end

        fun updateTyvarCtx (tyvars : TyVar seq) (tyvarctx : TT.set) : TT.set =
            let
                fun tyvarseq2strings (tyvars: TyVar.TyVar list) : string list = List.map TyVar.toString tyvars
                val tyvars = tyvarseq2strings (List.map ~ ($(~tyvars)))
                fun update [] ctx = ctx
                  | update (tyvar::tyvars) ctx = TT.insert (update tyvars ctx) tyvar
            in
                update tyvars tyvarctx
            end

        fun orderLabs labs = Sort.sort String.compare (labs)

        (*fun idFromFixbody (Fixbody (fixbody) : G.fixbody) : G.ident = #id fixbody*)

    end    	
end
