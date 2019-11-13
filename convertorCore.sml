(*
 * Converting hamlet/syntax/SyntaxCoreFn.sml and hamlet/syntax/TyVar.sml
 * For each function we provide the following:
 * EXAMPLE: an SML code example
 * FROM: hamlet file source code line numbers
 * TO:   gallina.sml source code line numbers
 * FROM SECTION: section and page number in Hamlet's documentation (if appliicable)
 * KEYWORD: keyword in Hamlet's documentation (if applicable)
 * TO SECTION: section and page number in Coq's documentation (if applicable)
 * KEYWORD: keyword in Coq's documentation (if applicable)
 * NOTES: additional notes
  *)



structure ConvertorCore = 
struct
	open ConvertorUtil
    open SyntaxCore	
    open AnnotationCore
    structure S = StaticObjectsCore
    structure D = DynamicObjectsCore
    local 
		structure G = Gallina
		infix @@
	in
		exception WildCard

		fun scon2term (SCon.STRING s : SCon.SCon) : G.term = G.StringTerm s
			| scon2term (SCon.CHAR s) = G.CharTerm s
			| scon2term (SCon.REAL s) = G.RealTerm s
			| scon2term (SCon.INT (b, s)) = if b = SCon.DEC then G.NumTerm s else G.HexTerm s
			(* Need to check what's a word constant *)
			| scon2term (SCon.WORD (b, s)) = G.WordTerm s 

		fun scon2pattern (SCon.STRING s : SCon.SCon) : G.pattern = G.StringPat s
			| scon2pattern (SCon.CHAR s) = G.CharPat s
			| scon2pattern (SCon.REAL s) = G.RealPat s
			| scon2pattern (SCon.INT (b, s)) = if b = SCon.DEC then G.NumPat s else G.HexPat s
			(* Need to check what's a word constant *)
			| scon2pattern (SCon.WORD (b, s)) = G.WordPat s 

		(* EXAMPLE: type class = (id, name) hashtable :(id, name) forms a tyseq
		 * FROM: SyntaxCoreFn.sml: 159 -> 164
		 * TO:   Gallina.sml : 55
		 * FROM SECTION: Appendix C.1 page 103
		 * KEYWORD: tyseq
		 * TO SECTION: 3.1.3 page 26
		 * KEYWORD: arg
		 * NOTES:
		*)	
		fun tyseq2args (Seq tys : Ty seq') : G.arg list = % ty2arg tys

		(* EXAMPLE: check tyseq2args
		 * FROM: SyntaxCoreFn.sml: 159 -> 164
		 * TO:   Gallina.sml : 55
		 * FROM SECTION: Appendix C.1 page 103
		 * KEYWORD: tyseq
		 * TO SECTION: 3.1.3 page 26
		 * KEYWORD: arg
		 * NOTES: Associativity: Might solve this by explicitly adding 
		 * parenthesis or by requiring the user to explicitly put parenthesis? 
		 *)
		and ty2arg (ty : Ty') : G.arg = G.Arg (ty2term ty)


		(* EXAMPLE: type age = int (ty encodes int)
		 * FROM: SyntaxCoreFn.sml: 159 -> 164
		 * TO:   Gallina.sml : 16 -> 53
		 * FROM SECTION: Appendix C.1 page 103
		 * KEYWORD: ty
		 * TO SECTION: 3.1.3 page 25
		 * KEYWORD: term
		 * NOTES: skipped RECORDTy
		*)	
			(* VARty is type variable, e.g. 'a list  *)
		and ty2term ((VARTy tyvar) : Ty') : G.term = 
				G.IdentTerm (checkLegal(TyVar.toString (~tyvar)))
			(* in scope term because the operator "*" is overloaded *)
			| ty2term (TUPLETyX (tys)) = 
				if List.length(tys) > 1 then
				G.InScopeTerm (G.TupleTerm (% ty2term tys), "type") 
				else
				G.ParensTerm (List.nth ((% ty2term tys), 0))
			(* CONTy is constructor type, e.g. int  *)			
			| ty2term (CONTy (tyseq, tycon)) = let
					val terms = % ty2term ($(~tyseq))
					val tycon = ltycon2id (~tycon)
				in
					(case terms of [] => G.IdentTerm tycon | _ => G.ExplicitTerm(tycon, terms))
				end
			(* PARTy is parenthesis type, e.g. (int)  *)							
			| ty2term (PARTy ty) = G.ParensTerm (ty2term (~ty))
			(* ARROWTy is arrow type, e.g. int -> int  *)							
			| ty2term (ARROWTy(ty1, ty2)) = G.ArrowTerm(ty2term (~ty1), ty2term (~ty2))

		and  clause2defsent (_ : bool) (G.Clause(_, _, NONE) : G.clause) : G.sentence list = []
            | clause2defsent exhaustive (G.Clause(ident, _, SOME typ)) = 
                let
                	val G.ArrowTerm (input, output) = typ
                	val G.ExplicitTerm (_, terms) = output
                	val implicitBinders = mkBinders terms
                    val equation2 = if exhaustive then [] else [G.Equation(G.WildcardPat, G.Axiom G.PatternFailure)]
                    val matchItems = [G.MatchItem (G.IdentTerm "x")]
                    val body = G.Equation(G.ArgsPat(ident, [G.QualidPat "y"]), G.IdentTerm "y") :: equation2
                in
                    G.DefinitionSentence
                    (
                        G.DefinitionDef
                            {localbool = false, 
                            id = "_"^ident, 
                            binders = implicitBinders @ 
                            	[G.SingleBinder{name = G.Name "x", typ = SOME output, inferred = false}],
                            body = G.MatchTerm {matchItems = matchItems, body = body},
                            typ = NONE}
                    ) :: []
                end

		and indBodies2sent (indBodies : G.indBody list) : G.sentence = 
			let
				fun indBody2match (indBody as G.IndBody{clauses, ...}) = 
					let
						val exhaustive = List.length clauses = 1
						val matches = List.concat (List.map (clause2defsent exhaustive) clauses)
					in
						matches
					end
				val matches = List.concat (List.map indBody2match indBodies)
			in
				G.SeqSentences (G.InductiveSentence(G.Inductive indBodies)::matches)
			end


		and mrule2equation (Mrule(pat, exp) : Mrule') : G.equation = 
			let
				val pattern = pat2pattern (~ pat)
				val term = exp2term (~ exp)
			in
				G.Equation(pattern, term)
			end

		and exp2matchitem (exp : Exp') : G.matchItem = G.MatchItem (exp2term(exp))


		and match2equations (Match(mrule, match2) @@ A : Match) : G.equation list = 
			let
				fun match2equations' (Match(mrule, match2)@@_ : Match) =
					(mrule2equation (~mrule)) :: (?match2equations' match2)
				val equation2 = case (try (exhaustive A)) of 
									SOME S.Exhaustive => []
									| _ => [G.Equation(G.WildcardPat, G.Axiom G.PatternFailure)]
				val equations = (mrule2equation (~mrule)) :: (?match2equations' match2) @ equation2
			in
				equations
			end


		and atexp2args (atexp : AtExp') : G.arg list = [G.Arg (atexp2term atexp)]


		and atexp2term (SCONAtExp scon : AtExp') : G.term = scon2term (~scon)
			(* ignoring Op for now *)
			| atexp2term (IDAtExp (_, longvid)) = G.IdentTerm (lvid2id (~longvid))
			| atexp2term (RECORDAtExp _) = raise Fail "Record expressions not yet impemented!\n"
			| atexp2term (LETAtExp (dec, exp)) = raise Fail "Let expressions not yet implemented!\n"
			| atexp2term (PARAtExp exp) = G.ParensTerm (exp2term (~exp))
			| atexp2term (UNITAtExpX) = raise Fail "unit expressions are invalid in Coq! \n"
			(* in scope term because the operator "*" is overloaded *)
			| atexp2term (TUPLEAtExpX(exps)) = G.TupleTerm(% exp2term exps)
			| atexp2term (LISTAtExpX(exps)) = G.ListTerm(% exp2term exps)


		and exp2term (ATExp atexp : Exp') : G.term = atexp2term (~atexp)
			| exp2term (APPExp (exp, atexp)) = 
				G.ApplyTerm(exp2term (~exp), atexp2args (~atexp))
			| exp2term (COLONExp (exp, ty)) = 
				G.HasTypeTerm(exp2term (~exp), ty2term(~ty))
			| exp2term (FNExp match) = raise Fail "Function expressions not yet implemented!\n"
			| exp2term (CASEExpX (exp, match)) = 
			let
				val matchItems = [exp2matchitem (~exp)]
				val equations = match2equations match
			in
				G.MatchTerm {matchItems = matchItems, body = equations}
			end
			| exp2term (IFExpX (exp1, exp2, exp3)) = let
				val exp1' = exp2term (~exp1)
				val exp2' = exp2term (~exp2)
				val exp3' = exp2term (~exp3)
			in
				G.IfTerm {test = exp1', thenTerm = exp2', elseTerm = exp3'}
			end
			| exp2term (ANDALSOExpX (exp1, exp2)) = let
				val exp1' = exp2term (~exp1)
				val exp2' = exp2term (~exp2)
			in
				G.AndTerm (exp1', exp2')
			end
			| exp2term (ORELSEExpX (exp1, exp2)) = let
				val exp1' = exp2term (~exp1)
				val exp2' = exp2term (~exp2)
			in
				G.OrTerm (exp1', exp2')
			end

		and atpat2pattern (WILDCARDAtPat : AtPat') : G.pattern = G.WildcardPat
			| atpat2pattern (SCONAtPat scon) = scon2pattern (~scon)
			(* ignoring Op for now *)
			| atpat2pattern (IDAtPat (_, longvid)) = G.QualidPat (lvid2id (~longvid))
			| atpat2pattern (RECORDAtPat _) = raise Fail "Record patterns not yet implemented!\n"
			| atpat2pattern (PARAtPat pat) = G.ParPat (pat2pattern (~pat))
			| atpat2pattern UNITAtPatX = raise Fail "Unit patterns are invalid in Coq!\n"
			| atpat2pattern (TUPLEAtPatX pats) = G.TuplePat (% pat2pattern pats)
			| atpat2pattern (LISTAtPatX pats) = G.ListPat (% pat2pattern pats)

		and pat2pattern (ATPat atpat  : Pat') : G.pattern = atpat2pattern (~ atpat)
			(* ignoring Op for now *)
			| pat2pattern (CONPat (_, longvid, atpat)) = G.ArgsPat (lvid2id (~longvid), [atpat2pattern (~ atpat)])
			| pat2pattern (COLONPat (pat, ty)) = let 
				val _ = print "Coq doesn't support type casting in patterns!\n" 
				in pat2pattern(~pat) end
			(* ignoring Op for now *)
			| pat2pattern (ASPat(_, vid, ty, pat)) = 
				let 
					val _ = if Option.isSome ty then print "Coq doesn't support type casting in patterns!\n" 
							else () 
				in G.AsPat(pat2pattern(~ pat), vid2id (~vid)) end

		and patternterm2sents (bodyVal : G.term) (G.QualidPat idVal: G.pattern) : G.sentence list = 
				[G.DefinitionSentence(G.DefinitionDef
					{localbool = false, id = idVal, binders = [], typ = NONE, body = bodyVal})]
			| patternterm2sents bodyVal (G.ArgsPat (ident, pats)) =
				let
					val bodyVals = List.tabulate ((List.length pats), (fn i => mkApplyTem i ident bodyVal) )
					val defs = ListPair.zip (bodyVals, pats)
				in
					List.concat (List.map (fn (body, pat) => patternterm2sents body pat) defs)
				end
			| patternterm2sents bodyVal (G.ParPat pat) =
				patternterm2sents bodyVal pat
			| patternterm2sents bodyVal (G.TuplePat pats) = 
				let
					val bodyVals = List.tabulate ((List.length pats), (fn i => mkApplyTem i "tuple" bodyVal) )
					val defs = ListPair.zip (bodyVals, pats)
				in
					List.concat (List.map (fn (body, pat) => patternterm2sents body pat) defs)
				end	
			| patternterm2sents _ (G.WildcardPat) = []
			| patternterm2sents _ _ = raise Fail "Invalid pattern \n"

			
		(* EXAMPLE: type ('a, 'b) age = 'a * 'b  (the lhs ('a, 'b))
		 * FROM: TyVar.sml: 25 -> 29
		 * TO:   Gallina.sml : 59
		 * FROM SECTION: -
		 * KEYWORD: -	
		 * TO SECTION: 3.1.4 page 26
		 * KEYWORD: binder
		 * NOTES:
		 * inferredVal is always false because the variable is always explicit
		*)
		and tyvarseq2binder (tyvars: TyVar.TyVar list) : G.binder list = 
			let
				fun tyvar2binder tyvars = 
					let
					 	val nameVal = mkName (TyVar.toString tyvars)
					 	val typVal = SOME (mkSortTerm 1)
					 	val inferredVal = true
					 in
					 	G.SingleBinder {name = nameVal, typ = typVal, inferred = inferredVal}
					 end 
			in
				List.map tyvar2binder tyvars
			end

		(* EXAMPLE: datatype cards = Hearts | Spades | Clubs | Diamonds (rhs is conbind)
		 * FROM: SyntaxCoreFn.sml: 130
		 * TO:   Gallina.sml : 147
		 * FROM SECTION: Appendix C.1 page 104
		 * KEYWORD: conbind	
		 * TO SECTION: 3.1.4 page 31
		 * KEYWORD: indbody (rhs is a clause list)
		 * NOTES:
		 * ignoring Op for now, check SyntaxCore for more info
		*)
		and conbind2clauses(cons @@ _ : ConBind) : G.clause list = 
			let
				val ConBind(_, tycon, ty, conbind2) = cons
				val idVal = vid2id (~tycon)
				val binderVal = []
				val typVal = (case ty of
					SOME ty' => SOME (ty2term (~ty'))
					| _ => NONE)
				val clauses = ?conbind2clauses conbind2
				val clause = G.Clause (idVal, binderVal, typVal)
			in
				clause :: ?conbind2clauses conbind2
			end

		(* EXAMPLE: type age = int
		 * FROM: SyntaxCoreFn.sml: 123 -> 124
		 * TO:   Gallina.sml : 100 -> 108
		 * FROM SECTION: Appendix C.1 page 104
		 * KEYWORD: typbind/typdesc ---there is a typo in the reference manual
		 	and typbind is replaced by typdesc
		 * TO SECTION: 3.1.4 page 31
		 * KEYWORD: definition
		 * NOTES:
		 * returns sentence list because one typbind can encode multiple 
		 * gallina definitions e.g. type age = int and name = string
		*)			
		and typbind2sent(typbind: TypBind) : G.sentence = 
			let fun typbind2sents (typbind @@ _) = 
				let
					val TypBind(tyvars, tycon, ty, typbind2) = typbind
					val localboolVal = false
					val idVal = tycon2id (~tycon)
					val parametersVal = tyvarseq2binder (List.map ~ ($(~tyvars)))
					val typVal = NONE
					val bodyVal = ty2term (~ty)
		        	val definition = G.DefinitionDef 
		        	{localbool = localboolVal, id = idVal, binders = parametersVal, typ = typVal, body = bodyVal}
		        	val  res = G.DefinitionSentence (definition)				
				in
		        	res :: ?typbind2sents typbind2
				end
			in
				G.SeqSentences (typbind2sents typbind)
			end


		(* EXAMPLE: datatype cards = Hearts | Spades | Clubs | Diamonds
		 * FROM: SyntaxCoreFn.sml: 126 -> 127
		 * TO:   Gallina.sml : 100 -> 108
		 * FROM SECTION: Appendix C.1 page 104
		 * KEYWORD: datbind
		 * TO SECTION: 3.1.4 page 31
		 * KEYWORD: definition
		 * NOTES:
		 * returns G.sentence list to be consistent with typbind2sent 
		*)
		and datbind2sent(datbind : DatBind) : G.sentence =
			let fun datbind2indbodies (datbind @@ _: DatBind) : G.indBody list =
				let
					val DatBind(tyvars, tycon, cons, datbind2) = datbind
					val idVal = tycon2id (~tycon)
					val parametersVal = tyvarseq2binder (List.map ~ ($(~tyvars)))				
					val typVal = mkSortTerm 1
					val clauses = conbind2clauses(cons)
					val clauses = List.map (updateTerm idVal parametersVal) clauses
					val indBody = G.IndBody {id = idVal, bind = parametersVal, typ = typVal, clauses = clauses}
				in 
					indBody :: (?datbind2indbodies (datbind2))
				end 
			in
				indBodies2sent (datbind2indbodies datbind)
			end	

		(* EXAMPLE: 1.  val x = 5
		 *          2.  val (x, y) = (1, 2)
		 * 			3.  val x :: l = [1, 2, 3]
		 * FROM: SyntaxCoreFn.sml: 124 -> 126
		 * TO:   Gallina.sml : 137 -> 138
		*)
		and valbind2sent(valbind: ValBind) : G.sentence = 
			let fun valbind2sents (PLAINValBind(pat, exp, valbind2) @@ A) = 
				(let
					val term = exp2term (~exp)
					val pattern = pat2pattern (~pat)
				in
					(patternterm2sents term pattern) @ (?(valbind2sents) valbind2)
				end)
				| valbind2sents _ = raise Fail "Recursive value bindings are not yet implemented \n"	
			in G.SeqSentences(valbind2sents valbind) end 

		(* FROM: SyntaxCoreFn.sml: 104 -> 114
		 * TO:   Gallina.sml : 100 -> 108
		 * FROM SECTION: Appendix C.1 page 104
		 * KEYWORD: dec
		 * TO SECTION: 3.1.4 page 30
		 * KEYWORD: sentence
		 * NOTES:
		 *)
	  	and dec2sent ((TYPEDec(typbind)@@ _) : Dec): G.sentence = 
		    	typbind2sent typbind
		 | dec2sent (DATATYPEDec(datbind)@@_) = 
		  		datbind2sent datbind
		  (* ignoring tyvarseq for now (function declarations) *)
	     | dec2sent (VALDec(tyvarseq, valbind)@@_) = 
	     		valbind2sent valbind 
	     | dec2sent _ = raise Fail "Unimplemented declaration! \n"
	end 
end