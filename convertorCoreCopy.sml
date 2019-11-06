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
				G.InScopeTerm (G.TupleTerm (% ty2term tys), "type") 
			(* CONTy is constructor type, e.g. int  *)			
			| ty2term (CONTy (tyseq, tycon)) = let
					val args = tyseq2args (~tyseq)
					val tycon = G.IdentTerm(ltycon2id (~tycon))
				in
					case args of [] => tycon | _ => G.ApplyTerm(tycon, args)
				end
			(* PARTy is parenthesis type, e.g. (int)  *)							
			| ty2term (PARTy ty) = G.ParensTerm (ty2term (~ty))
			(* ARROWTy is arrow type, e.g. int -> int  *)							
			| ty2term (ARROWTy(ty1, ty2)) = G.ArrowTerm(ty2term (~ty1), ty2term (~ty2))

		fun atexp2args (atexp : AtExp') : G.arg list = [G.Arg (atexp2term atexp)]



		and atexp2term (SCONAtExp scon : AtExp') : G.term = scon2term (~scon)
			(* ignoring Op for now *)
			| atexp2term (IDAtExp (_, longvid)) = G.IdentTerm (lvid2id longvid)
			(* in scope term because the operator "*" is overloaded *)
			| atexp2term (TUPLEAtExpX(exps)) = G.InScopeTerm ((List.map exp2term exps), "type")
			(* ignoring records and units *)
			| atexp2term (LISTAtExpX(exps)) = G.ListTerm(List.map exp2term exps)
			| atexp2term (PARAtExp exp) = G.ParensTerm (exp2term (~exp))
			| atexp2term (LETAtExp (dec, exp)) = 
				let
					val dec' = dec2sent dec
					val exp' = exp2term exp
				in
					sent2let(dec', exp')
				end
			| atexp2term _ = raise Fail "unexpected atmoic expression! \n"

		and sent2let (dec : G.sentence, exp : G.term) : G.term = 
				case dec of
					G.Fixpointsentence(G.Fixpoint fixes) => 
						G.LetTerm 
							{id = mkUniqueId(),
							binders = [], 
							typ = NONE,
							body = G.FixTerm (Fixbodies fixes, idFromFixbody (List.nth 0 fixes))
							inBody = exp}
					| G.DefinitionSentence(G.DefinitionDef (def, category)) => 
						(case category of 
							One => G.LetTerm 
									{id = #id def, 
									binders = #binders def,
								   	typ = #typ def, 
								   	body = #body def, 
								   	inBody = exp}
							| Two pattern => G.LetPatternTerm 
									{pat = pattern, 
									 inTerm = NONE,
									 body = ???})
					| G.SeqSentences (sents) =>




		and exp2term (AtExp atexp : Exp') : G.term = atexp2term (~atexp)
			| exp2term (APPExp (exp, atexp)) = 
				G.ApplyTerm(exp2term (~exp), atexp2args (~atexp))
			| exp2term (COLONExp (exp, ty)) = 
				G.HasTypeTerm(exp2term (~exp), ty2term(~ty))
			| exp2term (FNExp match)
			| exp2term (CASEExpX (exp, match))
			| exp2term (IFExpX (exp1, exp2, exp3)) = let
				val exp1' = exp2term exp1
				val exp2' = exp2term exp2
				val exp3' = exp2term exp3
			in
				G.IfTerm {test = exp1', thenTerm = exp2', elseTerm = exp3'}
			end
			| exp2term (ANDALSOExpX (exp1, exp2)) = let
				val exp1' = exp2term exp1
				val exp2' = exp2term exp2
			in
				G.AndTerm (exp1', exp2')
			end
			| exp2term (ORELSEExpX (exp1, exp2)) = let
				val exp1' = exp2term exp1
				val exp2' = exp2term exp2
			in
				G.OrTerm (exp1', exp2')
			end



		and atpatterm2sent(WILDCARDAtPat : AtPat', _ : G.term) : G.sentence list =
				raise Fail "Wildcard cannot be an id in Coq \n"
			| atpatterm2sent(SCONAtExp scon, _) = 
				raise Fail "Scon cannot be an id in Coq \n"
			(* Ignoring Op *)
			| atpatterm2sent(IDAtPat(_, longvid), term) = 
				let
					val localboolVal = false
					val idVal = lvid2id longvid
					val parametersVal = []
					val typVal = NONE
					val bodyVal = term
				in
					G.DefinitionSentence(
					G.DefinitionDef{localbool = localboolVal, id = idVal, 
					parameters = parametersVal, typ = typVal, body = bodyVal})
				end
			(* ignoring records and units *)
			| atpatterm2sent(RECORDAtPat patrow, term) = 
				(case patrow of	NONE => raise Fail "unit patterns are illegal in Coq\n"
					| SOME patrow => let
						val G.TupleTerm terms = term
					in
						patrowterms2sent(patrow, terms)
					end




		and patterm2sent(ATPat atpat : Pat',exp : Exp', A : ValBind_attr annotation) : G.sentence list = 
			let
				val valEnv = Prop.get (Prop.hd (Prop. tl A))
					
			in
				body
			end

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
					 	val inferredVal = false
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
				val typVal = case ty of
					SOME ty' => SOME (ty2term (~ty'))
					| _ => NONE
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
		and typbind2sent(typbind @@ _ : TypBind) : G.sentence list = 
			let
				val TypBind(tyvars, tycon, ty, typbind2) = typbind
				val localboolVal = false
				val idVal = tycon2id (~tycon)
				val parametersVal = tyvarseq2binder (List.map ~ ($(~tyvars)))
				val typVal = NONE
				val bodyVal = ty2term (~ty)
	        	val definition = G.DefinitionDef (
	        	{localbool = localboolVal, id = idVal, parameters = parametersVal, 
	        	typ = typVal, body = bodyVal, def2 = NONE}, G.One)
	        	val  res = G.DefinitionSentence (definition)				
			in
	        	G.SeqSentences (res :: ?typbind2sent typbind2)
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
					val clauses = List.map (updateTerm idVal) clauses
					val indBody = G.IndBody {id = idVal, bind = parametersVal,
								typ = typVal, clauses = clauses}
				in 
					indBody :: (? datbind2indbodies (datbind2))
				end
			in
				G.InductiveSentence(G.Inductive(datbind2indbodies datbind))
			end		


		and valbind2sent(PLAINValBind(pat, exp, valbind2) @@ A: ValBind) : G.sentence = 
				patterm2sent(~pat, ~exp, A) @ ?valbind2sent valbind2
			| valbind2sent _ => raise Fail "Recursive value bindings are not yet implemented \n"

		(* FROM: SyntaxCoreFn.sml: 104 -> 114
		 * TO:   Gallina.sml : 100 -> 108
		 * FROM SECTION: Appendix C.1 page 104
		 * KEYWORD: dec
		 * TO SECTION: 3.1.4 page 30
		 * KEYWORD: sentence
		 * NOTES:
		 *)
	  	and dec2sents ((TYPEDec(typbind)@@ _) : Dec): G.sentence = 
		    	typbind2sent typbind
		  | dec2sent (DATATYPEDec(datbind)@@_) = 
		  		datbind2sent datbind
		  (* ignoring tyvarseq for now (function declarations) *)
	      | dec2sent (VALDec(tyvarseq, valbind)@@_) = valbind2sent valbind
	      | dec2sent _ = raise Fail "Unimplemented declaration! \n"
	end
end      