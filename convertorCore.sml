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

		(* EXAMPLE: type student = int * string would evaluate to:
		 * 			type student = {1: int, 2: string} and each element in the 
		 *			record is a tyrow
		 * FROM: SyntaxCoreFn.sml: 167
		 * TO:   Gallina.sml :  16 -> 53
		 * FROM SECTION: Appendix C.1 page 103
		 * KEYWORD: tyrow	
		 * TO SECTION: 3.1.3 page 25
		 * KEYWORD: term
		 * NOTES: assuming they're always tuples for now
		*)
(*		and tyrow2term(tyrow : TyRow) : G.term = 
			let fun tyrow2terms (tyrow') = 
				let
					val tyrow @@ annot = tyrow'
					val TyRow(lab, ty, tyrow) = tyrow
					val ty = ~ty
					val isTuple = has(hd (tl (tl annot)))
				in
					if isTuple
					then (ty2term ty) :: ?tyrow2terms tyrow
					else raise Fail "RECORDTy is not yet implemented! \n"
				end
			in
				G.TupleTerm (tyrow2terms tyrow)
			end*)

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

(*		fun atexp2args (atexp : AtExp') : G.arg list = [G.Arg (atexp2term atexp)]

		and exprow2term (exprow : ExpRow) : G.term = 
			let fun exprow2terms (exprow') = 
				let
					val exprow @@ annot = exprow'
					val ExpRow(lab, exp, exprow2) = exprow
					val isTuple = has(hd (tl (tl annot)))
				in
					if isTuple
					then (exp2term (~exp)) :: ?exprow2terms exprow
					else raise Fail "RECORDExp is not yet implemented! \n"
				end
			in
				G.TupleTerm (exprow2terms exprow)
			end
*)

(*		and atexp2term (SCONAtExp scon : AtExp') : G.term = scon2term (~scon)
*)			(* ignoring Op for now *)
(*			| atexp2term (IDAtExp (_, longvid)) = G.IdentTerm (lvid2id longvid)
*)			(* in scope term because the operator "*" is overloaded *)
			(* ignoring records and units *)
(*			| atexp2term (RECORDAtExp (exprowOpt)) = 
				case exprowOpt of
					NONE => raise Fail "unit expressions not allowed in Coq\n"
					| SOME exprow => G.InScopeTerm (exprow2term (exprow), "type") 
			| atexp2term (PARAtExp exp) = G.ParensTerm (exp2term (~exp))*)
			(*| atexp2term (LETAtExp ) = *)
(*
		and exp2term (AtExp atexp : Exp') : G.term = atexp2term (~atexp)
			| exp2term (APPExp (exp, atexp)) = 
				G.ApplyTerm(exp2term (~exp), atexp2args (~atexp))
			| exp2term (COLONExp (exp, ty)) = 
				G.HasTypeTerm(exp2term (~exp), ty2term(~ty))*)
			(*| exp2term (FNExp match)*)

(*		and patrowterms2sent (terms : G.term list) (patrow : PatRow)
			: G.sentence list = 

			let val patrow @@ annot = patrow'
				val isTuple = has(hd (tl (tl annot)))
			in
				if not (isTuple)
				then raise Fail "RECORDAtPat is not yet implemented! \n"
				else case patrow of
					DOTSPatRow => 
						raise Fail "Record patterns are not yet implemented \n"
					| FIELDPatRow(_, pat, patrow2) => 
						patterm2sent(~pat, List.nth(terms, 0))
						@ ?(patrowterms2sent (List.tl terms)) patrow2					
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
					end*)




(*		and patterm2sent(ATPat atpat : Pat',term : G.term) : G.sentence list = 
			atpatterm2sent(~atpat, term)*)

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
		fun tyvarseq2binder (tyvars: TyVar.TyVar list) : G.binder list = 
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
		fun conbind2clauses(cons @@ _ : ConBind) : G.clause list = 
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
		fun typbind2sent(typbind @@ _ : TypBind) : G.sentence list = 
			let
				val TypBind(tyvars, tycon, ty, typbind2) = typbind
				val localboolVal = false
				val idVal = tycon2id (~tycon)
				val parametersVal = tyvarseq2binder (List.map ~ ($(~tyvars)))
				val typVal = NONE
				val bodyVal = ty2term (~ty)
	        	val definition = G.DefinitionDef 
	        	{localbool = localboolVal, id = idVal, parameters = parametersVal, 
	        	typ = typVal, body = bodyVal}
	        	val  res = G.DefinitionSentence definition				
			in
	        	res :: ?typbind2sent typbind2
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
		fun datbind2sent(datbind : DatBind) : G.sentence list =
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
				[G.InductiveSentence(G.Inductive(datbind2indbodies datbind))]
			end		


(*		fun valbind2sent(PLAINValBind(pat, exp, valbind2) @@ _: ValBind) : G.sentence list = 
				patterm2sent(~pat, exp2term (~exp)) @ ?valbind2sent valbind2
			| valbind2sent _ => raise Fail "Recursive value bindings are not yet implemented \n"*)

		(* FROM: SyntaxCoreFn.sml: 104 -> 114
		 * TO:   Gallina.sml : 100 -> 108
		 * FROM SECTION: Appendix C.1 page 104
		 * KEYWORD: dec
		 * TO SECTION: 3.1.4 page 30
		 * KEYWORD: sentence
		 * NOTES:
		 *)
	  	fun dec2sents ((TYPEDec(typbind)@@ _) : Dec): G.sentence list = 
		    	typbind2sent typbind
		  | dec2sents (DATATYPEDec(datbind)@@_) = 
		  		datbind2sent datbind
		  (* ignoring tyvarseq for now (function declarations) *)
(*	      | dec2sents (VALDec(tyvarseq, valbind)@@_) = valbind2sent valbind
*)	      | dec2sents _ = raise Fail "Unimplemented declaration! \n"
	end
end      