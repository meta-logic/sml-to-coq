structure ConvertorCore = 
struct
	open ConvertorUtil
    open SyntaxCore	
    local 
		structure G = Gallina
		infix @@
	in

		(* 
		Issue 1: Associativity: Might solve this by explicitly adding parenthesis
		Or by requiring the user to explicitly put parenthesis?
		Issue 2: Need to formally reason about why the list always has length 1*)
		fun ty2args (ty : Ty') : G.arg list = [G.Arg (ty2term ty)]

		and tyrow2term(tyrow : TyRow) : G.term = 
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
			end

		and ty2term ((VARTy tyvar) : Ty') : G.term = 
				G.IdentTerm (TyVar.toString (~tyvar))
			| ty2term (RECORDTy (SOME tyrow)) = G.InScopeTerm (tyrow2term (tyrow),
				"type")
			| ty2term (CONTy ty) = 
			let
				val (ty', tycon) = ty
				val (Seq ty', tycon) = (~ty', ~tycon)
				val ty' = List.map ~ ty'
			in
				case ty' of
					nil => G.IdentTerm (ltycon2id tycon)
					| [ty'] => G.ApplyTerm (G.IdentTerm (ltycon2id tycon),
											ty2args ty')
					| _ => raise Fail "ty' has length > 1 (line 26) \n"
			end
			| ty2term (PARTy ty) = G.ParensTerm (ty2term (~ty))

		(* type variables e.g. 'a translate to type parameters in Gallina *)
		fun tyvars2binder (tyvars: TyVar.TyVar list) : G.binder list = 
			let
				fun tyvar2binder tyvars = 
					let
					 	val nameVal = mkName (TyVar.toString tyvars)
					 	val typVal = SOME (mkSortTerm 1)
					 	val inferredVal = false
					 in
					 	G.VarBinder {names = [nameVal], typ = typVal, inferred = inferredVal}
					 end 
			in
				List.map tyvar2binder tyvars
			end

		(* ignoring Op for now, check SyntaxCore for more info *)
		fun cons2clauses(cons @@ _ : ConBind) : G.clause list = 
			let
				val ConBind(_, tycon, ty, conbind2) = cons
				val idVal = vidcon2id (~tycon)
				val binderVal = []
				val typVal = case ty of
					SOME ty' => SOME (ty2term (~ty'))
					| _ => NONE
				val clauses = ?cons2clauses conbind2
				val clause = G.Clause (idVal, binderVal, typVal)
			in
				clause :: ?cons2clauses conbind2
			end
			
		fun typbind2sent(typbind @@ _ : TypBind) : G.sentence list = 
			let
				val TypBind(tyvars, tycon, ty, typbind2) = typbind
				val localboolVal = false
				val idVal = tycon2id (~tycon)
				val parametersVal = tyvars2binder (List.map ~ ($(~tyvars)))
				val typVal = NONE
				val bodyVal = ty2term (~ty)
	        	val definition = G.DefinitionDef 
	        	{localbool = localboolVal, id = idVal, parameters = parametersVal, 
	        	typ = typVal, body = bodyVal}
	        	val  res = G.DefinitionSentence definition				
			in
	        	res :: ?typbind2sent typbind2
			end
			
		fun datbind2sent(datbind : DatBind) : G.sentence list =
			let fun datbind2indbodies (datbind @@ _: DatBind) : G.indBody list =
				let
					val DatBind(tyvars, tycon, cons, datbind2) = datbind
					val idVal = tycon2id (~tycon)
					val parametersVal = tyvars2binder (List.map ~ ($(~tyvars)))				
					val typVal = mkSortTerm 1
					val clauses = cons2clauses(cons)
					val clauses = List.map (updateTerm idVal) clauses
					val indBody = G.IndBody {id = idVal, bind = parametersVal,
								typ = typVal, clauses = clauses}
				in 
					indBody :: (? datbind2indbodies (datbind2))
				end
			in
				[G.InductiveSentence(G.Inductive(datbind2indbodies datbind))]
			end		

		(* Sml declaration to Gallina sentence *)
	  	fun dec2sents ((TYPEDec(typbind)@@ _) : Dec): G.sentence list = 
		    	typbind2sent typbind
		  | dec2sents (DATATYPEDec(datbind)@@_) = 
		  		datbind2sent datbind
	      | dec2sents _ = raise Fail "Unimplemented declaration! \n"
	end
end      