structure Convertor : CONVERTOR = 
struct
	structure G = Gallina
	structure C = ConvertorUtil

	fun ?exec NONE         = []
	  | ?exec (SOME phrase) = exec (B, phrase)

	fun $exec (Seq [])      = []
	  | $exec (Seq l) = List.map exec l


	fun tycon2id (tycon @@ _ : TyCon) : G.ident = tycon
	fun ltycon2id (tycon @@ _ : longTyCon) : G.ident = tycon

	(* Issue 1: Adding parens term to avoid associativity issues, this might 
	   result in redundant parenthesis. For example :
	   int (int list) ~> list ((list nat))
	   Issue 2: Need to formally reason about why the list always has length 1*)
	fun ty2args (ty : Ty) : G.arg list = [G.Arg (G.ParensTerm (ty2term ty))]

	and ty2term ((VARTy tyvar @@ _) @@ _ : Ty) : G.term =
		let val {name, ...} = tyvar in G.IdentTerm (name) end
		| ty2term (RECORDTy (tyrow))
		| ty2term (CONTy(ty) @@ _) = 
		let
			val (Seq ty', tycon) = ty
		in
			case ty' of
				nil => G.IdentTerm (ltycon2id tycon)
				| [ty'] => G.ApplyTerm (G.IdentTerm (ltycon2id tycon),
										ty2args ty')
				| _ => raise Fail "ty' has length > 1 (line 26) \n"
		end
		| ty2term ((PARTy ty) @@ _) = G.ParensTerm (ty2term ty)
		| ty2term (())

	(* type variables e.g. 'a translate to type parameters in Gallina *)
	fun tyvars2binder ((tyvars @@ _) : TyVar seq) : G.binder list = 
		let
			fun tyvar2binder {name, ...} = 
				let
				 	val nameVal = name
				 	val typVal = SOME (C.mkSortTerm 1)
				 	val inferredVal = false
				 in
				 	G.VarBinder {names = [nameVal], typ = typVal, inferred = inferredVal}
				 end 
		in
			$tyvar2binder tyvars
		end
		

	(* Sml declaration to Gallina sentence *)
  	fun dec2sent (TYPEDec(typbind)@@ _) : Dec'): G.sentence = 
		let val (tyvars, tycon @@ _, ty, typbind2) = typbind
			val localboolVal = false
			val idVal = tycon2id tycon
			val parametersVal = tyvars2binder tyvars
			val typVal = NONE
			val bodyVal = ty2term ty


			@ ?dec2sent typbind2


      | decToSentence (Ast.SeqDec l) = G.SeqSentences (List.map decToSentence l)
      | decToSentence (Ast.DatatypeDec {datatycs, withtycs}) = 
        	G.InductiveSentence(G.Inductive (List.map dbToIndbody datatycs))
      | decToSentence (Ast.TypeDec l) = G.SeqSentences (List.map tbToSent l)
      (*| decToSentence (ast as Ast.ValDec (l, l')) = let
        val absyn = Main.getAbsyn(Ast.ValDec (l, l'))
      in
        CA.decToSentence(ast, absyn)
      end*)

      | decToSentence _ = raise Fail "Unimplemented case"	 	
end