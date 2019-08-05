(*structure ConvertorAbsyn = 
struct
	structure G = Gallina
	structure A = Absyn
	structure VC = VarCon
	structure S = Symbol
	structure SP = SymPath
	structure CU = ConvertorUtil
	structure T = Types

	type pattern = {id : G.ident, parameters: G.binder list, typ : G.term option}

	fun varToId (var : VC.var) : G.ident = case var of
		VC.VALvar {path = SP.SPATH l, ...} => CU.symbolToId (List.hd l)
		| _ => raise Fail "Unimplemened! \n"

	fun expToArgs ()

	and expToTerm (A.MARKexp (exp, _) : A.exp) : G.term = expToTerm exp
		| expToTerm (A.VARexp (ref (var), _)) = G.IdentTerm (varToId (var))
		| expToTerm (A.CONexp (T.DATACON {name, ...}, _) = G.IdentTerm (CU.symbolToId)
		| expToTerm (A.INTexp (i, _)) = G.NumTerm (i)
		(* ignoring: WORDexp, REALexp, STRINGexp, CHARexp, RECORDexp,
					 SELECTexp, VECTORexp, PARCKexp *)
		| expToTerm (A.APPexp (exp1, exp2)) = 
			G.ApplyTerm (expToTerm exp1, expToArgs exp2)


	fun convVar(((A.VARpat var),exp) : A.pat * A.exp) : (pattern * G.term) list
		= case var of 
		VC.VALvar {path = SP.SPATH l, ...} => 
		let
			val localboolVal = false
			val idVal = CU.symbolToId (List.hd l)
			val parametersVal = []
			val typVal = NONE
			val bodyVal = expToTerm exp
			val definition = G.DefinitionDef {localbool = localboolVal, id =
         idVal, parameters = parametersVal, typ = typVal, body = bodyVal}
		in
			G.DefinitionSentence definition
		end
		| VC.OVLDvar _ => raise Fail "Unimplemened! \n"


	fun rmvMark ((A.MARKpat(pat, _), exp) : A.pat * A.exp) : A.pat * A.exp
	 		= rmvMark (pat, exp)
	 | rmvMark (pat, A.MARKexp(exp, _))
			= rmvMark (pat, exp)
	 | rmvMark (pat, exp) 
	 		= (pat, exp)


    fun vbToSent (A.Vb {pat, exp, ...} : A.vb) : G.sentence = let
    	val (pat, exp) = rmvMark (pat, exp) 


        val localboolVal = false
        val idVal = 
        val parametersVal = []
        val typVal = NONE
        val bodyVal = expToTerm exp
        val definition = G.DefinitionDef {localbool = localboolVal, id =
         idVal, parameters = parametersVal, typ = typVal, body = bodyVal}
      in
        G.DefinitionDef definition
      end




end*)