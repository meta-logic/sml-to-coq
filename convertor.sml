(* Converts an Sml AST to a Gallina AST *)

structure Convertor : CONVERTOR =
struct
	structure G = Gallina
	structure C = ConvertorUtil

	
  (* 'a list : 'a is a tyvar (type variable)
      Usually translates to (_a : Type) if inferred = false
      or {_a : Type} if infereed = true*)
  fun tyvarToBinder (Ast.MarkTyv (s, _) : Ast.tyvar) : G.binder = tyvarToBinder s
    | tyvarToBinder (Ast.Tyv s) = let
      val nameVal = C.symbolToName s
      val typVal = SOME (C.mkSortTerm 1)
      val inferredVal = false
    in
      G.VarBinder {names = [nameVal], typ = typVal, inferred = inferredVal}
    end

  (* 'a list : 'a is a tyvar (type variable) 
     This returns just _a as a term *)
  fun tyvarToTerm (Ast.MarkTyv(tyvar,_) : Ast.tyvar) : G.term = tyvarToTerm tyvar
  | tyvarToTerm (Ast.Tyv tyvar) = G.IdentTerm (C.symbolToId tyvar)

  fun tyvarToArg (Ast.MarkTyv(tyvar,_) : Ast.tyvar) : G.arg = tyvarToArg tyvar
  | tyvarToArg (tyvar) = G.Arg (tyvarToTerm tyvar)
  (* Skipping Record types for now
     There should be no way to get ConTy because ConTy stands
     for a constructor and this function is only called to get
     the type variables that are applied to a type 
     e.x ('a, 'b) list shoud return G.arg TupleTerm [_a, _b] *)
  fun tyToArg (Ast.MarkTy(ty, _) : Ast.ty) : G.arg = tyToArg ty
    | tyToArg (Ast.VarTy ty) = G.Arg (tyvarToTerm ty)
    | tyToArg (Ast.TupleTy ty) = G.Arg (G.TupleTerm (List.map tyToTerm ty))
    | tyToArg (Ast.ConTy ([s], ty)) = 
      G.Arg (G.ApplyTerm (G.IdentTerm (C.symbolToId s), 
        List.map tyToArg ty) )
    | tyToArg (Ast.ConTy _) = raise Fail "More than one symbol! \n"
    | tyToArg _ = raise Fail "Unimplemented Cons type! \n"        

  (* skipping records for now.. *)
  and tyToTerm (Ast.MarkTy(ty, _) : Ast.ty) : G.term = tyToTerm ty
    | tyToTerm (Ast.TupleTy ty) = G.TupleTerm (List.map tyToTerm ty)
    | tyToTerm (Ast.VarTy tyvar) = tyvarToTerm tyvar
    (* Only works if length of ty = 2 *)
    | tyToTerm (Ast.ConTy ([s], ty)) = 
        (case Symbol.number s of 
          (* Problem : need to modify this to make arrows associate to the left instead of right! *)
          0wx65B0 => let val SOME (hd, tl :: l) = List.getItem ty in
                      G.ArrowTerm (tyToTerm hd, tyToTerm tl) end
          | _ => G.ApplyTerm (G.IdentTerm (C.symbolToId s), List.map tyToArg ty))        
    | tyToTerm (Ast.ConTy _) = raise Fail "More than one symbol! \n"
    | tyToTerm _ = raise Fail "Unimplemented Cons type! \n"


  fun getClause (retTyp : G.term) ((s, ty) : (Ast.symbol * Ast.ty option)) :
   G.clause =
    let val consId = C.symbolToId s
        val bind = []
        val consType = 
        case ty of
          NONE => NONE
        | SOME ty => SOME (G.ArrowTerm(tyToTerm ty, retTyp))
    in G.Clause(consId, bind, consType) end



  (* Sml data bindings to Gallina inductive body
     This is the whole body of a datatype 
     db is an argument in: -and probably they all translate to indbody-
     DatatypeDec ( Datatype declarations )
     AbstypeDec ( Abstract type declarations -- advanced sml feature )
     DataSpec ( Datatype in signatures ) *)
    fun dbToIndbody (Ast.MarkDb (db, _)): G.indBody = dbToIndbody db
    | dbToIndbody (Ast.Db {tyc, tyvars, rhs,...}) = let
      val id = C.symbolToId tyc (* tree *)
      val binders = if tyvars = [] then [] else 
                  List.map tyvarToBinder tyvars
      val retType = if tyvars = [] then G.IdentTerm(id)
                    else G.ApplyTerm (G.IdentTerm(id), List.map tyvarToArg tyvars)
      val clauses = List.map (getClause retType) rhs
      (* typ = Type and not Set because Coq refuses Set for mutually inductive
       datatypes *)   
      val typ = C.mkSortTerm 1
    in
      G.IndBody {id = id, bind = binders, typ = typ, clauses = clauses}
    end

    fun tbToSent (Ast.MarkTb (t, _) : Ast.tb) : G.sentence = tbToSent t
      | tbToSent (Ast.Tb {tyc, def, tyvars}) = let
        val localboolVal = false
        val idVal = C.symbolToId tyc
        val parametersVal = if tyvars = [] then [] else 
                  List.map tyvarToBinder tyvars
        val typVal = NONE
        val bodyVal = tyToTerm def

      in
        G.DefinitionSentence (G.DefinitionDef {localbool = localboolVal, id =
         idVal, parameters = parametersVal, typ = typVal, body = bodyVal})
      end


	(* Sml declaration to Gallina sentence *)
    fun decToSentence (Ast.MarkDec (d, _) : Ast.dec): G.sentence = decToSentence d
      | decToSentence (Ast.SeqDec l) = G.SeqSentences (List.map decToSentence l)
      | decToSentence (Ast.DatatypeDec {datatycs, withtycs}) = let
        	val dbGallina = G.Inductive (List.map dbToIndbody datatycs)
        	(*val tbGallina = List.map convertTb withtycs ???*)
      	in
        	G.InductiveSentence dbGallina
      	end
      | decToSentence (Ast.TypeDec l) = G.SeqSentences (List.map tbToSent l)
      | decToSentence _ = raise Fail "Unimplemented case"		


		  
end