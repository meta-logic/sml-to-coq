(* Converts an Sml AST to a Gallina AST *)

structure Convertor : CONVERTOR =
struct
	structure G = Gallina
	structure C = ConvertorUtil

	
  (* 'a list : 'a is a tyvar *)
  fun tyvarToBinder (Ast.MarkTyv (s, _) : Ast.tyvar) : G.binder = tyvarToBinder s
    | tyvarToBinder (Ast.Tyv s) = let
      val nameVal = C.symbolToName s
      val typVal = SOME (C.mkSortTerm 1)
      val inferredVal = true
    in
      G.VarBinder {names = [nameVal], typ = typVal, inferred = inferredVal}
    end

  fun tyvarToTerm (Ast.MarkTyv(tyvar,_) : Ast.tyvar) : G.term = tyvarToTerm tyvar
  | tyvarToTerm (Ast.Tyv tyvar) = G.IdentTerm (C.symbolToId tyvar)

(* Only works if length of ty = 2 *)
  (* skipping records for now.. *)
  fun getConsType (Ast.MarkTy(ty, _) : Ast.ty) : G.term = getConsType ty
    | getConsType (Ast.TupleTy ty) = G.TupleTerm (List.map getConsType ty)
    | getConsType (Ast.VarTy tyvar) = tyvarToTerm tyvar
    | getConsType (Ast.ConTy (s, ty)) = 
      (case s of [sym] 
        => (case Symbol.number sym of 
              0wx65B0 => let val SOME (hd, tl :: l) = List.getItem ty in
                            (* Problem : need to modify this to make arrows 
                            associate to the left instead of right! *)
                            G.ArrowTerm (getConsType hd, getConsType tl) end
              | _ => G.IdentTerm (C.symbolToId sym))
        | _ => raise Fail "More than one symbol!")


  fun getClause (id : G.ident) ((s, ty) : (Ast.symbol * Ast.ty option)) :
   G.clause =
    let val consId = C.symbolToId s
        val bind = []
        val consType = 
        case ty of
          NONE => SOME (G.IdentTerm id)
        | SOME ty => SOME (G.ArrowTerm(getConsType ty, G.IdentTerm id))
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
      val clauses = List.map (getClause id) rhs
      (* typ = Type and not Set because Coq refuses Set for mutually inductive
       datatypes *)   
      val typ = C.mkSortTerm 1
    in
      G.IndBody {id = id, bind = binders, typ = typ, clauses = clauses}
    end

	(* Sml declaration to Gallina sentence *)
    fun decToSentence (Ast.MarkDec (d, _) : Ast.dec): G.sentence = decToSentence d
      | decToSentence (Ast.DatatypeDec {datatycs, withtycs}) = let
        	val dbGallina = G.Inductive (List.map dbToIndbody datatycs)
        	(*val tbGallina = List.map convertTb withtycs ???*)
      	in
        	G.InductiveSentence dbGallina
      	end
      | decToSentence _ = raise Fail "Unimplemented case"		

	(* Sml sequence of declarations to Gallina sentences
	 * Note : This returns a sequence of sentences and not one sentence *)
	fun convertDecs (Ast.SeqDec l: Ast.dec): G.sentences =
   G.SeqSentences (List.map decToSentence l)
		  
end