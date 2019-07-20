(* Converts an Sml AST to a Gallina AST *)

structure Convertor : CONVERTOR =
struct
	structure G = Gallina
	
	(* Sml symbol to Gallina ident
	   Takes care of Sml identifiers that start with '
	   Doesn't take care of Gallina reserved words *)
	fun symbolToId (s : Ast.symbol) : G.ident = 
		let val s = Symbol.name s in
		if String.isPrefix "'" s
		then "_" ^ String.extract(s,1, NONE) else s end
	
  (* 'a list : 'a is a tyvar *)
  fun tyvarToBinder (Ast.MarkTyv (s, _) : Ast.tyvar) : G.binder = tyvarToBinder s
    | tyvarToBinder (Ast.Tyv s) = let
      val nameVal = G.Name (symbolToId s)
      val typVal = SOME (G.SortTerm(G.Type))
      val inferredVal = true
    in
      G.VarBinder {names = [nameVal], typ = typVal, inferred = inferredVal}
    end

  fun tyvarToTerm (Ast.MarkTyv(tyvar,_) : Ast.tyvar) : G.term = tyvarToTerm tyvar
  | tyvarToTerm (Ast.Tyv tyvar) = G.IdentTerm (symbolToId tyvar)


  (* skipping records for now.. *)
  fun getConsType (Ast.MarkTy(ty, _) : Ast.ty) : G.term = getConsType ty
    | getConsType (Ast.TupleTy ty) = G.TupleTerm (List.map getConsType ty)
    | getConsType (Ast.ConTy (s, ty)) = 
      (case s of 
        [s'] => (case Symbol.number s' of (* Only works if length of ty = 2 *)
              0wx65B0 => let val SOME (hd, tl :: l) = List.getItem ty in
                            G.ArrowTerm (getConsType hd, getConsType tl) end
              | _ => (case ty of
                    [] => G.IdentTerm (symbolToId s')
                   | _ => raise Fail "Cannot convert."))
        | _ => raise Fail "More than one symbol!")
    | getConsType (Ast.VarTy tyvar) = tyvarToTerm tyvar



  fun getClause (id : G.ident) ((s, ty) : (Ast.symbol * Ast.ty option)) :
   G.clause =
    let val consId = symbolToId s
        val bind = []
        val consType = 
        case ty of
          NONE => SOME (G.IdentTerm id)
        | SOME ty => SOME (G.ArrowTerm(getConsType ty, G.IdentTerm id))
    in G.Clause(consId, bind, consType) end




	(* Sml declaration to Gallina sentence *)
    fun convertDec (Ast.MarkDec (d, _) : Ast.dec): G.sentence = convertDec d
      | convertDec (Ast.DatatypeDec {datatycs, withtycs}) = let
        	val dbGallina = G.Inductive (List.map convertDb datatycs)
        	(*val tbGallina = List.map convertTb withtycs (* ?? *)*)
      	in
        	G.InductiveSentence dbGallina
      	end
      | convertDec _ = raise Fail "Unimplemented case"		

	(* Sml sequence of declarations to Gallina sentences
	 * Note : This returns a sequence of sentences and not one sentence *)
	and convertDec' (Ast.SeqDec l: Ast.dec): G.sentences =
   G.SeqSentences (List.map convertDec l)

  (* Sml data bindings to Gallina inductive body
     This is the whole body of a datatype 
  	 db is an argument in: -and probably they all translate to indbody-
     DatatypeDec ( Datatype declarations )
     AbstypeDec ( Abstract type declarations -- advanced sml feature )
     DataSpec ( Datatype in signatures ) *)
    and convertDb (Ast.MarkDb (db, _)): G.indBody = convertDb db
    | convertDb (Ast.Db {tyc, tyvars, rhs,...}) = let
      val id = symbolToId tyc (* tree *)
      val binders = if tyvars = [] then [] else 
                  List.map tyvarToBinder tyvars
      val clauses = List.map (getClause id) rhs
      val typ = G.SortTerm (G.Set)
    in
      G.IndBody {id = id, bind = binders, typ = typ, clauses = clauses}
    end
		  
end