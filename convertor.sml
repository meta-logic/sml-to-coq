(* Converts an Sml AST to a Gallina AST *)

structure Convertor : CONVERTOR =
struct
	structure G = Gallina
	
	(* Sml symbol to Gallina ident
	   Takes care of Sml identifiers that start with '
	   Doesn't take care of Gallina reserved words *)
	fun getId (s : Ast.symbol) : G.ident = 
		let val s = Symbol.name s in
		if String.isPrefix "'" s
		then "_" ^ String.extract(s,1,None) else s end
	
	(* Sml sequence of declarations to Gallina sentences
	 * Note : This returns a sequence of sentences and not one sentence *)
	fun convertDec' (Ast.SeqDec l: Ast.dec): G.sententences = G.SeqSentences 
		(List.map convertDec l)

	(* Sml declaration to Gallina sentence *)
    fun convertDec (Ast.MarkDec (d, _) : Ast.dec): G.sententence = convertDec d
      | convertDec (Ast.DatatypeDec {datatycs, withtycs}) = let
        	val dbGallina = List.map convertDb datatycs
        	val tbGallina = List.map convertTb withtycs (* ?? *)
      	in
        	G.InductiveSentence dbGallina
      	end
      | convertDec _ = raise Fail "Unimplemented case"		


  (* Sml data bindings to Gallina inductive body
     This is the whole body of a datatype 
  	 db is an argument in: -and probably they all translate to indbody-
     DatatypeDec ( Datatype declarations )
     AbstypeDec ( Abstract type declarations -- advanced sml feature )
     DataSpec ( Datatype in signatures ) *)
    and convertDb (Ast.MarkDb (db, _)): G.indBody = convertDb db
    | convertDb (Ast.Db {tyc, tyvars, rhs,...}) = let
      val id = getId tyc (* tree *)
      val binders = getBinders tyvars (* 'a --> BinderC (a, Set) *)
      val clauses = getClauses rhs
    in
      IndBody {id = id, bind = binders, G.Set, clauses}
    end
		  
