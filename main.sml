Control.Print.printLength := 1000;
Control.Print.printDepth := 100;

structure Main = 
struct

  fun getAST (filename: string) = 
    let
      val f = TextIO.openIn (filename)
      val source = Source.newSource (filename, f, true, ErrorMsg.defaultConsumer())
    in
      SmlFile.parse source
    end

  fun decToGallinaAST (SeqDec l: AST.dec): Gallina.AST = SeqSentences (List.map toGallinaAST l)
    | decToGallinaAST (MarkDec (d, _)) = toGallinaAST d
    | dectToGallinaAST (DatatypeDec {datatycs, withtycs}) = let
        val dbGallina = List.map dbToGallinaAST datatycs
        val tbGallina = List.map tbToGallinaAST withtycs (* ?? *)
      in
        Inductive dbGallina
      end
    | _ = raise Fail "Unimplemented case"
  and dbToGallinaAST (MarkDb (db, _)): GallinaAST.indBody = dbToGallinaAST db
    | dbToGallinaAST (Db {tyc : symbol, 
                          tyvars : tyvar list,
		          rhs : (symbol * ty option) list, 
                          _}) = let
      val id = getId tyc (* tree *)
      val binders = getBinders tyvars (* 'a --> BinderC (a, Set) *)
      val clauses = getClauses rhs
    in
      IndBody (id, binders, Type/Set?, clauses)
    end
  and tbToGallinaAST _ = ?

end
