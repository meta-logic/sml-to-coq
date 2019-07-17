structure GallinaAST =
struct

  datatype ? = SeqSentences of sentence list(*?*)
  and sentence = Assumption
               | Definition
               | InductiveiSentence of inductive
               | Fixpoint
               | Assertion Proof
  and inductive = Inductive of indBody list
  (**
    ident : name of inductive type
    binder list : type parameters for the type (e.g. list (T: Set))
    term : type's type
    clause list : each constructor of the type
    *)
  and indBody = IndBody of ident * binder list option * term * clause list
  (**
    ident : constructor name (e.g. Node)
    binder list : named/patterned substructures for that constructor (e.g. Node (tl: tree) (tr: tree))
    term : constructor's type (e.g. Node : tree * tree -> tree)
    *)
  and clause = Clause of ident * binder list option * term option

end
