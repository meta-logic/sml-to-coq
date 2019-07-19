structure GallinaAST =
struct
  type ident = string

  (* Nonde denotes the wildcard "_" *)

  datatype term =
  TermForall of binder list * term
  | TermFun of binder list * term
  | TermFix of fixbody list
  | TermCofix of fixbody list
  (* let fun f x = 9 + x -> id = f , binders = [x]
     let val x : int = 9 -> id = x, binders = [] *)
  | TermLet of {id : ident, binders : binder list, typ: term option, 
        body : term, inBody : term}

  | TermLetFix of fixbody * term
  | TermLetCofix of fixbody * term
  | TermLetTuple of { names : name list, retType : depRetType option, 
        body : term, inBody: term}
  | TermLetPattern of { pat : pattern, body : term, inBody : term}
  | TermIf of {retType : depRetType, thenB : term, elseB : term}
  | TermHasType of term * term
  | (* omitting check type <: *) 
    (* omitting tu support type :> *)
    TermArrow of term * term
  | TermApply of arg list
  | TermExplicit of ident
  | TermInScope of term * ident
  | TermMatch of {variables : matchItem list, retType : retType option, 
                body : equation list}
  | TermIdent of ident
  | TermSort of sort 
  | TermNum of int 
  | TermWildcard
  | TermParens of term

and arg = Arg of term | ArgTyped of ident * term
and binder = 
  (* name ... name or { name ... name}
    or name ... name : type or {name ... name : type} *) 
  BinderVar of {names : name list, typ : term option, inferred : bool}  
  (* name ... name : type *)
  | BinderLet of {names : name list, typ : term option, body : term}
  | BinderPattern of pattern
  
and name = Name of ident | NameWild

and sort = Prop | Set | Type
 

and fixbody =   Fixbody of {id : ident, parameters : binder list option,
                            decArg : annotation option, retType : term option, 
                            body : term}

and annotation = Annotation of ident

and matchItem = MatchItem of {matchItem : ident, asItem : name, inItem : ident
  option, patterns : pattern option}

and depRetType = DepRet of name option * retType

and retType = Ret of term

and equation = Equation of multPattern list * term

and multPattern = MultPat of pattern list

and pattern = PatArgs of ident * pattern list * bool (* true for explicit*)
              | PatAs of ident
              | PatScope of ident
              | PatQualid of ident
              | PatWild
              | PatNum of int
              | PatString of string
              | PatOr of orPattern list

and orPattern = OrPattern of pattern list




		 
  datatype sentences = SeqSentences of sentence list(*?*)
  and sentence = AssumptionSentence
               | DefinitionSentence
               | InductiveSentence of inductive
               | FixpointSentence
               | AssertionSentence Proof
  and inductive = Inductive of indBody list
  (**
    ident : name of inductive type
    binder list : type parameters for the type (e.g. list (T: Set))
    term : type's type
    clauses : each constructor of the type
    *)
  and indBody = IndBody of {id : ident, bind : binder list option, 
                            typ : term, clauses : clause list}
  (**
    ident : constructor name (e.g. Node)
    binder list : named/patterned substructures for that constructor (e.g. Node (tl: tree) (tr: tree))
    term : constructor's type (e.g. Node : tree * tree -> tree)
    *)
  and clause = Clause of ident * binder list option * term option

end   
