(* 

An Ast for the Gallina language

The Gallina Specificationn Language can be found at:
https://coq.inria.fr/distrib/current/refman/language/gallina-specification-language.html

Some if the datatype and constructor names were inspired from:
https://github.com/antalsz/hs-to-coq/blob/fd1f53979746a862692ca1d60da303e1cf946363/src/lib/HsToCoq/Coq/Gallina.hs
*)

structure GallinaAST =
struct
  type ident = string

  datatype term =
    ForallTerm of binder list * term
  | FunTerm of binder list * term
  | FixTerm of fixbody list
  | CofixTerm of fixbody list
  (* let fun f x = 9 + x -> id = f , binders = [x]
     let val x : int = 9 -> id = x, binders = [] *)
  | LetTerm of {id : ident, binders : binder list, typ: term option, 
        body : term, inBody : term}

  | LetFixTerm of fixbody * term
  | LetCofixTerm of fixbody * term
  | LetTupleTerm of { names : name list, retType : depRetType option, 
        body : term, inBody: term}
  | LetPatternTerm of { pat : pattern, body : term, inBody : term}
  | IfTerm of {retType : depRetType, thenB : term, elseB : term}
  | HasTypeTerm of term * term
  | (* omitting check type <: *) 
    (* omitting tu support type :> *)
    ArrowTerm of term * term
  | ApplyTerm of arg list
  | ExplicitTerm of ident
  | InScopeTerm of term * ident
  | MatchTerm of {variables : matchItem list, retType : retType option, 
                body : equation list}
  | IdentTerm of ident
  | SortTerm of sort 
  | NumTerm of int 
  | WildcardTerm
  | ParensTerm of term

and arg = Arg of term | TypedArg of ident * term
and binder = 
  (* name ... name or { name ... name}
    or name ... name : type or {name ... name : type} *) 
    VarBinder of {names : name list, typ : term option, inferred : bool}  
  (* name ... name : type *)
  | LetBinder of {names : name list, typ : term option, body : term}
  | PatternBinder of pattern
  
and name = Name of ident | WildcardName

and sort = Prop | Set | Type
 

and fixbody =   Fixbody of 
  {id : ident, parameters : binder list,
      decArg : annotation option, retType : term option, body : term}

and annotation = Annotation of ident

and matchItem = MatchItem of {matchItem : ident, asItem : name, inItem : ident
                                option, patterns : pattern option}

and depRetType = DepRet of name option * retType

and retType = Ret of term

and equation = Equation of multPattern list * term

and multPattern = MultPat of pattern list

and pattern =   ArgsPat of ident * pattern list * bool (* true for explicit*)
              | AsPat of ident
              | ScopePat of ident
              | QualidPat of ident
              | WildcardPat
              | NumPat of int
              | StringPat of string
              | OrPat of orPattern list

and orPattern = OrPattern of pattern list



(* The vernacular - the language of commands of Gallina *)		 
  datatype sentences = SeqSentences of sentence list(*?*)


  and sentence = AssumptionSentence of assumption
               | DefinitionSentence of definition
               | InductiveSentence of inductive
               | FixpointSentence of fixpoint
               | AssertionSentence of assertion * proof
               (* Gallina syntax extension *)
               | RecordSentence of recBody list
  (* Gallina syntax extension *)             
  and recBody = RecordBody of 
      {id : ident, parameters : binder list, typ : sort option, 
       consName : ident option, body : field list}

 (* Gallina syntax extension *)
  and field = Field of (ident * term) list                

  and assumption = Assumption of assumptionKeyword * assums

  and assumptionKeyword = Axiom | Conjecture | Parameter | Parameters
                        | Variable | Variables | Hypothesis | Hypotheses       

  and assums = Assumptions of (ident list * term) list

  (* localbool = true if [local] Definition *)
  and definition = Definition of {localbool : bool, id : ident, 
              parameters : binder list, type : term option, body : term}


  and inductive = Inductive of indBody list | CoInductive of indBody list

  (**
    ident : name of inductive type
    binder list : type parameters for the type (e.g. list (T: Set))
    term : type's type
    clauses : each constructor of the type
    *)
  and indBody = 
    IndBody of {id : ident, bind : binder list, 
                            typ : term, clauses : clause list}

  and clause = Clause of ident * binder list * term option

  and fixpoint = Fixpoint of fixbody list | CoFixpoint of fixbody list

  and assertion = Assertion of assertionKeyword * ident * binder list * term

  and assertionKeyword = Theorem | Lemma | Remark | Fact
                        | Corollary | Proposition | Definition | Example   

  and proof = QedProof of string | DefProof of string | AdmitProof of string


end   
