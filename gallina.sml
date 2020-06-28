(* 

An Ast for the Gallina language

Some of the datatype and constructor names were inspired from:
https://github.com/antalsz/hs-to-coq/blob/fd1f53979746a862692ca1d60da303e1cf946363/src/lib/HsToCoq/Coq/Gallina.hs


*)

structure Gallina =
struct
  (* Lexical Conventions (Section 3.1.2):
   * We don't model lexical conventions, but we will add checks that 
   * ensure that all the constraints (i.e. keywords are not used, 
   * and identifiers are legal) are met *)
  type ident = string

  datatype axiom = PatternFailure

  datatype term =
    ForallTerm of binder list * term (* forall *)
  | FunTerm of binder list * term (* fun *)
  | FixTerm of fixbodies (* fix *)
  | CofixTerm of cofixbodies (* cofix *)
  (* let fun f x = 9 + x -> id = f , binders = [x]
     let val x : int = 9 -> id = x, binders = [] *)
  | LetTerm of {id : ident, binders : binder list, typ: term option, 
        body : term, inBody : term} 
  | LetFixTerm of fixbody * term (* let fix or let x := fix*)
  | LetCofixTerm of cofixbody * term (* let cofix or let x := cofix*)
  | LetTupleTerm of { names : name list, body : term, inBody: term} (* let (a, b) :=  *)
  | LetPatternTerm of { pat : pattern, inTerm: term option, body : term,
        inBody :  term} (* let '' *)
  | IfTerm of {test: term, thenTerm : term,  elseTerm : term}
  | HasTypeTerm of term * term
  | ArrowTerm of term * term
  | ApplyTerm of term * arg list (* CANNOT be empty *)
  | ExplicitTerm of ident* term list
  | InScopeTerm of term * ident
  | MatchTerm of {matchItems : matchItem list, body : equation list}
  | IdentTerm of ident
  | SortTerm of sort 
  | NumTerm of string 
  | WildcardTerm
  | ParensTerm of term
  | RecordTerm of fieldDef list
  (* Additional terms to match sml built-in types *)
  | WordTerm of string
  | RealTerm of string
  | StringTerm of string
  | CharTerm of string
  | HexTerm of string
    (* extra : denotes tuple types e.g. int * int *)
  | TupleTerm of term list 
  | ProductTerm of term list
  | ListTerm of term list
  | OrTerm of term * term
  | AndTerm of term * term
  | Axiom of axiom
  | MatchNotationTerm of {matchItem : matchItem, body : equation, exhaustive: bool}
  | UnitTerm

and arg = Arg of term | NamedArg of ident * term

and binder = 
  SingleBinder of {name : name, typ : term option, inferred : bool}   
  | LetBinder of {names : name list, typ : term option, body : term}
  | PatternBinder of pattern
  
and name = Name of ident | WildcardName

and sort = Prop | Set | Type

and fieldDef = FieldDef of {id : ident, binders : binder list, term : term}

and fixbodies = Fixbodies of fixbody list * ident

and cofixbodies = CoFixbodies of cofixbody list * ident

and fixbody =   Fixbody of 
  {id : ident, binders : binder list,
      decArg : annotation option, typ : term option, body : term}

and cofixbody =   Cofixbody of 
  {id : ident, binders : binder list, typ : term option, body : term}     


and annotation = Annotation of ident

and matchItem = MatchItem of term

and depRetType = DepRet of name option * retType

and retType = Ret of term

and equation = Equation of pattern * term

and pattern =   ArgsPat of ident * pattern list (* true for explicit*)
              | AtArgsPat of ident * pattern list
              | AsPat of pattern * ident
              | ScopePat of pattern * ident
              | QualidPat of ident
              | WildcardPat
              | NumPat of string
              | RecPat of fieldPat list
              (* Eliminating orpat *)
              (*| OrPat of orPattern list*)
              (* Additional Patternss *)
              | WordPat of string
              | RealPat of string
              | StringPat of string
              | CharPat of string
              | HexPat of string
                (* extra *)
              | TuplePat of pattern list
              | ListPat of pattern list 
              | ParPat of pattern
              | UnitPat

  and orPattern = OrPattern of pattern list

  and fieldPat = FieldPat of {id : ident, binders : binder list, pat : pattern}

(* The vernacular - the language of commands of Gallina *)		 
  and sentence = DefinitionSentence of definition
               | InductiveSentence of inductive
               | FixpointSentence of fixpoint
               (* Gallina syntax extension *)
               | RecordSentence of recBody list
                (* extra seq of sentences *)
               | SeqSentences of sentence list

  (* Gallina syntax extension *)             
  and recBody = RecordBody of 
      {id : ident, binders : binder list, typ : sort option, 
       consName : ident option, body : field list}

 (* Gallina syntax extension *)
  and field = Field of (ident * term) list                


  (* localbool = true if [local] Definition *)
  (* def2 is NONE when category is 1 *)
  and definition = DefinitionDef of {localbool : bool, id : ident, 
              binders : binder list, typ : term option, body : term}
              | LetDefinitionDef of {id : ident, binders : binder list, typ : term option, body : term} 

  and inductive = Inductive of indBody list | CoInductive of indBody list

  (**
    ident : name of inductive type
    binder list : type binders for the type (e.g. list (T: Set))
    term : type's type
    clauses : each constructor of the type
    *)
  and indBody = 
    IndBody of {id : ident, bind : binder list, 
                            typ : term, clauses : clause list}

  (* Since we're translating from sml datatype declaration,
      binder list will always be empty, and term option will have
      the type since a binder list needs a name for the identities
      e.g. datatype intList = Nil | Cons of int * intList
      the term option would be nat * intlist -> intlist *)
  and clause = Clause of ident * binder list * term option

  and fixpoint = Fixpoint of fixbody list | CoFixpoint of fixbody list

  (* category is the category of the definition, where: 
  One : Simple declarations with one definition and no pattern-matching
  Two : Declarations with more than one definition that donot require the 
        patternFailure axiom because the datatype being matched on has only 
        one constructor
  Three : Declarations with more than one definition that require the patternFailure axiom
  *)

end   
