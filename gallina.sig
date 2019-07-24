signature GALLINA = 
sig
	type ident
	datatype term =
	ForallTerm of binder list * term (* forall *)
	| FunTerm of binder list * term (* fun *)
	| FixTerm of fixbody list (* fix *)
	| CofixTerm of fixbody list (* cofix *)
	(* let fun f x = 9 + x -> id = f , binders = [x]
	let val x : int = 9 -> id = x, binders = [] *)
	| LetTerm of {id : ident, binders : binder list, typ: term option, 
	body : term, inBody : term} (* let *)

	| LetFixTerm of fixbody * term (* let fix or let x := fix*)
	| LetCofixTerm of fixbody * term (* let cofix or let x := cofix*)
	| LetTupleTerm of { names : name list, retType : depRetType option, 
	body : term, inBody: term} (* let (a, b) :=  *)
	| LetPatternTerm of { pat : pattern, body : term, inBody : term} 
	(* let '' *)
	| IfTerm of {retType : depRetType, thenB : term, elseB : term}
	| HasTypeTerm of term * term
	| (* omitting check type <: *) 
	(* omitting tu support type :> *)
	ArrowTerm of term * term
	(* extra : denotes tuple types e.g. int * int *)
	| TupleTerm of term list 
	| ApplyTerm of term * arg list
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

  and sentence = AssumptionSentence of assumption
               | DefinitionSentence of definition
               | InductiveSentence of inductive
               | FixpointSentence of fixpoint
               | AssertionSentence of assertion * proof
               (* Gallina syntax extension *)
               | RecordSentence of recBody list
                (* extra seq of sentences *)
               | SeqSentences of sentence list

                          
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
	and definition = DefinitionDef of {localbool : bool, id : ident, 
	parameters : binder list, typ : term option, body : term}


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

	(* Since we're translating from sml datatype declaration,
	binder list will always be empty, and term option will have
	the type since a binder list needs a name for the identities
	e.g. datatype intList = Nil | Cons of int * intList
	the term option would be nat * intlist -> intlist *)
	and clause = Clause of ident * binder list * term option

	and fixpoint = Fixpoint of fixbody list | CoFixpoint of fixbody list

	and assertion = Assertion of assertionKeyword * ident * binder list * term

	and assertionKeyword = Theorem | Lemma | Remark | Fact
	    | Corollary | Proposition | Definition | Example   

	and proof = QedProof of string | DefProof of string | AdmitProof of string


end   
