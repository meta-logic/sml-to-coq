structure Generator = 
struct
    structure G = Gallina;
    structure C = Convertor;
    structure S = String;


  (* concatListWith: string * 'a -> string * 'a list -> string
   * ENSURES: concatListWith(p, f, l) =  (S.concatWith p (List.map f l))
   *)
  fun concatListWith (p, f, l) = (S.concatWith p (List.map f l))


  (* writeFile: string -> unit
   * ENSURES: create a file with the name filename
   *)
  fun writeFile filename content =
    let 
      val fd = TextIO.openOut filename
      val _  = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
      val _  = TextIO.closeOut fd
    in 
      () 
    end


  (* generate: string -> unit
   * ENSURES: generate(source) = generate a file witht the generated Gallina code
   *)
  fun generate(source: string, output: string ): unit =
    let
      
      val ast        = C.convert source
      val codeList   = sentenceG(ast)
      val imports    = ["Require Import intSml.",
                        "Require Import listSml.",
                        "Require Import realSml.",
                        "Require Import stringSml.",
                        "Require Import charSml.",
                        "Require Import boolSml.",
                        "Require Import optionSml.",
                        "Require Import listPairSml.",
                        "Require Import notationsSml.", 
                        "From Equations Require Import Equations."]
      val settings = ["\nGeneralizable All Variables."]
      val codeList = imports @ settings @ codeList 
    in
      writeFile output ((S.concatWith ("\n") codeList)^ "\n") 
    end


  and genAllExamples () = List.map (
    fn name => generate("examples/" ^ name ^ ".sml", "examples2/" ^ name ^ ".v")
    ) ["decl_pat",
       "filter",
       (*"functor",*) (* Don't compile for some reason*)
       "id",
       "mutual_rec",
       "non_terminating",
       "partial",
       (*"records",*) (* Don't compile for some reason*)
       "terminating",
       "trees",
       "theorem_generation"
      ]


  (*--------------------------------------------------------------------------*)
  (* This part uses Gallina's Grammar to Generate Gallina's code from the AST *)
  (* -------------------------------------------------------------------------*)
  

  and termG (term: G.term): string =
    case term of                               
      G.FunTerm(bL,t)    => "fun "^(concatListWith (" ", binderG, bL))^" => "^termG(t)
    | G.FixTerm(fb)      => "fix "^ fixbodiesG(fb)
    | G.CofixTerm(fb)    => "cofix "^ cofixbodiesG(fb)
    | G.LetTerm{id=i, binders=bL, typ=tO, body=bT, inBody=inT} =>
      
      "\n" ^ "  let " ^ i ^ (concatListWith (" ", binderG, bL)) ^
      (case tO of NONE => "" | SOME t => " : "^termG(t))^
      " := " ^ termG(bT) ^ " in " ^ termG(inT)

    | G.LetFixTerm(fb, t)   => "\n"^"  let fix "^fixbodyG(fb)^" in "^termG(t)
    | G.LetCofixTerm(cb, t) => "\n"^"  let cofix "^coFixbodyG(cb)^" in "^termG(t)
    | G.LetTupleTerm{names=nL, body=bT, inBody=inT} =>
      
      "\n" ^ " let " ^ "(" ^ (concatListWith (", ", nameG, nL)) ^ ")" ^
      " := " ^ termG(bT) ^ " in " ^ termG(inT)
    
    | G.LetPatternTerm{pat=patt, inTerm=tO, body=bT, inBody=inT} => 
      
      "\n"^" let "^" ' "^ patternG(patt)^
      (case tO of NONE => "" | SOME t => " in "^termG(t))^
      " := " ^ termG(bT) ^ " in " ^ termG(inT)
    
    | G.IfTerm{test=tes, thenTerm=the,  elseTerm=els} => 
      "if "^termG(tes)^" then "^termG(the)^" else "^termG(els)
    
    | G.HasTypeTerm(v1,v2)  => "(" ^ termG(v1) ^ " : " ^ termG(v2) ^ ")"  (*Could be added to Gallina's AST without being in SML's AST*)
    | G.ArrowTerm(v1,v2)    => termG(v1) ^ " -> " ^ termG(v2)
    | G.ApplyTerm(v1,aL)    => termG(v1) ^" "^(concatListWith (" ", argG, aL))
    | G.ExplicitTerm(v1,tL) => "@" ^ v1 ^" "^(concatListWith (" ", termG, tL))
    | G.InScopeTerm(v1,v2)  => termG(v1) ^ "%" ^ v2 
    | G.MatchTerm{matchItems=mL, body=eL} => 
      
      "\n  match " ^ (concatListWith (", ", matchItemG, mL)) ^ " with" ^ "\n" ^
      "  | " ^ (S.concatWith ("  \n  | ") (List.map equationG eL)) ^ "\n  end"
    
    | G.IdentTerm(v)        => convertIdent(v)
    | G.IdentTypTerm(v)     => convertType(v)
    | G.SortTerm(v)         => sortG(v) 
    | G.NumTerm(v)          => (if (S.isPrefix "~" v) 
                                then "(-"^S.substring(v, 1, S.size(v)-1)^ ")" 
                                else v)
    
    | G.WildcardTerm        => "_"      
    | G.ParensTerm(v)       =>  "(" ^ termG(v) ^ ")"
    | G.RecordTerm(fL)      => "\n{|\n  "^concatListWith(";\n  ", fieldDefG, fL)^"\n|}"
    
    (*Additional terms to match sml built-in types. (!) *)  
    | G.WordTerm(v, b)      => (case b of 
                                  G.Dec => termG(G.NumTerm(v))
                                | G.Hex => termG(G.HexTerm(v)))

    | G.RealTerm(v)         => (if (S.isPrefix "~" v) 
                                then "(-"^S.substring(v, 1, S.size(v)-1)^ ")%float" 
                                else v ^ "%float")
    | G.StringTerm(v)       => "\"" ^ v ^ "\"" 
    | G.CharTerm(v)         => (convertChar v) 
    | G.HexTerm(v)          => "\"" ^ "0x"^ S.map Char.toLower v ^ "\""
    (* extra : denotes tuple types e.g. int * int. (!) *)
    | G.TupleTerm(tL)       => "(" ^ (concatListWith (", ", termG, tL)) ^ ")"
    | G.ProductTerm (tL)    => "(" ^ (concatListWith (" * ", termG, tL)) ^ ")"
    | G.ListTerm(tL)        => "[" ^ (concatListWith ("; ", termG, tL)) ^ "]" 
    | G.OrTerm(v1, v2)      => termG(v1) ^ " || "  ^ termG(v2) 
    | G.AndTerm(v1, v2)     => termG(v1) ^ " && "  ^ termG(v2)
    | G.Axiom(a)            => "patternFailure"
    | G.MatchNotationTerm{matchItem=mI, body=e, exhaustive=b} => 
      
      "\n  match " ^ matchItemG(mI) ^ " with" ^ "\n  " ^ equationG(e) ^
      (case b of  true => "" | false => "\n  | _ => patternFailure" )^"\n  end"

    | G.UnitTerm            => "tt"
    | G.InfixTerm(t, aL)    =>  let
                                  val G.Arg(t') = List.hd aL
                                  val G.TupleTerm(tL) = t'
                                in
                                  concatListWith (" " ^ termG(t) ^ " ", termG, tL) 
                                end
    (* Adding proposition terms for preconditions *)
    | G.DisjunctTerm(t1, t2) => termG(t1) ^ " \\/ " ^ termG(t2)
    | G.ConjunctTerm(t1, t2) => termG(t1) ^ " /\\ " ^ termG(t2)
    | G.ForallTerm(bL, t)    => "forall "^(concatListWith (" ", binderG, bL))^ ", " ^ termG(t)
    | G.ExistsTerm(bL, t)    => "exists "^(concatListWith (" ", binderG, bL))^" , " ^termG(t) 
    | G.EqualTerm(t1, t2)    => "eq (" ^ termG(t1) ^ ") (" ^ termG(t2) ^ ")"
    | G.DefTerm(id, bL, iO, b)   => 
      case iO of
        SOME h => "@" ^ id ^ " " ^ concatListWith(" ", patternG, bL) ^ " " ^ h ^ " = " ^ patternG(b)
      | NONE   => id ^ " " ^ concatListWith(" ", patternG, bL) ^ " = " ^ patternG(b)


  and argG (G.Arg(t))        = "(" ^ termG(t) ^ ")"
    | argG (G.NamedArg(v,t)) = "(" ^ v ^ " := " ^ termG(t) ^ ")"


  and binderG (G.SingleBinder{name=n, typ=tO, inferred=inf}) = 
      (case inf of false => 
      " " ^ nameG(n) ^ (case tO of NONE => "" | SOME x =>" : "^termG(x))
      | true => 
      " {" ^ nameG(n) ^(case tO of NONE => "" | SOME x =>" : "^termG(x))^ "}")  
    
    | binderG (G.MultipleBinders{names=nL, typ=t, inferred=inf}) = 
      (case inf of false => 
      " (" ^ (concatListWith (" ", nameG, nL)) ^ " : " ^ termG(t) ^ ")"
      | true => 
      " {" ^ (concatListWith (" ", nameG, nL)) ^ " : " ^ termG(t) ^ "}") 

    | binderG (G.LetBinder{names=nL, typ=tO, body=bT})       = 
      "(" ^ (concatListWith (" ", nameG, nL)) ^ 
      (case tO of NONE => "" | SOME x =>" : "^termG(x))^" := " ^ termG(bT) ^ ")"
    
    | binderG (G.PatternBinder(p)) ="' " ^ patternG(p)         


  and nameG (G.Name(n))      = n 
    | nameG (G.WildcardName) = "_"


  and sortG (G.Prop) = "Prop"
    | sortG (G.Set)  = "Set"
    | sortG (G.Type) = "Type"

  and fieldDefG(G.FieldDef{id=i, binders=bL, term=t}) =
    i^" " ^ concatListWith (" ", binderG, bL) ^ " := " ^ termG(t)

  
  and fixbodiesG (G.Fixbodies(fL, i)) = 
      (concatListWith ("\nwith ", fixbodyG, fL)) ^ " for " ^ i


  and cofixbodiesG (G.CoFixbodies(cL, i)) = 
      (S.concatWith ("\nwith ") (List.map coFixbodyG cL)) ^ " for " ^ i


  and fixbodyG (G.Fixbody{id=i, binders=bL, decArg=aO, typ=tO, body=t}) = 
      convertIdent(i) ^ " " ^(concatListWith (" ", binderG, bL)) ^ " " ^ 
      (case aO of NONE => "" | SOME a => annotationG(a)^" ") ^ 
      (case tO of NONE => "" | SOME t => " : " ^ termG(t)^" ") ^ ":= " ^ termG(t)


  and coFixbodyG (G.Cofixbody {id=i, binders=bL, typ=tO, body=t}) = 
      convertIdent(i) ^ " " ^(concatListWith (" ", binderG, bL)) ^ " " ^
      (case tO of NONE => "" | SOME x => termG(x)^" ") ^ ":= " ^ termG(t)      


  and annotationG (G.Annotation(i)) = "{ struct " ^ i ^ " }"


  and matchItemG (G.MatchItem (t))  = termG(t) 


  and depRetTypeG (G.DepRet(nO,r))   = 
    (case nO of NONE => "" | SOME x => "as " ^ nameG(x)) ^ retTypeG(r)


  and retTypeG (G.Ret(t)) = "return " ^ termG(t)


  and equationG (G.Equation(p, t))  = patternG(p) ^ " => " ^ termG(t)


  and patternG (pattern: G.pattern): string =
    case pattern of
      G.ArgsPat(i, pL)   => "(" ^ (convertIdent i) ^ " " ^ concatListWith (" ", patternG, pL) ^ ")"
    | G.AtArgsPat(i, pL) => "@" ^ (convertIdent i) ^ " " ^ concatListWith (" ", patternG, pL)
    | G.AsPat(p, i)      => patternG(p) ^ " as " ^ i
    | G.ScopePat(p, i)   => patternG(p) ^ " % " ^ i 
    | G.QualidPat(i)     => convertIdent(i)
    | G.WildcardPat      => "_"
    | G.NumPat(s)        => (if (S.isPrefix "~" s) then "-"^S.substring(s, 1, S.size(s)-1) else s)
    | G.RecPat(fL)       => "\n{|\n  "^concatListWith(";\n  ", fieldPatG, fL)^"\n|}"
    | G.WordPat(s, b)    => (case b of 
                               G.Dec => patternG(G.NumPat(s))
                             | G.Hex => patternG(G.HexPat(s)))
    | G.RealPat(s)       => (if (S.isPrefix "~" s) 
                             then "(-"^S.substring(s, 1, S.size(s)-1)^ ")%float" 
                             else s ^ "%float")
    | G.StringPat(s)     => "\"" ^ s ^ "\""
    | G.CharPat(s)       => (convertChar s)
    | G.HexPat(s)        => "\"" ^ "0x"^ S.map Char.toLower s ^ "\"" 
      (* extra *)  
    | G.TuplePat(pL)     => "(" ^ concatListWith (", ", patternG, pL) ^ ")"
    | G.ListPat(pL)      => "[" ^ concatListWith ("; ", patternG, pL) ^ "]" 
    | G.ParPat(p)        => patternG(p)
    | G.UnitPat          => "tt"
    | G.InfixPat(i, pL)  => let
                              val G.TuplePat(pL') = List.hd pL
                            in
                              "(" ^ concatListWith (" " ^ i ^ " ", patternG, pL') ^ ")" 
                            end


  and orPatternG (G.OrPattern(pL)) = concatListWith("| ", patternG, pL)


  and fieldPatG(G.FieldPat{id=i, binders=bL, pat=p}) =
    convertIdent(i)^" " ^ concatListWith(" ", binderG, bL) ^" := " ^ patternG(p)


  and sentenceG (sentence: G.sentence list): string list =
    case sentence of 
      nil    => nil
    | x::ast => case x of
                  G.DefinitionSentence(d)      => definitionG(d)::sentenceG(ast) 
                | G.InductiveSentence(i)       => inductiveG(i)::sentenceG(ast)
                | G.FixpointSentence(f)        => fixpointG(f)::sentenceG(ast) 
                | G.AssumptionSentence(a)      => assumptionG(a)::sentenceG(ast)
                | G.RecordSentence(r)          => recordG(r)::sentenceG(ast)
                | G.ModuleSentence(m)          => moduleG(m)::sentenceG(ast)
                | G.SignatureSentence(g)       => gsignatureG(g)::sentenceG(ast)
                | G.DeclareModuleSentence(d)   => declarationG(d)::sentenceG(ast)
                | G.IncludeSentence(i)         => inclusionG(i)::sentenceG(ast)
                | G.SeqSentences(n)            => sentenceG(n)@sentenceG(ast)
                | G.EquationSentence(e)        => eprogramsG(e)::sentenceG(ast)
                | G.ProofObligationSentence(p) => proofObligationG(p)::sentenceG(ast)


  and recordG (rL) = "\nRecord " ^ concatListWith("with ", recBodyG, rL)


  and recBodyG (G.RecordBody{id=i, binders=bL, typ=sO, consName=iO, body=fL}) =
    convertIdent(i) ^ " " ^ concatListWith(" ", binderG, bL) ^ 
    (case sO of NONE => "" | SOME x => sortG(x)) ^ 
    " := " ^ (case iO of NONE => "" | SOME x => x) ^ 
    "\n{\n  " ^ concatListWith(";\n  ", fieldG, fL) ^ "\n}" ^ "." 


  and fieldG (G.Field(itL)) = 
    concatListWith(";\n  ", (fn (i,t)=> i ^ " : " ^ termG(t)), itL)
    

  and definitionG (def: G.definition): string  =
    case def of
      G.DefinitionDef{binders=bL, body=term ,id=i, localbool=loc ,typ=ty}    =>
      "\n" ^ (if loc then "Local" else "") ^ "Definition " ^ 
      convertIdent(i) ^ concatListWith(" ", binderG, bL) ^ 
      (case ty of NONE => "" | SOME x => " : " ^ termG(x)) ^
       " := " ^ termG(term) ^ "."

    | G.LetDefinitionDef{binders=bL, body=term ,id=i, typ=ty} =>
      "Let " ^ convertIdent(i) ^ concatListWith(" ", binderG, bL) ^ 
      (case ty of NONE => "" | SOME x => " : " ^ termG(x)) ^
       " := " ^ termG(term) ^ "."


  and inductiveG (ind: G.inductive): string  = 
    case ind of
      G.Inductive(inbL)   => "\nInductive "   ^ concatListWith("\nwith ", indBodyG, inbL)^"."
    | G.CoInductive(inbL) => "\nCoInductive " ^ concatListWith("\nwith ", indBodyG, inbL)^"."
  

  and indBodyG (G.IndBody{id=i, bind=bL, typ=t, clauses=cL}) =
      convertIdent(i) ^ " " ^ concatListWith(" ", binderG, bL) ^ " : " ^ termG(t) ^
      " := " ^ "\n  | " ^ concatListWith("  \n  | ", clauseG, cL)


  and clauseG (G.Clause(i, bL, tO)) = 
    i ^ concatListWith(" ", binderG, bL) ^ 
    (case tO of NONE => "" | SOME x => " : " ^ termG(x))


  and fixpointG (fp: G.fixpoint): string =
    case fp of
      G.Fixpoint(fL)   => "\nFixpoint "   ^ concatListWith("\nwith ", fixbodyG, fL)^"."
    | G.CoFixpoint(fL) => "\nCoFixpoint " ^ concatListWith("\nwith ", coFixbodyG, fL)^"."  


  and assumptionG (G.Assumption(ak, i, t)) = 
    assumKeywordG(ak) ^ " " ^ convertIdent(i) ^ " : " ^ termG(t) ^ "." 


  and assumKeywordG (a: G.assumKeyword) = 
    case a of 
      G.Conjecture => "\nConjecture"
    | G.Parameter  => "\nParameter"
    | G.Parameters => "\nParameters"
    | G.Variable   => "\nVariable"
    | G.Variables  => "\nVariables"


  and moduleG (m: G.module): string =
    case m of
      G.IModule{id=i, typ=oo, bindings=ml, body=mB} => let
          val id = convertIdent i
          val modBinds = concatListWith("\n", moduleBindingsG, ml)
          val binds = case modBinds of "" => ""
                                     | _  => " " ^ modBinds
          val modType = case oo of NONE => "" 
                                 | SOME x => " " ^ (ofModuleTypG x)
          val modBody = moduleBodyG mB
        in
          "\nModule " ^ id ^ binds ^ modType ^ ".\n" ^
          modBody ^ 
          "\nEnd " ^ id ^ "."
        end
    | G.Module{id=i, typ=oo, bindings=ml, body=mE} => let
          val id = convertIdent i
          val modBinds = concatListWith("\n", moduleBindingsG, ml)
          val binds = case modBinds of "" => ""
                                     | _  => " " ^ modBinds
          val modType = case oo of NONE => "" 
                                 | SOME x => " " ^ (ofModuleTypG x)
          val modExp = moduleExpressionG mE
        in
          "\nModule " ^ id ^ binds ^ modType ^ " := " ^ modExp ^ "."
        end


  and moduleBodyG (G.ModuleBody(sL)): string = 
    concatListWith("\n", fn x => x , sentenceG(sL))


  and moduleExpressionG (m: G.moduleExpression): string =
    case m of
      G.ModuleName(i)   => i
    | G.FunctorName(id1, id2) => "!" ^ id1 ^ " " ^ id2


  and ofModuleTypG (m: G.ofModuleTyp): string =
    case m of
      G.TransparentSig(m') => "<: " ^ moduleTypG(m')
    | G.OpaqueSig(m')      => ": " ^ moduleTypG(m')


  and moduleTypG (m: G.moduleTyp): string = 
    case m of
      G.SigName(i) => i ^ ""
    | G.SigParens(mT) => "( " ^ moduleTypG(mT) ^ " )"
    | G.SigType(mT, w) => moduleTypG(mT) ^ " " ^ withDeclG(w)


  and withDeclG (G.WithTyp(d)): string = 
    let 
      val defWithPeriod = definitionG d
      val len = S.size defWithPeriod
      val def = S.substring (defWithPeriod, 0, len-1)
    in
      "with " ^ def
    end


  and moduleBindingsG(G.ModuleBinding(iO, iL, mT)): string =
    "( " ^ (case iO of NONE => "" | SOME i => importG(i)^" ") ^ 
    concatListWith(" ",fn x => x, iL) ^" : " ^ moduleTypG(mT) ^ " )"


  and importG (i: G.import): string = 
    case i of
      G.Import => "Import"
    | G.Export => "Export"
  
  
  and gsignatureG (g: G.gsignature): string =
    case g of
      G.ISignature{id=i, bindings=ml, body=s} => let
          val id = convertIdent i
          val modBinds = concatListWith("\n", moduleBindingsG, ml) 
          val binds = case modBinds of "" => ".\n" 
                                     | _  => " " ^ modBinds ^ ".\n"
          val sigBody = signatureBodyG s
        in
          "\nModule Type " ^ id ^ binds ^
          sigBody ^ 
          "\nEnd " ^ id ^ "."
        end
    | G.Signature{id=i, bindings=ml, body=m} => let
          val id = convertIdent i
          val modBinds = concatListWith("\n", moduleBindingsG, ml) 
          val binds = case modBinds of "" => "" 
                                     | _  => "(" ^ modBinds ^ ")"
          val modType = moduleTypG m
        in
          "\nModule Type " ^ id ^ binds ^ " := " ^ modType ^ "."
        end

  and signatureBodyG (G.SigBody(sL)): string = 
    concatListWith("\n", fn x => x , sentenceG(sL))


  and declarationG (G.Declare {id=i, bindings=ml, typ=mT}): string = 
    "\nDeclare Module " ^ convertIdent(i) ^ " " ^
    concatListWith("\n", moduleBindingsG, ml) ^ " : " ^ moduleTypG(mT) ^ "."


  and inclusionG (G.Include (m)): string = "Include " ^ moduleTypG(m) ^ "."


  and ebinderG (b: G.ebinder): string = 
    case b of
      G.ESingleBinder{name = n, typ = t, inferred = inf} => 
        (case inf of 
            false => "(" ^ nameG(n) ^ ": " ^ termG(t) ^ ")"
          | true => "{" ^ nameG(n) ^ ": " ^ termG(t) ^ "}") 
    | G.ELetBinder{names = nL, typ = t, body = b} => 
        "(" ^ concatListWith(" ", nameG, nL) ^ ":= " ^ 
        termG(b) ^ ": " ^ termG(t) ^ ")"
    | G.EPatternBinder{name = n, typ = t} => "`(" ^ nameG(n) ^ ": " ^ termG(t) ^ ")"


  and econtextG (G.EContext(bL)): string = concatListWith(" ", ebinderG, bL)


  and eprogramsG (G.EPrograms(e, eL)): string = 
    eprogramG(e)  ^ concatListWith("\n", emutualG, eL) ^ "."


  and emutualG (e: G.emutual): string = 
    case e of
      G.EWith(p)  => ( let
        val fbody = (eprogramG p)
        val newFbody = if S.substring(fbody, 0, 11) = "\nEquations " 
                      then S.substring(fbody, 11, S.size(fbody) - 11)
                      else fbody
      in
        "\nwith " ^ newFbody
      end )
    | G.EWhere(p) => (ewhereG p)


  and ewhereG (e: G.ewhere): string =
    case e of
      G.Ewherep(p) => "where " ^ (eprogramG p)
    | G.Ewheren(p) => "where " ^ (enotG p) 


  and enotG (G.Enot(s, t)) =  "\"" ^ s ^ "\" " ^ ":= " ^ termG(t) 


  and eprogramG (G.EProgram{ id = i, context = econt, ret = t, body = ecls}) =
    "\nEquations "^ convertIdent(i) ^ " " ^ econtextG(econt) ^ ": " ^ termG(t) ^
     " :=\n" ^ eclausesG(ecls, i)


  and eclausesG (G.EClauses(cl), id): string = 
    let
      val cs  = concatListWith("\n", fn x=> "  " ^ convertIdent(id) ^ " " ^ (eclauseG x), cl)
      val lcs = S.size cs 
    in
      case lcs of
        0 => cs
      | _ => case S.sub(cs, lcs - 1) of
              #";" => S.substring(cs, 0, lcs-1) 
            | _ => cs
    end 


  and eclauseG (G.EClause{ pats = pL, body = t}): string = 
     concatListWith(" ", patternG, pL) ^ " := " ^ termG(t) ^ ";"


  and proofObligationG (G.Theorem(id, t)): string =
    "\nTheorem " ^ id ^ ": "  ^ termG(t) ^ "." ^ "\nAdmitted."    


  (* convertChar(t): string -> string
   * ENSURES: Change char to its representation in Gallina.
   *)
  and convertChar (s: string): string = 
    let
      val c = ord(Option.valOf ( Char.fromString(s) ))
      val c' = if c = 34 then "\"\"" else 
               if c = 92 then "\\" else
               if (S.size s = 6) then Int.toString c else
               if (S.size s = 4) then Int.toString c else
               if c < 32 then Int.toString c else 
               if c > 126 then Int.toString c else s
      val r = if (List.all (Char.isDigit) (S.explode c')) then 
                (if (S.size c') = 3 then c' else 
                 if (S.size c') = 2 then "0" ^ c' else
                 if (S.size c') = 1 then "00" ^ c' else c' )
              else c' 
    in
      "#\"" ^ r ^ "\""
    end
(*----------------------------------------------------------------------------*)
(*----------------------------------------------------------------------------*)


  (* convertType(t): Gallina.ident -> string
   * ENSURES: Change the types (int, char, real, and order) 
   *          to their Gallina equivalent.
   *)
  and convertType (t: G.ident): string =
    case t of 
      "int" => "Z"
    | "char" => "ascii"
    | "real" => "float"
    | "order" => "comparison"
    | _ => t


  (* convertType(t): Gallina.ident -> string
   * ENSURES: Change these special idents to their representation in Gallina.
   *)
  and convertIdent (i: G.ident): string =  
    case i of 
      "LESS" => "Lt"
    | "EQUAL" => "Eq" 
    | "GREATER" => "Gt" 
    | "SOME" => "Some" 
    | "NONE" => "None" 
    | "List.exists" => "List.existsb" 
    | "ListPair.exists" => "ListPair.existsb" 
    | _ => i

end
