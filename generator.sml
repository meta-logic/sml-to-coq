structure Generator = 
struct
    structure G = Gallina;
    structure C = Convertor;
    structure S = String;


  fun concatListWith (p, f, l) = (S.concatWith p (List.map f l))
  val stringLib = ref false
  val asciiLib  = ref false
  val intLib    = ref false
  val realLib   = ref false
  val hexLib    = ref false
  val listLib   = ref false
  val boolLib   = ref false
  val pFailure  = ref false

  (* generate: string -> string
   * ENSURES: generate(source) = code, where code is the string that represents 
   *          the equivelant Gallina code to the SML code from the source
   *)
  fun generate(source: string): string =
    let
      
      val ast        = C.convert source
      val codeList   = sentenceG(ast)
      val codeList   = "\n" :: codeList
      
      val pFailureL  = if !pFailure = true
      then "Local Axiom patternFailure: forall{a}, a."::codeList
      else codeList

      val realLibL   = if !realLib = true
      then "Require Import Floats.\nOpen Scope float_scope."::pFailureL
      else pFailureL
      
      val intLibL    = if !intLib = true
      then "Require Import ZArith.\nOpen Scope Z_scope."::realLibL
      else realLibL
      
      val listLibL   = if !listLib = true
      then "Require Import List.\nImport ListNotations."::intLibL
      else intLibL
      
      val boolLibL   = if !boolLib = true
      then "Require Import Bool."::listLibL
      else listLibL
      
      val hexLibL    = if !hexLib = true
      then "Require Import String HexString.\nOpen Scope string_scope."::boolLibL
      else boolLibL
      
      val asciiLibL = if !asciiLib = true 
      then "Require Import Ascii.\nOpen Scope ascii_scope."::hexLibL
      else hexLibL
      
      val stringLibL = if !stringLib = true 
      then "Require Import String.\nOpen Scope string_scope."::asciiLibL
      else asciiLibL
      
      val () = print((S.concatWith ("\n") stringLibL)^ "\n" ) (*To see the result*)
    in
      (S.concatWith ("\n") stringLibL)^ "\n" 
    end

  and termG (term: G.term): string =
    case term of                              
      G.ForallTerm(bL,t) => "forall "^(concatListWith (" ", binderG, bL))^" , " ^termG(t)
    | G.FunTerm(bL,t)    => "fun"^(concatListWith (" ", binderG, bL))^" => "^termG(t)
    | G.FixTerm(fb)      => "fix " ^ fixbodiesG(fb)
    | G.CofixTerm(fb)    => "cofix " ^ cofixbodiesG(fb)
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
    
    | G.HasTypeTerm(v1,v2)  => termG(v1) ^ " : " ^ termG(v2) 
  (*| omitting check type <: *) 
  (*| omitting tu support type :> *) 
    | G.ArrowTerm(v1,v2)    => termG(v1) ^ " -> " ^ termG(v2) 
    | G.ApplyTerm(v1,aL)    => termG(v1)^" "^(concatListWith (" ", argG, aL)) 
    | G.ExplicitTerm(v1,tL) => "@ " ^ v1 ^" "^(concatListWith (" ", termG, tL)) 
    | G.InScopeTerm(v1,v2)  => termG(v1) ^ " % " ^ v2 
    | G.MatchTerm{matchItems=mL, body=eL} => 
      "match " ^ (concatListWith (", ", matchItemG, mL)) ^ " with" ^ "\n  " ^
      (S.concatWith ("  \n  | ") (List.map equationG eL)) ^ " end"
    
    | G.IdentTerm(v)        => v before boolLib := true
    | G.SortTerm(v)         => sortG(v) 
    | G.NumTerm(v)          => 
      (case (S.isPrefix "~" v) of true => "-"^S.substring(v, 1, S.size(v)-1)
                                | false => v) before intLib:= true       
      
    | G.WildcardTerm        => "_"
    | G.ParensTerm(v)       => "(" ^ termG(v) ^ ")" 
    (*Additional terms to match sml built-in types. (!) *)  
    | G.WordTerm(v)         => v
    | G.RealTerm(v)         => v ^ "%" ^ "float" before realLib := true 
    | G.StringTerm(v)       => "\"" ^ v ^ "\"" before stringLib := true 
    | G.CharTerm(v)         => (convertChar v) before  asciiLib := true
    | G.HexTerm(v)          => "\"" ^ "0x"^ S.map Char.toLower v ^ "\""
                               before hexLib := true
    (* extra : denotes tuple types e.g. int * int. (!) *)
    | G.TupleTerm(tL)       => "(" ^ (concatListWith (", ", termG, tL)) ^ ")"
    | G.ProductTerm (tL)    => "(" ^ (concatListWith (" * ", termG, tL)) ^ ")"
    | G.ListTerm(tL)        => "[" ^ (concatListWith ("; ", termG, tL)) ^ "]" 
                               before listLib := true
    | G.OrTerm(v1, v2)      => termG(v1) ^ " || "  ^ termG(v2) before boolLib := true
    | G.AndTerm(v1, v2)     => termG(v1) ^ " && "  ^ termG(v2) before boolLib := true
    | G.Axiom(a)            => "patternFailure" before pFailure := true
    (*Datatypes with multiple constructors is not considered since it's not implemented yet*)
    | G.MatchNotationTerm{matchItem=mI, body=e, exhaustive=b} => 
      "match " ^ matchItemG(mI) ^ " with" ^ "\n  " ^ equationG(e) ^
      (case b of  true => ""
         | false => "\n  | _ => patternFailure" before pFailure := true)^" end"


  and argG (G.Arg(t))        = termG(t)
    | argG (G.NamedArg(v,t)) = "(" ^ v ^ " := " ^ termG(t) ^ ")"


  and binderG (G.SingleBinder{name=n, typ=tO, inferred=inf}) = 
      (case inf of false => 
      "(" ^ nameG(n) ^ (case tO of NONE => "" | SOME x =>" : "^termG(x))^")"
      | true => 
      "{" ^ nameG(n) ^(case tO of NONE => "" | SOME x =>" : "^termG(x))^ "}")   
    | binderG (G.LetBinder{names=nL, typ=tO, body=bT})       = 
      "(" ^ (concatListWith (" ", nameG, nL)) ^ 
      (case tO of NONE => "" | SOME x =>" : "^termG(x))^" : " ^ termG(bT) ^ ")"
    | binderG (G.PatternBinder(p)) ="' " ^ patternG(p)         


  and nameG (G.Name(n))      = n 
    | nameG (G.WildcardName) = "_"


  and sortG (G.Prop) = "Prop"
    | sortG (G.Set)  = "Set"
    | sortG (G.Type) = "Type"


  and fixbodiesG (G.Fixbodies(fL, i)) = 
      (concatListWith ("\nwith ", fixbodyG, fL)) ^ " for " ^ i


  and cofixbodiesG (G.CoFixbodies(cL, i)) = 
      (S.concatWith ("\nwith ") (List.map coFixbodyG cL)) ^ " for " ^ i


  and fixbodyG (G.Fixbody{id=i, binders=bL, decArg=aO, typ=tO, body=t}) = 
      i ^ " " ^(concatListWith (" ", binderG, bL)) ^ " " ^ 
      (case aO of NONE => "" | SOME a => annotationG(a)^" ") ^ 
      (case tO of NONE => "" | SOME t => " : " ^ termG(t)^" ") ^ ":= " ^ termG(t)


  and coFixbodyG (G.Cofixbody {id=i, binders=bL, typ=tO, body=t}) = 
      i ^ " " ^(concatListWith (" ", binderG, bL)) ^ " " ^
      (case tO of NONE => "" | SOME x => termG(x)^" ") ^ ":= " ^ termG(t)      


  and annotationG (G.Annotation(i)) = "{ struct " ^ i ^ " }"


  and matchItemG (G.MatchItem (t))  = termG(t) 


  and depRetTypeG (G.DepRet(nO,r))   = 
    (case nO of NONE => "" | SOME x => "as " ^ nameG(x)) ^ retTypeG(r)


  and retTypeG (G.Ret(t)) = "return " ^ termG(t)


  and equationG (G.Equation(p, t))  = patternG(p) ^ " => " ^ termG(t)


  and patternG (pattern: G.pattern): string =
    case pattern of
      G.ArgsPat(i, pL)   => i ^ " " ^ concatListWith (" ", patternG, pL)
    | G.AtArgsPat(i, pL) => "@" ^ i ^ " " ^ concatListWith (" ", patternG, pL)
    | G.AsPat(p, i)      => patternG(p) ^ " as " ^ i
    | G.ScopePat(p, i)   => patternG(p) ^ " % " ^ i 
    | G.QualidPat(i)     => i
    | G.WildcardPat      => "_"
    | G.NumPat(s)        => 
    (if S.isPrefix "~" s then "-"^S.substring(s, 1, S.size(s)-1) else s) 
    before intLib:= true  
  (*| omitting pattern OrPat(oL) => "(" ^o rPatternG(oL) ^ ")"*)
    (*Additional Patternss*)
    | G.WordPat(s)       => s
    | G.RealPat(s)       => s before realLib := true 
    | G.StringPat(s)     => "\"" ^ s ^ "\"" before stringLib := true 
    | G.CharPat(s)       => "\"" ^ s ^ "\"" before stringLib := true
    | G.HexPat(s)        => "\"" ^ "0x"^ S.map Char.toLower s ^ "\"" 
                            before hexLib := true
      (* extra *)  
    | G.TuplePat(pL)     => "(" ^ concatListWith (", ", patternG, pL) ^ ")"
    | G.ListPat(pL)      => "[" ^ concatListWith (", ", patternG, pL) ^ "]" 
                            before listLib := true
    | G.ParPat(p)        => patternG(p)


  and orPatternG (G.OrPattern(pL)) = concatListWith("| ", patternG, pL)


  and sentenceG (sentence: G.sentence list): string list =
    case sentence of 
      nil    => nil
    | x::ast => case x of
                  G.DefinitionSentence(d) => definitionG(d)::sentenceG(ast)
                | G.InductiveSentence(i)  => inductiveG(i)::sentenceG(ast)
                | G.FixpointSentence(f)   => fixpointG(f)::sentenceG(ast)
                | G.RecordSentence(r)     => recordG(r)::sentenceG(ast)
                | G.SeqSentences(n)       => sentenceG(n)@sentenceG(ast)


  and recordG (rL) = "Record " ^ concatListWith("with ", recBodyG, rL)


  and recBodyG (G.RecordBody{id=i, binders=bL, typ=sO, consName=iO, body=fL}) =
    i ^ " := " ^ concatListWith(" ", binderG, bL) ^ 
    (case sO of NONE => "" | SOME x => sortG(x)) ^ 
    " := " ^ (case iO of NONE => "" | SOME x => x) ^ 
    "{ " ^ concatListWith(" \n  ; ", fieldG, fL) ^ "}" ^ "." 


  and fieldG (G.Field(itL)) = 
    concatListWith(" \n  ; ", (fn (i,t)=> i ^ " := " ^ termG(t)), itL)
    

  and definitionG (def: G.definition): string  =
    case def of
      G.DefinitionDef{binders=bL, body=term ,id=i, localbool=loc ,typ=ty}    =>
      (if loc then "Local" else "") ^ "Definition " ^ 
      i ^ concatListWith(" ", binderG, bL) ^ 
      (case ty of NONE => "" | SOME x => " : " ^ termG(x)) ^
       " := " ^ termG(term) ^ "."

    | G.LetDefinitionDef{binders=bL, body=term ,id=i, typ=ty} =>
      "Let " ^ i ^ concatListWith(" ", binderG, bL) ^ 
      (case ty of NONE => "" | SOME x => " : " ^ termG(x)) ^
       " := " ^ termG(term) ^ "."


  and inductiveG (ind: G.inductive): string  = (* I think there is somthing wrong with the AST*)
    case ind of
        G.Inductive(inbL)   => "Inductive "   ^ concatListWith("\nwith ", indBodyG, inbL)^"."
      | G.CoInductive(inbL) => "CoInductive " ^ concatListWith("\nwith ", indBodyG, inbL)^"."
  

  and indBodyG (G.IndBody{id=i, bind=bL, typ=t, clauses=cL}) =
      i ^" "^concatListWith(" ", binderG, bL) ^ " : " ^ termG(t) ^
      " := " ^ "\n  " ^ concatListWith("  \n  | ", clauseG, cL)


  and clauseG (G.Clause(i, bL, tO)) = 
    i ^ concatListWith(" ", binderG, bL) ^ 
    (case tO of NONE => "" | SOME x => " :" ^ termG(x))


  and fixpointG (fp: G.fixpoint): string =
    case fp of
        G.Fixpoint(fL)   => "Fixpoint "    ^ concatListWith("\nwith ", fixbodyG, fL)^"."
      | G.CoFixpoint(fL) => "CoFixpoint  " ^ concatListWith("\nwith ", fixbodyG, fL)^"."  

  and convertChar (s: string): string = 
      let
        val c = ord(Option.valOf ( Char.fromString(s) ))
        val c' = if c = 34 then "\"\"" else 
                if c < 32 then Int.toString c else 
                if c > 126 then Int.toString c else s
        val r = if (List.all (Char.isDigit) (S.explode c')) then 
                  (if (S.size c') = 3 then c' else 
                   if (S.size c') = 2 then "0" ^ c' else
                   if (S.size c') = 1 then "00" ^ c' else c' )
                else c' 
      in
        "\"" ^ r ^ "\"" ^ "%"^ "char"
      end
end
