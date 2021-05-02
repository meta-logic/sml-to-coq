(* (c) SMLtoCoq
 * We refer to important sections in the following four documents:
 * Documentation (doc): in the doc directory
 * SML's Definition (def): https://smlfamily.github.io/sml97-defn.pdf
 * Gallina's Documentation (gallina): https://coq.inria.fr/refman/language/core/index.html
 * HaMLet's Documentation (hamlet): https://people.mpi-sws.org/~rossberg/hamlet/hamlet-2.0.0.pdf
 *)

(*
 * Converts SML abstract core syntax (doc, section 3).
 * For each translation rule of the form s => g, we define a corresponding function s2g (some exceptions may apply).
 * We make use of three contexts: record local context, record global context, and tyvar local context (doc, sections 3.2 and 3.3)
 * The full grammar can be found in SML's Definition (def, appendix B)
*)

(*
 * For each main translation function we provide the following:
 * EXAMPLE: an SML code example
 * FROM: Section/Figure number in SML's Definition
 * TO SECTION: Section name in Gallina's documentation
 * NOTES: additional notes
 *)



structure ConvertorCore =
struct
structure D = DynamicObjectsCore
structure F = FunctionChecker
structure T = TyvarResolver
local
    structure G = Gallina
    infix @@
    infix ==>
in
exception WildCard

(* Local record context, doc: section 3.2 *)
val recordContext = ref [] : (G.sentence list) ref
val infixContext = ref [] : (G.sentence list) ref
(* Global record context, doc: section 3.2 *)
val recordTracker = ref (ConvertorUtil.LT.empty) : (G.ident ConvertorUtil.LT.dict) ref
val infixTracker = ref (VIdMap.empty) : ((Infix.InfStatus * bool) VIdMap.map) ref
(* Local tyvar context, doc: section 3.3 *)
val tyvarCtx = ref (ConvertorUtil.TT.empty)

(* functions' names that use obligations *)
val funH = ref [] : (string list) ref
val exFNum = ref 0  : int ref
val inThm = ref false : bool ref

structure AE = AnnotationExtractor(val recordContext = recordContext; val recordTracker = recordTracker)
open AE

(* EXAMPLES: 5, "a", #'c'
 * FROM: Section 2.2
 * TO: Essential Vocabulary: term
 * KEYWORD: term
 *)
fun scon2term (SCon.STRING s : SCon.SCon) : G.term = G.StringTerm s
  | scon2term (SCon.CHAR s) = G.CharTerm s
  | scon2term (SCon.REAL s) = G.RealTerm s
  | scon2term (SCon.INT (b, s)) = if b = SCon.DEC then G.NumTerm s else G.HexTerm s
  (* Need to check what's a word constant *)
  | scon2term (SCon.WORD (b, s)) = if b = SCon.DEC then G.WordTerm (s, G.Dec) else G.WordTerm (s, G.Hex)

structure PF = PrecondsFinder(struct val scon2term = scon2term end)

fun isExhaustive A : bool =
    case (try (exhaustive A)) of
        SOME S.Exhaustive => true
      | _ => false

(* FROM: Scon.sml: 15 -> 20
 * TO:   Gallina.sml : 97 -> 115
 * FROM SECTION: -
 * TO SECTION: 4.1.3 page 115
 * KEYWORD: pattern
 *)
fun scon2pattern (SCon.STRING s : SCon.SCon) : G.pattern = G.StringPat s
  | scon2pattern (SCon.CHAR s) = G.CharPat s
  | scon2pattern (SCon.REAL s) = G.RealPat s
  | scon2pattern (SCon.INT (b, s)) = if b = SCon.DEC then G.NumPat s else G.HexPat s
  (* Need to check what's a word constant *)
  | scon2pattern (SCon.WORD (b, s)) = if b = SCon.DEC then G.WordPat (s, G.Dec) else G.WordPat (s, G.Hex)


and tyrow2body (TyRow(lab, ty, tyrow') @@ _ : TyRow) : (G.ident * Ty') list = (~lab, ~ty) :: ?tyrow2body tyrow'

and tybody2labs (body : (G.ident * Ty') list) = Sort.sort String.compare (#1(ListPair.unzip body))

and status2modifiers ((Infix.LEFT, level) : Infix.InfStatus) : G.modifier list = [G.LeftAssoc, G.Level level]
  | status2modifiers ((Infix.RIGHT, level)) = [G.RightAssoc, G.Level level]


and exprow2body (ExpRow(lab, exp, exprow') @@ _) = (~lab, ~exp) :: ?exprow2body exprow'

and expbody2fields ident body = let
    fun expbody2field (lab, exp) = G.FieldDef {id = ident ^ "_" ^ (checkLegal lab), binders = [], term = exp2term exp }
in List.map expbody2field body end

and patrow2body (labels : Lab.Lab list) (patrow) =
    let
        fun patrow2body' (FIELDPatRow(lab, pat, patrow') @@ _) =
            let
                val (lab, pat) = (~lab, pat2pattern (pat))
                val body = (lab, pat) :: (?patrow2body' patrow')
            in
                body
            end
          | patrow2body' _ = []
        val body = LabMap.fromList (patrow2body' patrow)
        val body' = LabMap.fromList (List.map (fn l => (l, G.WildcardPat)) labels)
        val labs = orderLabs labels
        val res = LabMap.listItemsi (LabMap.unionWith (fn (a, _) => a) (body, body'))
    in
        case LT.find (!recordTracker) labs of
            SOME id => (id, res)
          | NONE => let
              val id = genIdent ()
              val typs = gentyps (List.length labs)
              val _ = recordTracker := LT.insert (!recordTracker) labs id
              val _ = recordContext := mkRecord (labs, id, typs) :: !recordContext
          in
              (id, res)
          end

    end



and patbody2fields ident body = let
    fun patbody2field (lab, pat) = G.FieldPat {id = ident ^ "_" ^ checkLegal lab, binders = [], pat = pat}
in List.map patbody2field body end

(* EXAMPLE: type class = (id, name) hashtable :(id, name) forms a tyseq
 * FROM: SyntaxCoreFn.sml: 159 -> 164
 * TO:   Gallina.sml : 55
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: tyseq
 * TO SECTION: 4.1.3 page 115
 * KEYWORD: arg
 *)
and tyseq2args (Seq tys : Ty seq') : G.arg list = % ty2arg tys

(* EXAMPLE: check tyseq2args
 * FROM: SyntaxCoreFn.sml: 159 -> 164
 * TO:   Gallina.sml : 55
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: tyseq
 * TO SECTION: 4.1.3 page 115
 * KEYWORD: arg
 * NOTES: Associativity: Might solve this by explicitly adding 
 * parenthesis or by requiring the user to explicitly put parenthesis? 
 *)
and ty2arg (ty : Ty') : G.arg = G.Arg (ty2term ty)


(* EXAMPLE: type age = int (ty encodes int)
 * FROM: SyntaxCoreFn.sml: 159 -> 164
 * TO:   Gallina.sml : 16 -> 53
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: ty
 * TO SECTION: 4.1.3 page 115
 * KEYWORD: term
 *)    
(* VARty is type variable, e.g. 'a list  *)
and ty2term ((VARTy tyvar) : Ty') : G.term =
    let val typ = (checkLegal(TyVar.toString (~tyvar)))
    in
        G.IdentTypTerm (typ)
    end
  (* in scope term because the operator "*" is overloaded *)
  | ty2term (TUPLETyX (tys)) = 
    if List.length(tys) > 1 then
        G.InScopeTerm (G.ProductTerm (% ty2term tys), "type") 
    else
        (* G.ParensTerm *) (List.nth ((% ty2term tys), 0))
  (* CONTy is constructor type, e.g. int  *)            
  | ty2term (CONTy (tyseq, tycon)) = let
      val terms = % ty2term ($(~tyseq))
      val tycon = ltycon2id (~tycon)
  in
      (case terms of [] => G.IdentTypTerm tycon | _ => G.ExplicitTerm(tycon, terms))
  end
  (* PARTy is parenthesis type, e.g. (int)  *)
  | ty2term (PARTy ty) = G.ParensTerm (ty2term (~ty))
  (* ARROWTy is arrow type, e.g. int -> int  *)
  | ty2term (ARROWTy(ty1, ty2)) = G.ArrowTerm(ty2term (~ty1), ty2term (~ty2))
  | ty2term (RECORDTy recBody) = let
      val body = ?tyrow2body recBody
      val labs = tybody2labs body
      val names = case recBody of NONE => []
                                | SOME(_@@A) => (case !(elab A) of NONE => []
                                                                 | SOME rowtyp => T.getTyvars' (T.S.RowType(rowtyp)))
  in
      case LT.find (!recordTracker) labs of
          SOME ident => G.IdentTypTerm (ident)
        | _ => let
            val id = genIdent ()
            val _ = recordTracker := LT.insert (!recordTracker) labs id
            val _ = recordContext := tyrow2sent (names, body, id) :: !recordContext
        in
            G.IdentTypTerm (id)
        end
  end

(* FROM: SyntaxCoreFn.sml: 103 -> 104
 * TO:   Gallina.sml: 95
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: mrule
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: equation
 *)
and mrule2equation (Mrule(pat, exp) : Mrule') : G.equation = 
    let
        val term = exp2term (~ exp)
        val pattern = pat2pattern (pat)
    in
        G.Equation(pattern, term)
    end

(* FROM: SyntaxCoreFn.sml: 84 -> 94
 * TO:   Gallina.sml: 89
 * FROM SECTION: Appendix C.1 page 102
 * KEYWORD: exp
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: match_item
 *)
and exp2matchitem (exp : Exp') : G.matchItem = G.MatchItem (exp2term(exp))

(* FROM: SyntaxCoreFn.sml: 100 -> 101
 * TO:   Gallina.sml: 95
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: match
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: equation
 *)
and match2equations (Match(mrule, match2) @@ A : Match) : G.equation list = 
    let
        fun match2equations' (Match(mrule, match2)@@_ : Match) =
            (mrule2equation (~mrule)) :: (?match2equations' match2)
        val equation2 = if isExhaustive A then []
                        else [G.Equation(G.WildcardPat, G.Axiom G.PatternFailure)]
        val equations = (mrule2equation (~mrule)) :: (?match2equations' match2) @ equation2
    in
        equations
    end

(* FROM: SyntaxCoreFn.sml: 71 -> 79
 * TO:   Gallina.sml: 64
 * FROM SECTION: Appendix C.1 page 102
 * KEYWORD: atexp
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: arg
 *)
and atexp2args (atexp : AtExp) : G.arg list = [G.Arg (atexp2term atexp)]

(* Helper function doesn't have corresponding sections, check atexp2term *)
and sentterm2letTerm ((G.DefinitionSentence (G.DefinitionDef sent)) : G.sentence, term : G.term) = 
    G.LetTerm {id = #id sent, binders = #binders sent, typ = #typ sent,
               body = #body sent, inBody = term}
  | sentterm2letTerm (G.SeqSentences sents, term) = 
    let
        fun nested([] : G.sentence list) = term
          | nested (s :: sL) = 
            sentterm2letTerm (s, (nested sL))
    in
        nested sents
    end    
  | sentterm2letTerm _ = raise Fail "Translating this sentence to let is invalid/Unimplemented \n"        

(* FROM: SyntaxCoreFn.sml: 71 -> 79
 * TO:   Gallina.sml: 21 -> 62
 * FROM SECTION: Appendix C.1 page 102
 * KEYWORD: atexp
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: term
 *)
and atexp2term (SCONAtExp(scon)@@_ : AtExp) : G.term = scon2term (~scon)
  | atexp2term (IDAtExp(opVal, longvid)@@A) = 
    let
        val vid = lvid2id (~longvid)
        val opVal = case opVal of
                        NONE => false
                      | SOME _ => (case VIdMap.find (!infixTracker, VId.fromString vid) of
                                       NONE => false
                                     | SOME (_, true) => true
                                     | SOME (status, false) =>
                                       (infixContext := (mkInfix(vid, status2modifiers status) @ !infixContext);
                                        infixTracker := VIdMap.insert(!infixTracker, VId.fromString vid, (status, true));
                                        true))
    in
        (case T.resolveTyvars tyvarCtx (!(elab A)) of
             NONE => G.IdentTerm (opetize opVal vid)
           | SOME typ => G.HasTypeTerm(G.IdentTerm (opetize opVal (vid)), typ))
    end
  | atexp2term (RECORDAtExp(recBody)@@_) = let
      val body = ?exprow2body recBody
      val labs = orderLabs (#1 (ListPair.unzip body))
  in
      case LT.find (!recordTracker) labs of
          SOME ident => G.RecordTerm (expbody2fields ident body)
        | NONE => let
            val id = genIdent ()
            val typs = gentyps (List.length labs)
            val _ = recordTracker := LT.insert (!recordTracker) labs id
            val _ = recordContext := mkRecord (labs, id, typs) :: !recordContext
        in
            G.RecordTerm (expbody2fields id body)
        end
  end
  | atexp2term (LETAtExp(dec, exp)@@_) = 
    let
        val sent = dec2sent dec
        val term = exp2term (~exp)
    in
        sentterm2letTerm (sent, term)
    end
  | atexp2term (PARAtExp(exp)@@_) = G.ParensTerm (exp2term (~exp))
  | atexp2term (UNITAtExpX@@ _) = G.UnitTerm 
  (* in scope term because the operator "*" is overloaded *)
  | atexp2term (TUPLEAtExpX(exps)@@_) = G.TupleTerm(% exp2term exps)
  | atexp2term (LISTAtExpX(exps)@@A) = 
    if length exps > 0 then G.ListTerm(% exp2term exps)
    else (* For empty lists with undetermined types, we need to add an explicit type in Gallina *)
        case T.resolveTyvars tyvarCtx (!(elab A)) of
            NONE => G.ListTerm(% exp2term exps)
          | SOME typ => G.HasTypeTerm(G.ListTerm(% exp2term exps), typ)


(* FROM: SyntaxCoreFn.sml: 84 -> 94
 * TO:   Gallina.sml: 21 -> 62
 * FROM SECTION: Appendix C.1 page 102
 * KEYWORD: exp
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: term
 *)
and exp2term (ATExp atexp : Exp') : G.term = atexp2term (atexp)
  | exp2term (APPExp (exp, atexp)) =  (* Changed, (might need to be changed in the future) *)
    let
      val result = 
        case exp of
          ATExp(IDAtExp(opr, lvid)@@_)@@_ => 
            (case List.find (fn x => x = (lvid2id (~lvid))) (!funH) of
              SOME x => 
               (if (!inThm) 
                then G.ExplicitTerm(x, (atexp2term atexp)::[G.IdentTerm("H")]) before (exFNum := 1 + !exFNum)
                else G.ApplyTerm(exp2term (~exp), atexp2args (atexp)))
            | NONE => G.ApplyTerm(exp2term (~exp), atexp2args (atexp)))
        | _ => G.ApplyTerm(exp2term (~exp), atexp2args (atexp))

    in
      result (*G.ApplyTerm(exp2term (~exp), atexp2args (atexp))*)
    end      
  | exp2term (COLONExp (exp, ty)) = 
    let val typ = ty2term (~ty)
        val exp = exp2term (~exp)
    in G.HasTypeTerm(exp, typ) end
  | exp2term (FNExp(match as Match(Mrule(pat, exp)@@_, _)@@A)) = 
    let
        val expand = isExhaustive A 
        val ty = extractTypFromPat (~pat)
        val binders = pat2binders (pat) false
    in
        (case (expand, ty) of
             (false, NONE) =>
             let val binders = pat2binders (pat) false
                 val body = exp2term (~exp)
             in G.FunTerm (binders, body) end
           | (false , SOME typ) =>
             (case binders of
                  [G.SingleBinder {name = name, ... }] =>
                  let val binders = G.SingleBinder {name = name, typ = SOME typ, inferred = false}
                      val body = exp2term (~exp)
                  in G.FunTerm ([binders], body) end
                | _ => 
                  let val id= vid2id (VId.invent())
                      val binders = G.SingleBinder {name = G.Name id, typ = NONE, inferred= false}
                      val equations = match2equations match
                      val body = G.MatchTerm { matchItems = [G.MatchItem (G.HasTypeTerm (G.IdentTerm (id), typ))], body = equations}
                  in G.FunTerm ([binders], body) end)
           | (_, SOME typ) => 
             let val id= vid2id (VId.invent())
                 val binders = G.SingleBinder {name = G.Name id, typ = NONE, inferred= false}
                 val equations = match2equations match
                 val body = G.MatchTerm { matchItems = [G.MatchItem(G.HasTypeTerm (G.IdentTerm (id), typ))], body = equations}
             in G.FunTerm ([binders], body) end
           | (_, NONE) => 
             let val id= vid2id (VId.invent())
                 val binders = G.SingleBinder {name = G.Name id, typ = NONE, inferred= false}
                 val equations = match2equations match
                 val body = G.MatchTerm { matchItems = [G.MatchItem(G.IdentTerm (id))], body = equations}
             in G.FunTerm ([binders], body) end)
    end
  | exp2term (CASEExpX (exp, match)) = 
    let
        val matchItems = [exp2matchitem (~exp)]
        val equations = match2equations match
    in
        G.MatchTerm {matchItems = matchItems, body = equations}
    end
  | exp2term (IFExpX (exp1, exp2, exp3)) = let
      val exp1' = exp2term (~exp1)
      val exp2' = exp2term (~exp2)
      val exp3' = exp2term (~exp3)
  in
      G.IfTerm {test = exp1', thenTerm = exp2', elseTerm = exp3'}
  end
  | exp2term (ANDALSOExpX (exp1, exp2)) = let
      val exp1' = exp2term (~exp1)
      val exp2' = exp2term (~exp2)
  in
      G.AndTerm (exp1', exp2')
  end
  | exp2term (ORELSEExpX (exp1, exp2)) = let
      val exp1' = exp2term (~exp1)
      val exp2' = exp2term (~exp2)
  in
      G.OrTerm (exp1', exp2')
  end
  | exp2term (INFIXExpX (exp, atexp)) =
    G.InfixTerm (exp2term (~exp), atexp2args (atexp))

and extractTypFromAtPat (RECORDAtPat(NONE)) : G.term option = NONE
  | extractTypFromAtPat (RECORDAtPat(SOME patrow)) =  raise Fail "Constructor Pattern shouldn't have interior types\n"
  | extractTypFromAtPat (PARAtPat pat) = extractTypFromPat (~pat)
  | extractTypFromAtPat (TUPLEAtPatX pats) =
    let
        val typs = % extractTypFromPat pats
    in
        if List.exists (Option.isSome) typs then
            SOME (G.ProductTerm (List.map (fn x => case x of NONE => G.WildcardTerm 
                                                           | SOME ty => ty) typs))
        else NONE
    end
  | extractTypFromAtPat (LISTAtPatX pats) = 
    let
        val typs = % extractTypFromPat pats
    in
        (case List.find (Option.isSome) typs of
             NONE => NONE
           | SOME (SOME typ) => SOME (G.ExplicitTerm ("list", [typ])))
    end
  | extractTypFromAtPat _ = NONE

and extractTypFromPat (ATPat atpat) = extractTypFromAtPat (~atpat)
  | extractTypFromPat (CONPat(_, longvid, atpat)) =
    (case extractTypFromAtPat(~atpat) of
         NONE => NONE
       | SOME _ => raise Fail "Constructor Pattern shouldn't have interior types\n")
  | extractTypFromPat (COLONPat (pat, ty)) = SOME (ty2term(~ty))
  | extractTypFromPat (ASPat (_, _, SOME ty, _)) = SOME (ty2term(~ty))
  | extractTypFromPat (ASPat (_, _, NONE, pat)) = extractTypFromPat (~pat)
  | extractTypFromPat (INFIXPatX(_, _, atpat)) = extractTypFromAtPat (~atpat)


and atpat2binders (WILDCARDAtPat@@_ : AtPat)  withTy : G.binder list =
    [G.SingleBinder {name = G.WildcardName, typ = NONE, inferred = false}]
  | atpat2binders ((SCONAtPat scon)@@_) withTy = raise Fail "Invalid Pattern!\n"
  | atpat2binders (IDAtPat(_, longvid)@@_) withTy =
    [G.SingleBinder {name = mkName (lvid2id (~longvid)), typ = NONE, inferred = false}]
  | atpat2binders (PARAtPat(pat)@@_) withTy = pat2binders (pat) withTy
  | atpat2binders p withTy = [G.PatternBinder (atpat2pattern p)]


and pat2binders (ATPat(atpat)@@_ : Pat) (withTy) : G.binder list =
    atpat2binders (atpat) withTy
  | pat2binders (COLONPat(pat, ty)@@_) (true) = 
    (case pat of
        (ATPat(IDAtPat(_, longvid)@@_)@@_) =>
      [G.GenericBinder {name = mkName (lvid2id (~longvid)), typ = SOME (typ2typ tyvarCtx (ty2type ty)), inferred = false}]
    | _ => pat2binders (pat) true)
  | pat2binders (COLONPat(pat, ty)@@_) (withTy) = pat2binders (pat) withTy
  | pat2binders (p) (_) = [G.PatternBinder (pat2pattern p)]

(* FROM: SyntaxCoreFn.sml: 144 -> 152
 * TO:   Gallina.sml : 96 -> 114
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: atpat
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: pattern
 *)
and atpat2pattern (WILDCARDAtPat@@_ : AtPat) : G.pattern = G.WildcardPat
  | atpat2pattern (SCONAtPat(scon)@@_) = scon2pattern (~scon)
  (* ignoring Op for now *)
  | atpat2pattern (IDAtPat (_, longvid)@@_) = G.QualidPat (lvid2id (~longvid))
  | atpat2pattern (RECORDAtPat(recBody)@@A) =
    let
        val SOME (_, labs) = !(hd (tl A))
        val labs = (case !labs of
            S.RowType (l, _) => l
          | S.Determined (ref (S.RowType (l, _))) => l (* For {...} patterns *)
          | _ => raise Fail "Error fetching labels from record patterns."
        )
        val labs = #1 (ListPair.unzip (LabMap.listItemsi labs))
        val (ident, body) = case recBody of NONE => ("", [])
                                          | SOME recBody => patrow2body labs recBody
    in
        if List.length body = 0 then G.WildcardPat 
        else G.RecPat (patbody2fields ident body)
    end
  | atpat2pattern (PARAtPat(pat)@@_) = G.ParPat (pat2pattern (pat))
  | atpat2pattern (UNITAtPatX@@_) = G.UnitPat
  | atpat2pattern (TUPLEAtPatX(pats)@@_) = G.TuplePat (List.map pat2pattern pats)
  | atpat2pattern (LISTAtPatX(pats)@@_) = G.ListPat (List.map pat2pattern pats)

(* FROM: SyntaxCoreFn.sml: 159 -> 163
 * TO:   Gallina.sml : 96 -> 114
 * FROM SECTION: Appendix C.1 page 103
 * KEYWORD: pat
 * TO SECTION: Section 4.1.3 Page 115
 * KEYWORD: pattern
 *)
and pat2pattern (ATPat(atpat)@@_ : Pat) : G.pattern = atpat2pattern atpat
  | pat2pattern (CONPat (opVal, longvid, atpat)@@_) = G.ArgsPat (opetize false (lvid2id (~longvid)), [atpat2pattern (atpat)])
  | pat2pattern (COLONPat (pat, ty)@@_) = 
    let val _ = print "Coq doesn't support type casting in patterns!\n" 
    in pat2pattern(pat) end
  (* Can ASPat ever has a non-empty Op? *)
  | pat2pattern (ASPat(_, vid, ty, pat)@@_) = 
    let val _ = if Option.isSome ty then print "Coq doesn't support type casting in patterns!\n" 
                else () 
    in G.AsPat(pat2pattern(pat), vid2id (~vid)) end
  (* Can INFIXPatX ever has a non-empty Op? *)
  | pat2pattern (INFIXPatX (_, longvid, atpat)@@_) = G.InfixPat (lvid2id (~longvid), [atpat2pattern (atpat)])

(* Helper function doesn't have corresponding sections, check valBind2sent *)
and patBody2sents (G.QualidPat ident : G.pattern, body : G.term) (_ : bool): G.sentence list = 
    [G.DefinitionSentence
         (G.DefinitionDef
              {localbool = false, id = ident, binders = T.clearTyvars true tyvarCtx, typ = NONE, body = body})]
  (* As patterns are split into two definitions:
         val x as y = 1 becomes Defintion x := 1; Definition y := 1 *)
  | patBody2sents (G.AsPat (pat, id), body) exhaustive = 
    (patBody2sents (G.QualidPat id, body) exhaustive) @ (patBody2sents (pat, body) exhaustive)
  (* Wildcard patterns are ignored because apart from side effects, they cannot change the context *)
  | patBody2sents (G.WildcardPat, _) (_) = []
  (* Parenthesis patterns are ignored (e.g. val (x) = 1) *)
  | patBody2sents (G.ParPat pat, body) exhaustive = patBody2sents (pat, body) exhaustive
  (* N-ary Tuple patterms are split into N-ary definitions:
         val (x, y ) = (1, 2) becomes Definition x := 1; Definition y := 2 *)
  | patBody2sents (pat as G.TuplePat pats, body) exhaustive =
    List.concat (List.map (patBody2sents' (pat, body, exhaustive)) pats)
  (* N-ary Tuple patterms are split into N-ary definitions:
             val (x, y) = (1, 2) becomes Definition x := 1; Definition y := 2 *)
  | patBody2sents (pat as G.ListPat pats, body) exhaustive =
    List.concat (List.map (patBody2sents' (pat, body, exhaustive)) pats)
  | patBody2sents (pat as G.ArgsPat (id, pats), body) exhaustive =
    List.concat (List.map (patBody2sents' (pat, body, exhaustive)) pats)
  | patBody2sents (pat as G.RecPat fieldpats, body) exhaustive =
    List.concat (List.map (patBody2sents' (pat, body, exhaustive))
                          (List.map (fn (G.FieldPat {pat = pat, ...}) => pat) fieldpats))
  | patBody2sents (pat as G.InfixPat (id, pats), body) exhaustive =
    List.concat (List.map (patBody2sents' (pat, body, exhaustive)) pats)
  | patBody2sents _ _ = raise Fail "Invalid pattern! \n"

(* Helper function doesn't have corresponding sections, check valBind2sent *)
and patBody2sents' (matchees : G.pattern, matcher : G.term, exhaustive : bool) (pat as G.QualidPat ident : G.pattern) : G.sentence list = 
    patBody2sents(pat, mkMatchNotationTerm (G.MatchItem matcher, matchees) (G.IdentTerm ident, exhaustive)) exhaustive
  | patBody2sents' (matchees, matcher, exhaustive) (G.AsPat (pat, id)) = 
    (patBody2sents' (matchees, matcher, exhaustive) pat) @ 
    (patBody2sents (
          G.QualidPat id, 
          mkMatchNotationTerm (G.MatchItem matcher, matchees) (G.IdentTerm id , exhaustive)) exhaustive)
  | patBody2sents' (matchees, matcher, exhaustive) (G.ArgsPat(id, pats)) =
    List.concat (List.map (patBody2sents' (matchees, matcher, exhaustive)) pats)
  | patBody2sents' (matchees, matcher, exhaustive) (G.TuplePat pats) = 
    List.concat (List.map (patBody2sents' (matchees, matcher, exhaustive)) pats)
  | patBody2sents' (matchees, matcher, exhaustive) (G.ListPat pats) = 
    List.concat (List.map (patBody2sents' (matchees, matcher, exhaustive)) pats)            
  | patBody2sents' (matchees, matcher, exhaustive) (G.ParPat pat) = 
    patBody2sents' (matchees, matcher, exhaustive) pat
  | patBody2sents' _ G.WildcardPat = []
  | patBody2sents' (matchees, matcher, exhaustive) (G.InfixPat(id, pats)) =
    List.concat (List.map (patBody2sents' (matchees, matcher, exhaustive)) pats)
  | patBody2sents' _ (G.NumPat _) = []
  | patBody2sents' _ (G.StringPat _) = []
  | patBody2sents' _ (G.CharPat _) = []
  | patBody2sents' _ _ = raise Fail "Invalid pattern!"


(* EXAMPLE: type ('a, 'b) age = 'a * 'b  (the lhs ('a, 'b))
 * FROM: TyVar.sml: 25 -> 29
 * TO:   Gallina.sml : 59
 * FROM SECTION: -
 * KEYWORD: -    
 * TO SECTION: 4.1.3 page 115
 * KEYWORD: binder
 * NOTES:
 * inferredVal is always false because the variable is always explicit
 *)
and tyvarseq2binder (tyvars: TyVar.TyVar list) : G.binder list = 
    let
        fun tyvar2binder tyvars =
            let
                val nameVal = mkName (TyVar.toString tyvars)
                val typVal = SOME (mkSortTerm 1)
                val inferredVal = true
            in
                G.SingleBinder {name = nameVal, typ = typVal, inferred = inferredVal}
            end
    in
        List.map tyvar2binder tyvars
    end

and names2binder (names : G.name list) : G.binder list =
    [G.MultipleBinders {names = names, typ = mkSortTerm 1, inferred = true}]

(* EXAMPLE: datatype cards = Hearts | Spades | Clubs | Diamonds (rhs is conbind)
 * FROM: SyntaxCoreFn.sml: 130
 * TO:   Gallina.sml : 147
 * FROM SECTION: Appendix C.1 page 104
 * KEYWORD: conbind
 * TO SECTION: 4.1.4 page 120
 * KEYWORD: indbody (rhs is a clause list)
 * NOTES:
 * ignoring Op for now, check SyntaxCore for more info
 *)
and conbind2clauses(cons @@ _ : ConBind) : G.clause list =
    let
        val ConBind(_, tycon, ty, conbind2) = cons
        val idVal = vid2id (~tycon)
        val binderVal = []
        val typVal = (case ty of
                          SOME ty' => SOME (ty2term (~ty'))
                        | _ => NONE)
        val clauses = ?conbind2clauses conbind2
        val clause = G.Clause (idVal, binderVal, typVal)
    in
        clause :: ?conbind2clauses conbind2
    end

and tyrow2sent (names : G.name list, body : (G.ident * Ty') list, ident : G.ident) : G.sentence =
    G.RecordSentence [G.RecordBody {id = ident, binders = names2binder names, typ = NONE,
                                    consName = NONE, body = [tyrow2field ident body] }]

and tyrow2field ident (body : (G.ident * Ty') list) : G.field =
    G.Field (List.map (fn (id, ty) => (ident ^ "_" ^ checkLegal id, ty2term ty)) body)


and fnexp2funbody (FNExp(Match(Mrule(ATPat(IDAtPat(_, longvid)@@_)@@_, exp)@@_,_)@@_)) : G.binder list * G.term =
    let val (binders, body) = fnexp2funbody (~exp)
        val binders = (T.clearTyvars true tyvarCtx) @ binders
        val name = mkName (lvid2id(~longvid))
        val binder = G.SingleBinder {name = name, typ = NONE, inferred = false}
    in
        (binder :: binders, body)
    end
  | fnexp2funbody (exp) = ([], exp2term exp)

and valbind2fixbodies (PLAINValBind(
                            ATPat(IDAtPat(_, longvid)@@_)@@_,
                            exp@@_,
                            valbind2)@@_) : G.fixbody list =
    let val ident = lvid2id (~longvid)
        val (binders, body) = fnexp2funbody exp
        val typ = NONE
        val decArg = NONE
        val fixBody = G.Fixbody {id = ident, typ = typ, decArg = decArg, binders = binders, body = body }
    in
        fixBody :: (?valbind2fixbodies valbind2)
    end


(* EXAMPLE: type age = int
 * FROM: SyntaxCoreFn.sml: 123 -> 124
 * TO:   Gallina.sml : 100 -> 108
 * FROM SECTION: Appendix C.1 page 104
 * KEYWORD: typbind/typdesc ---there is a typo in the reference manual
             and typbind is replaced by typdesc
         * TO SECTION: 4.1.4 page 120
         * KEYWORD: definition
         * NOTES:
         * returns sentence list because one typbind can encode multiple
         * gallina definitions e.g. type age = int and name = string
         *)
and typbind2sent(typbind: TypBind) : G.sentence =
    let fun typbind2sents (typbind @@ _) =
            let
                val TypBind(tyvars, tycon, ty, typbind2) = typbind
                val localboolVal = false
                val idVal = tycon2id (~tycon)
                val parametersVal = tyvarseq2binder (List.map ~ ($(~tyvars)))
                val typVal = NONE
                val bodyVal = ty2term (~ty)
                val definition = G.DefinitionDef
                                     {localbool = localboolVal, id = idVal, binders = parametersVal, typ = typVal, body = bodyVal}
                val  res = G.DefinitionSentence (definition)
            in
                res :: ?typbind2sents typbind2
            end
        val sents = typbind2sents typbind
        val sent = G.SeqSentences (!recordContext @ (typbind2sents typbind))
    in (recordContext := []; sent) end


(* EXAMPLE: datatype cards = Hearts | Spades | Clubs | Diamonds
 * FROM: SyntaxCoreFn.sml: 126 -> 127
 * TO:   Gallina.sml : 100 -> 108
 * FROM SECTION: Appendix C.1 page 104
 * KEYWORD: datbind
 * TO SECTION: 4.1.4 page 120
 * KEYWORD: definition
 *)
and datbind2sent(datbind : DatBind) : G.sentence =
    let fun datbind2indbodies (datbind @@ _: DatBind) : G.indBody list =
            let
                val DatBind(tyvars, tycon, cons, datbind2) = datbind
                val idVal = tycon2id (~tycon)
                val parametersVal = tyvarseq2binder (List.map ~ ($(~tyvars)))
                val typVal = mkSortTerm 1
                val clauses = conbind2clauses(cons)
                val clauses = List.map (updateTerm idVal parametersVal) clauses
                val indBody = G.IndBody {id = idVal, bind = parametersVal, typ = typVal, clauses = clauses}
            in 
                indBody :: (?datbind2indbodies (datbind2))
            end 
        val sent = G.InductiveSentence(G.Inductive(datbind2indbodies datbind))
        val recordC = !recordContext
        val _ = recordContext := []
    in
        if recordC = [] then sent else G.SeqSentences (recordC @ [sent])
    end

(* EXAMPLE: 1.  val x = 5
 *          2.  val (x, y) = (1, 2)
 *          3.  val x :: l = [1, 2, 3]
 * FROM: SyntaxCoreFn.sml: 124 -> 126
 * TO:   Gallina.sml : 137 -> 138
 * FROM SECTION: Appendix C.1 page 104
 * KEYWORD: valbind
 * TO SECTION: Section 4.1.4 page 120
 * KEYWORD : definition
 *)
and valbind2sent(valbind: ValBind): G.sentence = 
    let fun valbind2sents (PLAINValBind(pat, exp, valbind2) @@ A) = 
            let
                val exhaustive = isExhaustive A
                val body = exp2term (~exp)
                val pat = pat2pattern (pat)
                val sents = patBody2sents (pat, body) exhaustive
                val sents' = ?valbind2sents valbind2
            in
                !recordContext @ !infixContext @ sents @ sents'
            end
          | valbind2sents (RECValBind(PLAINValBind(
                                           ATPat(IDAtPat(_, longvid)@@_)@@_,
                                           exp@@_,
                                           valbind2)@@_)@@_) =
            let
                val recursive = isSome(valbind2) orelse F.checkExp(lvid2id (~longvid)) exp
                val (binders, body) = fnexp2funbody (exp)
                val binders =  (T.clearTyvars true tyvarCtx) @ binders
                val ident = lvid2id (~longvid)
                val typ = NONE
                val decArg = NONE
                val sent = if recursive
                           then G.FixpointSentence (G.Fixpoint(G.Fixbody
                                                                   {id = ident, typ = typ, decArg = decArg, 
                                                                    binders = binders, body = body}
                                                               :: (?(valbind2fixbodies) valbind2)))
                           else G.DefinitionSentence (G.DefinitionDef
                                                          {id = ident, localbool = false, binders = binders, 
                                                           typ = typ, body = body})
            in
                !recordContext @ !infixContext @ [sent]
            end
        val sent = G.SeqSentences(valbind2sents valbind)
    in (recordContext := []; infixContext := []; sent) end

and binders2ebinders(G.SingleBinder {name = name, typ = SOME typ, inferred = inferred} :: l) =
    G.ESingleBinder {name = name, typ = typ, inferred = inferred } :: (binders2ebinders l)
  | binders2ebinders (G.MultipleBinders {names = names, typ = typ, inferred = inferred} :: l) = 
    (List.map (fn n => G.ESingleBinder{name = n, typ = typ, inferred = inferred}) names) @ (binders2ebinders l)
  | binders2ebinders _ = []


and fundec2eprograms(tyvars : TyVar seq, fvalbind : ValBind) : G.eprograms = 
    let

        (* val tyvars = tyvarseq2binder (List.map ~ ($(~tyvars))) *) (* probably not needed *)
        fun match2econtext(m : Match, arity : int, id) : G.econtext =
            let
                val Match(FmruleX(pat, ty_opt, _)@@_, _)@@annot_m = m
                val _@@annot_pat = pat
                
                (* Type inferred by elaboration *)
                val SOME (_, inferTyp) = !(hd (tl annot_pat))
                val inferTyp = unwrapType (inferTyp, arity)
                
                (* All matched patterns *)
                val pats = matchedPats m
 
                (* Inferred types using type aliases from all patterns *)
                val typs_alias : S.Type list = List.foldl (fn (p, t) => 
                    let
                        val pats = unwrapPat p
                        val n_pats = List.length pats
                    in
                        if n_pats = arity then List.map mkTypeAliased (ListPair.zip (pats, t))
                        else raise Fail "[ERROR] Function pattern with wrong arity."
                    end
                ) inferTyp pats

                (* Bool indicates presence of type variables *)
                val gtypterms : (G.term * bool) list = 
                    List.map (fn t => (typ2typ tyvarCtx t, T.hasTyvars t)) typs_alias

                (* Binders are generically named x1, x2, ... *)
                val ebinders = mkEbinders gtypterms

                val precondsBinders = if isExhaustive annot_m then []
                                      else [PF.findPreconds m] before (funH := id::(!funH))   (* used id to Add funName to the H record *)
            in
                G.EContext (ebinders @ precondsBinders)
            end
        fun match2eclauses(arity: int) (Match(fmrule, match2)@@A : Match) : G.eclause list =
            let
                fun fmrule2eclause (FmruleX(pat, _, exp)) : G.eclause =
                    let
                        val ATPat(TUPLEAtPatX(pats)@@_)@@_ = pat
                        val pats = List.map pat2pattern pats
                        val body = exp2term (~exp)
                    in
                        G.EClause { pats = pats, body = body }
                    end
            in
                fmrule2eclause(~fmrule) :: (? (match2eclauses arity) match2)
            end
        fun fvalbind2eprogram(FValBindX(vid, match, arity, valbind2)@@_ : ValBind) : G.eprogram list =
            let
                val id = vid2id (~vid)
                val Match(FmruleX(pat, ty_opt, _)@@A, _)@@Am = match
                val ret = case ty_opt of
                              SOME ty => ty2term (~ty)
                            | NONE => matchannot2outputtyp tyvarCtx (tl A)
                
                val context = match2econtext(match, arity, id)
                val eclauses = match2eclauses arity match
                (* FIXME: The functions above have the side effect of filling in the type variables context.
                   Since this context is no longer used, it is cleared here, but the side-effect remains
                   implemented for other situations where keeping track of type variables is needed. *)
                val _ = T.clear tyvarCtx
                
                val wildCardClause = if isExhaustive Am
                                     then []
                                     else [G.EClause {pats = List.tabulate(arity, fn _ => G.WildcardPat), body = G.WildcardTerm}]
                val body = G.EClauses (eclauses @ wildCardClause)
            in
                G.EProgram { id = id, context = context, ret = ret, body = body } ::
                (? fvalbind2eprogram valbind2)
            end
    in
        let
            val prog :: mutual = fvalbind2eprogram fvalbind
        in
            G.EPrograms(prog, List.map (fn x => G.EWith x) mutual)
        end
    end




and bool2Prop(t: G.term): G.term = G.InfixTerm(G.IdentTerm("="), [G.Arg(G.TupleTerm([G.TupleTerm([t]), G.IdentTerm("true")]))])


and conts2proofObligation(def: ValBind list, cont: Exp list): G.proofObligation = 
  let

    fun atPat(atpat)    = ATPat(atpat)@@at(atpat)
    fun idAtPat(vid@@A) = IDAtPat(NONE, LongVId.fromId(vid)@@A)@@at(vid@@A)
    fun idPat(vid)      = atPat(idAtPat(vid))

    (* Extract information *)
    val [FValBindX(vid, match, arity, valbind2)@@_] = def
    val Match(FmruleX(pat, ty_opt, _)@@A, _)@@Am = match

    (* pL: list that has the patterns and the last element is the result *)
    val ATPat(TUPLEAtPatX(pL)@@TA)@@PA = pat

    (* function name *)
    val id = (vid2id (~vid))

    (* requires and ensures expressions *)
    val req@@RA = List.hd cont
    val ens@@EA = List.hd (List.tl cont)

    (* vars represents variables in the def. res represents the result in the def*)
    val vars = List.take(pL, (List.length pL) - 1)    
    val [res] = List.drop(pL, (List.length pL) - 1)

    (* We need to convert these bool exps to props *)
    val cHCheck = !exFNum
    val _ = (inThm := true) 
    val reqT = bool2Prop (exp2term req) 
    val ensT = bool2Prop (exp2term ens)
    val _ = (inThm := false)

    (* Check whether the function is exhaustive or not and add Hs to the req and ens*)
    val fHCheck = case List.find (fn x => x = id) (!funH) of SOME x => true | NONE   => false
    val cHCheck = if !exFNum - cHCheck > 0 then true else false

    (* Extract all variables from uncurried terms*)
    fun extractVars pL = 
      case pL of
        (ATPat(TUPLEAtPatX(p2)@@TA)@@PA)::pL' => p2@extractVars(pL')
      | p::pL' => p::extractVars(pL')
      | nil => nil
    val pL = extractVars pL

    (* Add H to the variables if there exist an exhaustive function call in the theorem *)
    val H = idPat((VId.fromString "H")@@nowhere())
    val funBinders = case fHCheck orelse cHCheck of
                      true  => List.map (fn p => List.hd (pat2binders p true)) (pL@[H])
                    | false => List.map (fn p => List.hd (pat2binders p true)) pL

    (* vars binders and res binder *)
    val varBinders = List.map pat2pattern vars
    val resBinder  = pat2pattern res

    (* defintion of the function, (id varBinders = resBinder) is (funName vars = res)*)
    val defTerm = G.DefTerm( id, varBinders, if fHCheck then SOME "H" else NONE, resBinder)

    (* Construct the theorem term *)
    val sentTerm = G.ArrowTerm(G.ConjunctTerm(defTerm, reqT) , ensT)
    val sent = G.ForallTerm(funBinders, sentTerm)
  in
    G.Theorem(id ^ "_THM", sent)
  end


(* FROM: SyntaxCoreFn.sml: 104 -> 114
 * TO:   Gallina.sml : 100 -> 108
 * FROM SECTION: Appendix C.1 page 104
 * KEYWORD: dec
 * TO SECTION: 4.1.4 page 120
 * KEYWORD: sentence
 * NOTES:
 *)
and dec2sent ((TYPEDec(typbind)@@ _) : Dec): G.sentence = typbind2sent typbind
  | dec2sent (DATATYPEDec(datbind)@@_) = datbind2sent datbind
  | dec2sent (DATATYPE2Dec(tycon, ltycon)@@_) =
    G.DefinitionSentence(
        G.DefinitionDef{localbool = false, id = tycon2id(~tycon), binders = [], typ = NONE,
                        body = G.IdentTypTerm(ltycon2id(~ltycon))})
  | dec2sent (VALDec(tyvars, valbind)@@_) = (tyvarCtx := updateTyvarCtx (tyvars) (!tyvarCtx); valbind2sent valbind)
  | dec2sent (FUNDecX((def, conts), tyvars, fvalbind)@@_) = let
      val sent = G.EquationSentence (fundec2eprograms(tyvars, fvalbind))
      val recordC = !recordContext
      val _ = recordContext := []
      val infixC = !infixContext
      val _ = infixContext := []
      val proofObl = case conts of nil => nil | _ => [G.ProofObligationSentence (conts2proofObligation(def, conts))]
    in
        G.SeqSentences (recordC @ infixC @ sent::proofObl)
    end
  | dec2sent (SEQDec(dec1, dec2)@@_) = G.SeqSentences [dec2sent dec1, dec2sent dec2]
  | dec2sent (EMPTYDec@@_) = G.SeqSentences []
  | dec2sent _ = raise Fail "Fail: unsupported"
  (* For debuggin purposes *)
  (*| dec2sent d = (PPCore.ppDec (TextIO.stdOut, 0, d)  ; raise Fail "dec2sent" ) *)
end

end
