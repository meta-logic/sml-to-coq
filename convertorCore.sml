(*
 * Converting hamlet/syntax/SyntaxCoreFn.sml and hamlet/syntax/TyVar.sml
 * For each function we provide the following:
 * EXAMPLE: an SML code example
 * FROM: hamlet file source code line numbers
 * TO:   gallina.sml source code line numbers
 * FROM SECTION: section and page number in Hamlet's documentation (if appliicable)
 * KEYWORD: keyword in Hamlet's documentation (if applicable)
 * TO SECTION: section and page number in Coq's documentation (if applicable)
 * KEYWORD: keyword in Coq's documentation (if applicable)
 * NOTES: additional notes
 *)
structure ConvertorCore = 
struct
    open ConvertorUtil
    open SyntaxCore    
    open AnnotationCore
    structure S = StaticObjectsCore
    structure D = DynamicObjectsCore
    local 
        structure G = Gallina
        infix @@
        infix ==>
    in
        exception WildCard

        val recordContext = ref [] : (G.sentence list) ref
        val recordTracker = ref (LT.empty) : (G.ident LT.dict) ref

        (* FROM: Scon.sml: 15 -> 20
         * TO:   Gallina.sml : 16 -> 53 
         * FROM SECTION: -
         * TO SECTION: 4.1.3 page 115
         * KEYWORD: term
         *)
        fun scon2term (SCon.STRING s : SCon.SCon) : G.term = G.StringTerm s
            | scon2term (SCon.CHAR s) = G.CharTerm s
            | scon2term (SCon.REAL s) = G.RealTerm s
            | scon2term (SCon.INT (b, s)) = if b = SCon.DEC then G.NumTerm s else G.HexTerm s
            (* Need to check what's a word constant *)
            | scon2term (SCon.WORD (b, s)) = if b = SCon.DEC then G.WordTerm (s, G.Dec) else G.WordTerm (s, G.Hex)

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

        and exprow2body (ExpRow(lab, exp, exprow') @@ _) = (~lab, ~exp) :: ?exprow2body exprow'

        and expbody2labs body = Sort.sort String.compare (#1(ListPair.unzip body))

        and expbody2fields body = let
            fun expbody2field (lab, exp) = G.FieldDef {id = checkLegal lab, binders = [], term = exp2term exp }
        in List.map expbody2field body end

        and patrow2body (FIELDPatRow(lab, pat, patrow') @@ _) =
            let
                val (lab, pat) = (~lab, pat2pattern (~pat))
                val body = (lab, pat) :: ?patrow2body patrow'
                val labs = patbody2labs body
                val keys = LT.domain (!recordTracker)
            in
                case LT.find (!recordTracker) labs of
                    SOME _ => body
                  | NONE => case List.find (fn l => List.exists (fn x => x = lab) l) keys of
                                NONE => raise Fail "Record pattern undefined \n"
                              | SOME labs' => List.map (fn l => case List.find (fn x => #1(x) = l) body of
                                                                    SOME res => res
                                                                 |  _ => (l, G.WildcardPat)) labs'
            end
          | patrow2body  _ = []

        and patbody2labs body = Sort.sort String.compare (#1(ListPair.unzip body))

        and patbody2fields body = let
            fun patbody2field (lab, pat) = G.FieldPat {id = checkLegal lab, binders = [], pat = pat}
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
                G.IdentTerm (checkLegal(TyVar.toString (~tyvar)))
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
                (case terms of [] => G.IdentTerm tycon | _ => G.ExplicitTerm(tycon, terms))
            end
            (* PARTy is parenthesis type, e.g. (int)  *)
            | ty2term (PARTy ty) = G.ParensTerm (ty2term (~ty))
            (* ARROWTy is arrow type, e.g. int -> int  *)
            | ty2term (ARROWTy(ty1, ty2)) = G.ArrowTerm(ty2term (~ty1), ty2term (~ty2))
            | ty2term (RECORDTy recBody) = let
                val body = ?tyrow2body recBody
                val labs = tybody2labs body
            in
                case LT.find (!recordTracker) labs of
                    SOME ident => G.IdentTerm (ident)
                  | _ => let
                      val id = genIdent ()
                      val _ = recordTracker := LT.insert (!recordTracker) labs id
                      val _ = recordContext := tyrow2sent (body, id) :: !recordContext
                  in
                      G.IdentTerm (id)
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
                val pattern = pat2pattern (~ pat)
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
                val equation2 = case (try (exhaustive A)) of 
                                    SOME S.Exhaustive => []
                                    | _ => [G.Equation(G.WildcardPat, G.Axiom G.PatternFailure)]
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
        and atexp2args (atexp : AtExp') : G.arg list = [G.Arg (atexp2term atexp)]

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
            | sentterm2letTerm _ =raise Fail "Translating this sentence to let is invalid/Unimplemented \n"        

      (* FROM: SyntaxCoreFn.sml: 71 -> 79
       * TO:   Gallina.sml: 21 -> 62
       * FROM SECTION: Appendix C.1 page 102
       * KEYWORD: atexp
       * TO SECTION: Section 4.1.3 Page 115
       * KEYWORD: term
       *)
        and atexp2term (SCONAtExp scon : AtExp') : G.term = scon2term (~scon)
            (* ignoring Op for now *)
            | atexp2term (IDAtExp (_, longvid)) = G.IdentTerm (lvid2id (~longvid))
            | atexp2term (RECORDAtExp recBody) = let
                val body = ?exprow2body recBody
                val labs = expbody2labs body
            in
                case LT.find (!recordTracker) labs of
                    SOME ident => G.RecordTerm (expbody2fields body)
                  | NONE => let
                      val id = genIdent ()
                      val typs = gentyps (List.length labs)
                      val _ = recordTracker := LT.insert (!recordTracker) labs id
                      val _ = recordContext := exprow2sent (labs, id, typs) :: !recordContext
                  in
                      G.RecordTerm (expbody2fields body)
                  end
            end
            | atexp2term (LETAtExp (dec, exp)) = 
                let
                    val sent = dec2sent dec
                    val term = exp2term (~exp)
                in
                    sentterm2letTerm (sent, term)
                end
            | atexp2term (PARAtExp exp) = G.ParensTerm (exp2term (~exp))
            | atexp2term (UNITAtExpX) = G.UnitTerm 
            (* in scope term because the operator "*" is overloaded *)
            | atexp2term (TUPLEAtExpX(exps)) = G.TupleTerm(% exp2term exps)
            | atexp2term (LISTAtExpX(exps)) = G.ListTerm(% exp2term exps)


      (* FROM: SyntaxCoreFn.sml: 84 -> 94
       * TO:   Gallina.sml: 21 -> 62
       * FROM SECTION: Appendix C.1 page 102
       * KEYWORD: exp
       * TO SECTION: Section 4.1.3 Page 115
       * KEYWORD: term
       *)
        and exp2term (ATExp atexp : Exp') : G.term = atexp2term (~atexp)
            | exp2term (APPExp (exp, atexp)) = 
                G.ApplyTerm(exp2term (~exp), atexp2args (~atexp))
            | exp2term (COLONExp (exp, ty)) = 
              let val typ = ty2term (~ty)
                  val exp = exp2term (~exp)
              in G.HasTypeTerm(exp, typ) end
            | exp2term (FNExp match) = raise Fail "Function expressions not yet implemented!\n"
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
              G.InfixTerm (exp2term (~exp), atexp2args (~atexp))


      (* FROM: SyntaxCoreFn.sml: 144 -> 152
       * TO:   Gallina.sml : 96 -> 114
       * FROM SECTION: Appendix C.1 page 103
       * KEYWORD: atpat
       * TO SECTION: Section 4.1.3 Page 115
       * KEYWORD: pattern
       *)
        and atpat2pattern (WILDCARDAtPat : AtPat') : G.pattern = G.WildcardPat
            | atpat2pattern (SCONAtPat scon) = scon2pattern (~scon)
            (* ignoring Op for now *)
            | atpat2pattern (IDAtPat (_, longvid)) = G.QualidPat (lvid2id (~longvid))
            | atpat2pattern (RECORDAtPat recBody) = let
                val body = ?patrow2body recBody
            in
                if List.length body = 0 then G.WildcardPat 
                else G.RecPat (patbody2fields body)
            end
            | atpat2pattern (PARAtPat pat) = G.ParPat (pat2pattern (~pat))
            | atpat2pattern UNITAtPatX = G.UnitPat
            | atpat2pattern (TUPLEAtPatX pats) = G.TuplePat (% pat2pattern pats)
            | atpat2pattern (LISTAtPatX pats) = G.ListPat (% pat2pattern pats)

      (* FROM: SyntaxCoreFn.sml: 159 -> 163
       * TO:   Gallina.sml : 96 -> 114
       * FROM SECTION: Appendix C.1 page 103
       * KEYWORD: pat
       * TO SECTION: Section 4.1.3 Page 115
       * KEYWORD: pattern
       *)
        and pat2pattern (ATPat atpat  : Pat') : G.pattern = atpat2pattern (~ atpat)
            (* ignoring Op for now *)
            | pat2pattern (CONPat (_, longvid, atpat)) = G.ArgsPat (lvid2id (~longvid), [atpat2pattern (~ atpat)])
            | pat2pattern (COLONPat (pat, ty)) = let 
                val _ = print "Coq doesn't support type casting in patterns!\n" 
                in pat2pattern(~pat) end
            (* ignoring Op for now *)
            | pat2pattern (ASPat(_, vid, ty, pat)) = 
                let 
                    val _ = if Option.isSome ty then print "Coq doesn't support type casting in patterns!\n" 
                            else () 
                in G.AsPat(pat2pattern(~ pat), vid2id (~vid)) end
            | pat2pattern (INFIXPatX (_, longvid, atpat)) = G.InfixPat (lvid2id (~longvid), [atpat2pattern (~atpat)])

      (* Helper function doesn't have corresponding sections, check valBind2sent *)
        and patBody2sents (G.QualidPat ident : G.pattern, body : G.term) (_ : bool): G.sentence list = 
                [G.DefinitionSentence
                    (G.DefinitionDef
                           {localbool = false, id = ident, binders = [], typ = NONE, body = body})]
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
          | patBody2sents' _ _ = raise Fail "Invalid pattern!\n"

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

        and tyrow2sent (body : (G.ident * Ty') list, ident : G.ident) : G.sentence =
            G.RecordSentence [G.RecordBody {id = ident, binders = [], typ = NONE,
                                            consName = NONE, body = [tyrow2field body] }]

        and tyrow2field (body : (G.ident * Ty') list) : G.field =
            G.Field (List.map (fn (id, ty) => (checkLegal id, ty2term ty)) body)

        and exprow2sent (labs : G.ident list, ident : G.ident, typs : G.binder list) : G.sentence =
            G.RecordSentence [G.RecordBody { id = ident, binders = typs, typ = NONE,
                                             consName = NONE, body = [labs2field labs typs]}]


        and labs2field (labs : G.ident list) (typs : G.binder list) : G.field =
            G.Field (ListPair.zip (labs, List.map extractTyp typs))


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
                    val exhaustive = case try (exhaustive A) of SOME S.Exhaustive => true | _ => false                    
                    val body = exp2term (~exp)
                    val pat = pat2pattern (~pat)
                    val sents = patBody2sents (pat, body) exhaustive
                in
                    !recordContext @ sents @ (?(valbind2sents) valbind2)
                end
                | valbind2sents _ = raise Fail "Recursive value bindings are not yet implemented \n"    
                val sent = G.SeqSentences(valbind2sents valbind)
            in (recordContext := []; sent) end



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
            (* ignoring tyvarseq for now (function declarations) *)
            | dec2sent (VALDec(tyvarseq, valbind)@@_) = valbind2sent valbind
            | dec2sent _ = raise Fail "Unimplemented declaration! \n"
    end 
end
