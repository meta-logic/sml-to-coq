(*
 * Converting hamlet/syntax/SyntaxModuleFn.sml
 * For each function we provide the following:
 * FROM: hamlet file source code line numbers
 * TO:   gallina.sml source code line numbers
 * FROM SECTION: section and page number in Hamlet's documentation (if appliicable)
 * KEYWORD: keyword in Hamlet's documentation (if applicable)
 * TO SECTION: section and page number in Coq's documentation (if applicable)
 * KEYWORD: keyword in Coq's documentation (if applicable)
 *)
structure ConvertorModule =
struct
    open SyntaxModule
	open ConvertorCore
    local
		structure G = Gallina
		infix @@
	in

  val cxt = ref [] : (G.sentence list) ref

  fun spec2id (spec : Spec') : G.ident =
      let
          val sigid = sigid2id(SigId.invent())
          val _ = cxt := !cxt @ [G.SignatureSentence(spec2signature(sigid, spec))]
      in sigid end

  and valdesc2sent(valdesc : ValDesc') : G.sentence =
      let fun valdesc2sents(ValDesc(vid, ty, valdesc2)) =
              let
                  val sent = G.AssumptionSentence (G.Assumption (G.Parameter, vid2id(~vid), ty2term(~ty)))
                  val sents = sent :: ? (fn x => valdesc2sents(~x)) (valdesc2)
              in
                  sents
              end
      in
          G.SeqSentences(valdesc2sents valdesc)
      end

  and typdesc2sent(typdesc : TypDesc') : G.sentence =
      let fun typdesc2sents(TypDesc(tyvars, tycon, typdesc2)) =
              let
                  val tyvars = $(~tyvars)
                  fun tyvars2typ [] = G.SortTerm(G.Type)
                    | tyvars2typ (tyvar :: tyvars) = G.ArrowTerm(G.SortTerm(G.Type), tyvars2typ tyvars)
                  val typ = tyvars2typ tyvars
                  val sent = G.AssumptionSentence (G.Assumption (G.Parameter, tycon2id(~tycon), typ))
                  val sents = sent :: ? (fn x => typdesc2sents(~x)) (typdesc2)
              in
                  sents
              end
      in
          G.SeqSentences(typdesc2sents typdesc)
      end

  and datdesc2sent(datdesc : DatDesc') : G.sentence = 
      let fun datdesc2indbodies(DatDesc(tyvars, tycon, condesc, datdesc2)) =
              let
                  val id = tycon2id (~tycon)
                  val parameters = tyvarseq2binder (List.map ~ ($(~tyvars)))
                  val typ = mkSortTerm 1
                  val clauses = condesc2clauses(~condesc)
                  val clauses = List.map (updateTerm id parameters) clauses
                  val indBody = G.IndBody {id = id, bind = parameters, typ = typ, clauses = clauses}
              in
                  indBody :: (? (fn x => datdesc2indbodies (~x)) datdesc2)
              end
          val sent = G.InductiveSentence(G.Inductive(datdesc2indbodies datdesc))
      in
          sent
      end


  and condesc2clauses(ConDesc(vid, ty, condesc2): ConDesc') : G.clause list =
      let
          val id = vid2id(~vid)
          val binders = []
          val typ = (case ty of SOME ty' => SOME(ty2term(~ty')) 
                             |  _ => NONE)
          val clauses = ? (fn x => condesc2clauses(~x)) condesc2
          val clause = G.Clause(id, binders, typ)
      in
          clause :: clauses
      end

  and strdesc2sent(strdesc : StrDesc') : G.sentence =
      let fun strdesc2sents(StrDesc(strid, sigexp, strdesc2)) =
              let
                  val id = strid2id(~strid)
                  val typ = sigexp2moduleTyp(~sigexp)
                  val sent = G.DeclareModuleSentence (G.Declare {id = id, bindings = [], typ = typ})
                  val sents = sent :: ? (fn x => strdesc2sents(~x)) (strdesc2)
              in
                  sents
              end
      in
          G.SeqSentences(strdesc2sents strdesc)
      end

  and syndesc2sents([] : (TyVar seq * TyCon * Ty) list) : G.sentence list = []
    | syndesc2sents((tyvars, tycon, ty) :: syndescs)  = 
      let
          val id = tycon2id(~tycon)
          val binders = tyvarseq2binder (List.map ~ ($(~tyvars)))
          val body = ty2term(~ty)
      in
          (G.DefinitionSentence(G.DefinitionDef{localbool = false, id = id, binders = binders, typ = NONE, body = body})) :: syndesc2sents syndescs
      end

  and spec2signature (sigid, spec : Spec') : G.gsignature =
      let
          fun spec2sents (VALSpec(valdesc)) : G.sentence list = [valdesc2sent(~valdesc)]
            | spec2sents (TYPESpec(typdesc)) = [typdesc2sent(~typdesc)]
            | spec2sents (DATATYPESpec(datdesc)) = [datdesc2sent(~datdesc)]
            | spec2sents (STRUCTURESpec(strdesc)) = [strdesc2sent(~strdesc)]
            | spec2sents (EMPTYSpec) = []
            | spec2sents (SEQSpec(spec1, spec2)) = spec2sents(~spec1) @ spec2sents(~spec2)
            | spec2sents (INCLUDESpec(sigexp)) = [G.IncludeSentence(G.Include(sigexp2moduleTyp(~sigexp)))]
            | spec2sents (SYNSpecX(syndesc)) = syndesc2sents(~syndesc)
          val body = G.SigBody(spec2sents spec)
      in
          G.ISignature {id = sigid, bindings = [], body = body}
      end

  and sigexp2moduleTyp (SIGSigExp(spec) : SigExp' ) : G.moduleTyp = G.SigName (spec2id(~spec))
    | sigexp2moduleTyp (IDSigExp(sigid)) = G.SigName (sigid2id(~sigid))
    | sigexp2moduleTyp (WHERETYPESigExp(sigexp, tyvars, ltycon, ty)) =
      let
          val modtyp = sigexp2moduleTyp(~sigexp)
          val id = ltycon2id(~ltycon)
          val tyvars = tyvarseq2binder (List.map ~ ($(~tyvars)))
          val ty = ty2term(~ty)
          val defBody = if tyvars = [] then ty else
                        G.FunTerm(tyvars, ty)
          val withdecl = G.WithTyp(G.DefinitionDef {localbool = false, id = id, binders = [], typ = NONE, body = defBody})
      in
          G.SigType(modtyp, withdecl)
      end


  and sigexp2ofmoduleTyp(sigexp : SigExp', true : bool) : G.ofModuleTyp = G.OpaqueSig (sigexp2moduleTyp sigexp)
    | sigexp2ofmoduleTyp (sigexp, false) = G.TransparentSig (sigexp2moduleTyp sigexp)

  and strexp2id (strexp : StrExp') : G.ident =
      let
          val strid = strid2id(StrId.invent())
          val _ = cxt := !cxt @ [G.ModuleSentence(strexp2module(strid, strexp))]
      in strid end

  and strexp2module (strid, STRUCTStrExp(strdec)) : G.module =
      let
          val id = strid
          val typ = NONE
          val bindings = []
          val body = G.ModuleBody ([strDec2sents strdec])
      in
          G.IModule { id = id, typ = typ, bindings = bindings, body = body }
      end
    | strexp2module (strid, IDStrExp(lstrid)) = G.Module { id = strid, typ = NONE, bindings = [], body = G.ModuleName(lstrid2id (~lstrid)) }
    | strexp2module (strid, COLONStrExp(strexp, sigexp)) =
      (case strexp2module (strid, ~strexp) of
          G.Module { id = id, body = body, ... } =>
          G.Module { id = id, body = body, typ = SOME (sigexp2ofmoduleTyp(~sigexp, false)), bindings = [] }
        | G.IModule { id = id, body = body, ... } =>
          G.IModule { id = id, body = body, typ = SOME (sigexp2ofmoduleTyp(~sigexp, false)), bindings = []})
    | strexp2module (strid, SEALStrExp(strexp, sigexp)) =
      (case strexp2module(strid, ~strexp) of
           G.Module {id = id, body = body, ... } =>
           G.Module { id = id, body = body, typ = SOME (sigexp2ofmoduleTyp(~sigexp, true)), bindings = []}
         | G.IModule {id = id, body = body, ... } =>
           G.IModule { id = id, body = body, typ = SOME (sigexp2ofmoduleTyp(~sigexp, true)), bindings = []})
    | strexp2module (strid, APPStrExp(funid, strexp)) =
      let
          val id = strid
          val typ = NONE
          val bindings = []
          val body = G.FunctorName [(funid2id(~funid)), strexp2id(~strexp) ]
      in
          G.Module { id = id, typ = typ, bindings = bindings, body = body }
      end

  and sigexp2signature (sigid, SIGSigExp(spec)) : G.gsignature = spec2signature(sigid, ~spec)
    | sigexp2signature (sigid, IDSigExp(sigid')) = G.Signature {id = sigid, bindings = [], body = G.SigName(sigid2id(~sigid'))}
    | sigexp2signature (sigid, WHERETYPESigExp(sigexp, tyvars, ltycon, ty)) =
      let
          val gsignature = sigexp2signature(sigid, ~sigexp)
          val id = ltycon2id(~ltycon)
          val tyvars = tyvarseq2binder (List.map ~ ($(~tyvars)))
          val ty = ty2term (~ty)
          val defBody = if tyvars = [] then ty else
                        G.FunTerm(tyvars, ty)
          val withdecl = G.WithTyp(G.DefinitionDef {localbool = false, id = id, binders = [], typ = NONE, body = defBody})
      in
          case gsignature of
              G.ISignature{body = body, id = id', bindings = bindings} =>
              G.ISignature{body = updateSigBody body (id, tyvars, ty), id = id', bindings = bindings}
            | G.Signature {body = body, id = id, bindings = bindings} =>
              G.Signature {body = G.SigType(body, withdecl), id = id, bindings = bindings}
      end


  and strbind2sent (strbind : StrBind) : G.sentence =
      let fun strbind2sents (StrBind(strid, strexp, strbnd2)@@_) =
              let
                  val id = strid2id (~strid)
                  val module = strexp2module (id, ~strexp)
                  val sent = G.ModuleSentence module
                  val context = !cxt
                  val _ = cxt := []
                  val sents =  ?strbind2sents strbnd2
              in
                  context @ (sent :: sents)
              end
      in
          G.SeqSentences (strbind2sents strbind)
      end

  and sigbind2sent (sigbind : SigBind) : G.sentence =
      let fun sigbind2sents(SigBind(sigid, sigexp, sigbind2)@@_) =
              let
                  val id = sigid2id(~sigid)
                  val gsignature = sigexp2signature(id, ~sigexp)
                  val sent = G.SignatureSentence gsignature
                  val sents = ?sigbind2sents sigbind2
              in
                  sent :: sents
              end
      in
          G.SeqSentences (sigbind2sents sigbind)
      end

  and funbind2sent (funbind : FunBind) : G.sentence =
      let fun funbind2sents(FunBind(funid, strid, sigexp, strexp, funbind2)@@_) =
              let
                  val funid = funid2id(~funid)
                  val strid = strid2id(~strid)
                  val moduletyp = sigexp2moduleTyp(~sigexp)
                  val module = strexp2module (funid, ~strexp)
                  val bindings = [G.ModuleBinding(NONE, [strid], moduletyp)]
                  val sent = (case module of
                                  G.IModule {bindings = _, id = id, typ = typ, body = body} =>
                                  G.ModuleSentence (G.IModule{bindings = bindings, id = id, typ = typ, body = body})
                                | G.Module{bindings = _, id = id, typ = typ, body = body} =>
                                  G.ModuleSentence (G.Module{bindings = bindings, id = id, typ = typ, body = body}))
                  val context = !cxt
                  val _ = cxt := []
                  val sents = ?funbind2sents funbind2
              in
                  context @ (sent :: sents)
              end
            | funbind2sents (SPECFunBindX(funid, spec, strexp, funbind2)@@_) = 
              let
                  val funid = funid2id(~funid)
                  val sigid = spec2id (~spec)
                  val moduletyp = G.SigName(sigid)
                  val strid = strid2id(StrId.invent())
                  val module = strexp2module(funid, ~strexp)
                  val bindings = [G.ModuleBinding(SOME G.Import, [strid], moduletyp)]
                  val sent = (case module of
                                  G.IModule {bindings = _, id = id, typ = typ, body = body} =>
                                  G.ModuleSentence (G.IModule{bindings = bindings, id = id, typ = typ, body = body})
                                | G.Module{bindings = _, id = id, typ = typ, body = body} =>
                                  G.ModuleSentence (G.Module{bindings = bindings, id = id, typ = typ, body = body}))
                  val context = !cxt
                  val _ = cxt := []
                  val sents = ?funbind2sents funbind2
              in
                  context @ (sent :: sents)
              end
      in
          G.SeqSentences (funbind2sents funbind)
      end

	(* FROM: SyntaxModuleFn.sml: 72 -> 76
	 * TO:   Gallina.sml : 121 -> 128
	 * FROM SECTION: Appendix C.2 page 106
	 * KEYWORD: strdec
	 * TO SECTION: Section 3.1.4 Page 30
	 * KEYWORD: sentence
	 *)
	and strDec2sents (DECStrDec(strDec) @@ _ : StrDec) : G.sentence = dec2sent strDec
    | strDec2sents (STRUCTUREStrDec(strbnd)@@_) = strbind2sent strbnd
    | strDec2sents (EMPTYStrDec@@_) = G.SeqSentences []
    | strDec2sents (SEQStrDec(strdec1, strdec2)@@_) =
      G.SeqSentences (strDec2sents(strdec1) :: [strDec2sents(strdec2)])

  and sigDec2sents (SigDec(sigbind) @@ _ : SigDec) : G.sentence = sigbind2sent sigbind

  and funDec2sents (FunDec(funbind)@@_ : FunDec) : G.sentence = funbind2sent funbind

  (* FROM: SyntaxModuleFn.sml: 142 -> 145
	 * TO:   Gallina.sml : 121 -> 128
   * FROM SECTION: Appendix C.2 page 106
	 * KEYWORD: topdec
	 * TO SECTION: Section 3.1.4 Page 30
	 * KEYWORD: sentence
	 *)	
	and topDec2sents (STRDECTopDec(strdec, topdec2) @@ _ : TopDec) : G.sentence list =
	    (strDec2sents strdec) :: (?(topDec2sents) topdec2)
		| topDec2sents (SIGDECTopDec(sigdec, topdec2)@@_) =
      (sigDec2sents sigdec) :: (?(topDec2sents) topdec2)
    | topDec2sents (FUNDECTopDec(fundec, topdec2)@@_) =
      (funDec2sents fundec) :: ((?topDec2sents) topdec2)
	end
end
