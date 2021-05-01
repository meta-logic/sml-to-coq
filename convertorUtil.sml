structure ConvertorUtil =
struct

    structure G = Gallina
    structure Sort = Quicksort 
    structure Key = ListOrdered(StringOrdered)
    structure LT = SplayDict (structure Key = Key) (* LabelsTracker *)
    structure TT = FinSetFn(type ord_key = string; val compare = String.compare)
(* (structure Elem = StringOrdered) (* Tyvar tracker *) *)
    structure S = StaticObjectsCore
    structure D = DerivedFormsCore
    open Annotation;

    local
        open SyntaxCore
    in
        infix @@;
        val rid_ctr = ref 0 (* record id counter *)
    	(* Sml symbol to Gallina ident. If ident starts with ' it converts it to _
        	Doesn't take care of Gallina reserved words *)
        fun checkLegal (s : string) : G.ident =
            if String.isPrefix "'" s then "_" ^ String.extract(s,1, NONE) else s

        (* Converting SML's ids to Gallina id *)
        fun tycon2id (tycon : TyCon.Id) : G.ident = checkLegal(TyCon.toString tycon)
        fun ltycon2id (tycon : LongTyCon.longId) = checkLegal(LongTyCon.toString tycon)
        fun vid2id (tycon : VId.Id) = checkLegal(VId.toString tycon)
        fun lvid2id (tycon : LongVId.longId) = checkLegal(LongVId.toString tycon)
        fun strid2id (strid : StrId.Id) = checkLegal(StrId.toString strid)
        fun lstrid2id (lstrid : LongStrId.longId) = checkLegal(LongStrId.toString lstrid)
        fun sigid2id (sigid : SigId.Id) = checkLegal(SigId.toString sigid)
        fun funid2id (funid : FunId.Id) = checkLegal(FunId.toString funid)

        (* ? : ('a -> 'b list) * 'a option -> 'b list
           ? f o returns [] if o = NONE and f val if o = SOME val *)
        fun ?exec NONE         = []
          | ?exec (SOME phrase) = exec phrase

        (* $ : 'a SyntaxCore.Seq' -> 'a list *)
        fun $ (Seq l)      = l


        (* ~ : returns the syntax and drops the annotation *)
        fun ~ (x @@ y) = x

        fun % f l = List.map (fn a => f(~a)) l


        fun mkMatchNotationTerm (matcher : G.matchItem,  matchees: G.pattern) (body : G.term, exhaustive : bool) =
            G.MatchNotationTerm {matchItem = matcher, body = G.Equation(matchees, body), exhaustive = exhaustive}
        (* mkSortTerm returns a Prop, Set or Type Gallina terms *)
        fun mkSortTerm (i : int) : G.term =
        	let val typ = case i of  0 => G.Prop
        							| 1 => G.Type
        							| 2 => G.Set
        	in (G.SortTerm typ) end

        (* mkArrowTerm returns a Gallina term representing input -> output *)
        fun mkArrowTerm (input : G.term, output : G.term) : G.term =
            G.ArrowTerm (input, output)

        (* mkName makes a Gallina name *)
        fun mkName (s : string) : G.name = G.Name (checkLegal s)


        fun mkExplicitTerm ((G.IdentTerm term1): G.term) (terms : G.term list) : G.term =
            G.ExplicitTerm (term1, terms)
          | mkExplicitTerm (G.IdentTypTerm term1) terms =
            G.ExplicitTerm (term1, terms)

        fun updateTerm (_ : G.ident) (_: G.binder list) (clause as G.Clause(_, _, NONE) : G.clause) : G.clause
            = clause
            | updateTerm name parametersVal (clause as G.Clause(id, bL, SOME typ)) =
            let
                val terms = List.map (fn (G.SingleBinder{name = G.Name name, ...} )=> G.IdentTypTerm name) parametersVal
                val output = mkExplicitTerm (G.IdentTypTerm name) terms
            in
                G.Clause (id, bL, SOME(mkArrowTerm (typ, output) ) )
            end

        fun mkBinders (terms : G.term list) : G.binder list =
            let
                fun term2binder (G.IdentTerm id) =
                    G.SingleBinder {name = G.Name id, typ = SOME (G.IdentTypTerm "Type"), inferred = true}
                  | term2binder (G.IdentTypTerm id) = 
                    G.SingleBinder {name = G.Name id, typ = SOME (G.IdentTypTerm "Type"), inferred = true}
            in
                List.map term2binder terms
            end

        fun mkEbinders (gtyps : (G.term * bool) list) : G.ebinder list = 
            let
                fun mkEbindersN ([] : (G.term * bool) list, n : int) : G.ebinder list = []
                  | mkEbindersN ((gtyp, hasvars)::rest, n) =
                    let
                        val name = mkName ("x" ^ Int.toString n)
                        val binds = mkEbindersN (rest, n+1)
                    in
                        if hasvars then
                            (* Using pattern binder so that type variables can be generalized *)
                            (G.EPatternBinder { name = name, typ = gtyp}) :: binds
                        else
                            (G.ESingleBinder { name = name, typ = gtyp, inferred = false}) :: binds
                    end
            in
                mkEbindersN (gtyps, 1)
            end


        fun extractTyp (G.SingleBinder {name = G.Name id, ...} : G.binder) : G.term = G.IdentTypTerm id
          | extractTyp _ = raise Fail "Unexpected binder \n"

        fun genIdent () = (rid_ctr := !rid_ctr + 1; "rid_" ^ (Int.toString (!rid_ctr)))

        fun gentyps (n : int) = let 
            fun mkSingleBinder i =
                G.SingleBinder {name = G.Name ("_ty"^ (Int.toString i)),
                                 typ = SOME (G.IdentTypTerm "Type"), inferred = true}
        in
            List.tabulate (n, mkSingleBinder)
        end

        fun opetize (SOME Op : Op option) (id : G.ident) : G.ident = "op" ^ id
          | opetize _ id = id

        fun updateSigBody (G.SigBody(sents)) (id, binders, ty) : G.signatureBody =
            let fun updateSent(sent) =
                    case sent of G.SeqSentences(sents) => G.SeqSentences(List.map updateSent sents)
                               | G.AssumptionSentence(G.Assumption(keyword, id', body)) => 
                                 if id' = id
                                 then G.DefinitionSentence(G.DefinitionDef{localbool = false, id = id, binders = binders, body = ty, typ = NONE})
                                 else sent
                               | _ => sent
            in
                G.SigBody(List.map updateSent sents)
            end

        fun updateTyvarCtx (tyvars : TyVar seq) (tyvarctx : TT.set) : TT.set =
            let
                fun tyvarseq2strings (tyvars: TyVar.TyVar list) : string list = List.map TyVar.toString tyvars
                val tyvars = tyvarseq2strings (List.map ~ ($(~tyvars)))
                fun update [] ctx = ctx
                  | update (tyvar::tyvars) ctx = TT.add ((update tyvars ctx), tyvar)
            in
                update tyvars tyvarctx
            end

        fun orderLabs labs = Sort.sort String.compare (labs)

        fun augmentLabs ident labs = List.map (fn l => ident ^ "_" ^ l) labs

        fun labs2field (labs : G.ident list) (typs : G.binder list) : G.field =
            G.Field (ListPair.zip (labs, List.map extractTyp typs))

        fun mkRecord (labs : G.ident list, ident : G.ident, typs : G.binder list) : G.sentence =
            G.RecordSentence [G.RecordBody { id = ident, binders = typs, typ = NONE,
                                             consName = NONE, body = [labs2field (augmentLabs ident labs) typs]}]

        fun tupleLabs (labs: LabMap.Key.ord_key list) : bool = labs = (List.tabulate (length labs, fn i => (Int.toString (i+1))))

        fun isolate [] = []
          | isolate (x::xs) = x::isolate(List.filter (fn y => y <> x) xs)

        (*fun idFromFixbody (Fixbody (fixbody) : G.fixbody) : G.ident = #id fixbody*)

        (* Every pattern starts with ATPat(TUPLEAtPatX(...)) *)
        fun unwrapPat (ATPat(TUPLEAtPatX(pats)@@_)@@_ : Pat) : Pat list = pats

        (* Removes leading RowType when arity is greater than 1 *)
        fun unwrapType (ref (S.Determined t) : S.Type, arity : int) : S.Type list = unwrapType (t, arity)
          | unwrapType (t as ref (S.RowType (labmap, tyvars)), arity) =
              if arity = 1 then [t]
              else List.tabulate (arity, fn i =>
                  case LabMap.find (labmap, Lab.fromInt (i+1)) 
                    of SOME t => t
                     | NONE => raise Fail "[ERROR] Inferred type has incorrect arity." 
                  )
          | unwrapType (t, _) = [t]

       (* ty2type t1 ==> t2
        * Converts from Ty (hamlet/syntax) to Type (hamlet/elab) 
        *)
        fun ty2type (t1 : Ty) : S.Type = ref (ty2type' (~t1) )

        and ty2type' (VARTy tyvar) = S.TyVar (~tyvar)
          | ty2type' (RECORDTy tyrow_opt) = S.RowType (tyRow2type tyrow_opt)
          | ty2type' (CONTy (tyseq, longTyCon)) = 
              let
                  val Seq(tys) = ~tyseq
                  val types = List.map ty2type tys
                  val name = LongTyCon.toString (~longTyCon)
                  val arity = List.length types
                  (* FIXME: Cannot find out span at this point, using 0 *)
                  val tyname = TyName.tyname(name, arity, true, 0)
              in
                  S.ConsType(types, tyname)
              end
          | ty2type' (ARROWTy(t1, t2)) = S.FunType (ty2type t1, ty2type t2)
          | ty2type' (PARTy ty) = ty2type' (~ty)
          | ty2type' (TUPLETyX tys) = ty2type' (D.TUPLETy' tys)

        and tyRow2type NONE = (LabMap.empty, NONE)
          | tyRow2type (SOME tyrow) =
              let
                  val TyRow(lab, ty, tyrow_opt) = ~tyrow
                  val t = ty2type ty
                  val r = tyRow2type tyrow_opt
              in
                  Type.insertRow (r, ~lab, t)
              end


        (* mergeTypes (t1, t2) ==> t
         * REQUIRES: 
         * - t1 is the type written by the programmer (possibly using type aliases)
         * - t2 is the type inferred during elaboration
         * ENSURES:
         * - t is the type inferred during elaboration with type aliases
         *)
        fun mergeTypes (t1 : Ty, t2 : S.Type) : S.Type = ref (mergeTypes' (~t1, !t2))

        and mergeTypes' (VARTy _ : Ty', t as S.TyVar _ : S.Type') : S.Type' = t
          | mergeTypes' (RECORDTy tyrow_opt, S.RowType row) = mergeRowType (tyrow_opt, row)
          | mergeTypes' (ARROWTy (t1, t2), S.FunType(s1, s2)) = S.FunType (mergeTypes (t1, s1), mergeTypes (t2, s2))
          | mergeTypes' (PARTy t, s) = mergeTypes' (~t, s)
          (* If this is a unary tuple, the inferred type might not be RowType *)
          | mergeTypes' (TUPLETyX [ty], t) = mergeTypes' (~ty, t)
          | mergeTypes' (TUPLETyX tys, S.RowType row) = 
              let
                  val RECORDTy tyrow_opt = D.TUPLETy' tys
              in
                  mergeRowType (tyrow_opt, row)
              end
          | mergeTypes' (CONTy (ty_seq, longtycon), t) = (case t
              (* Inferred type is ConsType, CONTy could be a type alias or not, check name *)
              of S.ConsType (tyvarseq, tyname) => 
                  let
                      val name_syn   = LongTyCon.toString (~longtycon)
                      val name_annot = TyName.toString tyname
                      val new_tyname = TyName.tyname (name_syn, 
                                                      TyName.arity tyname, 
                                                      TyName.admitsEquality tyname, 
                                                      TyName.span tyname)
                  in
                      if (name_syn = name_annot) then t
                      else S.ConsType (tyvarseq, new_tyname)
                  end
               (* Inferred type is not ConsType, this is definitely a type alias *)
               | _ => let
                      val name = LongTyCon.toString (~longtycon)
                      (* FIXME: the fields arity, admitsEquality, and span are a guess at best *)
                      val Seq l    = ~ty_seq
                      val arity    = List.length l
                      val admitsEq = false
                      val span     = 0
                      val tyname   = TyName.tyname (name, arity, admitsEq, span)

                      val ty_list = List.map ty2type l
                  in
                    S.ConsType (ty_list, tyname)
                  end
              )
          | mergeTypes' (t1, t2) = raise Fail "[ERROR] Explicit and inferred types do not match."

        and mergeRowType (tyrow_opt : TyRow option, (labmap, tyvars)) = 
            let
                fun collectPairs NONE = []
                  | collectPairs (SOME ((TyRow (lab, ty, opt))@@_)) = (~lab, ty) :: collectPairs opt

                fun mergeRowTypes' ([], labmap) = labmap
                  | mergeRowTypes' ((lab, ty)::tl, labmap) = 
                      let
                          val ty_annot = case LabMap.find (labmap, lab)
                                           of NONE => raise Fail "[ERROR] Explict and inferred types have different labels." 
                                            | SOME t => t
                          val merged_ty = mergeTypes (ty, ty_annot)
                          val updated_map = LabMap.insert(labmap, lab, merged_ty)
                      in
                          mergeRowTypes' (tl, updated_map)
                      end

                val row_syn = collectPairs tyrow_opt
                val n1 = LabMap.numItems labmap
                val n2 = List.length row_syn
              in
                  if (n1 = n2) then S.RowType (mergeRowTypes' (row_syn, labmap), tyvars)
                  else raise Fail "[ERROR] Explicit and inferred types have different arity."
              end
         
        (* Reconstructs type based on what was written explicitly in a pattern *)
        fun mkTypeAliased (p: Pat, t : S.Type) : S.Type = ref (mkTypeAliased' (~p, !t))

        and mkTypeAliased' (ATPat atPat, t) : S.Type' = mkTypeAliased'' (~atPat, t)
          | mkTypeAliased' (COLONPat(_, ty1), ty2) = ! (mergeTypes (ty1, ref ty2))
          | mkTypeAliased' (ASPat(_, _, SOME ty1, _), ty2) = ! (mergeTypes (ty1, ref ty2))
          | mkTypeAliased' (ASPat(_, _, NONE, pat), t) = mkTypeAliased' (~pat, t)
          (* The types of CONPat and INFIXPatX are a type constructor. 
             Type aliases used inside these constructors are not replaced.
             E.g.:
             datatype t = T of int * bool 
             fun f (T (x : int, y)) = 0
             ==> The explicit type on x will be lost as it is not supported in Coq.
          *)
          | mkTypeAliased' (CONPat(_, _, atPat), t as S.ConsType _) = t
          | mkTypeAliased' (INFIXPatX(_, _, atPat), t as S.ConsType _) = t
          | mkTypeAliased' _ = raise Fail "[ERROR] Cannot combine pattern with type."

        and mkTypeAliased'' (PARAtPat pat, t) : S.Type' = mkTypeAliased' (~pat, t)
          | mkTypeAliased'' (RECORDAtPat patrow_opt, S.RowType (labmap, tyvars)) =
              let
                  fun collectPats NONE = []
                    | collectPats (SOME (DOTSPatRow@@_)) = []
                    | collectPats (SOME ((FIELDPatRow (lab, pat, patrow_opt)@@_))) = (~lab, pat) :: collectPats patrow_opt

                  val pats = collectPats patrow_opt
                  val updated_map = List.foldl (fn ((lab, pat), lm) =>
                      let
                          val ty = case LabMap.find (lm, lab)
                                     of NONE => raise Fail "[ERROR] Record pattern and type have different labels." 
                                      | SOME t => t
                          val new_ty = mkTypeAliased' (~pat, !ty)
                      in
                          LabMap.insert (lm, lab, ref new_ty)
                      end
                  ) labmap pats
              in
                S.RowType (updated_map, tyvars)
              end
          | mkTypeAliased'' (TUPLEAtPatX patList, S.RowType(labmap, tyvars)) = 
              let
                  val n_pat = List.length patList
                  val n_tys = LabMap.numItems labmap

                  fun update_map ([], _) = labmap 
                    | update_map (p :: ps, i) = 
                        let
                            val l = Lab.fromInt i
                            val ty = case LabMap.find (labmap, l)
                                       of NONE => raise Fail "[ERROR] Incorrect numbered labels for tuple pattern."
                                        | SOME t => t
                            val new_ty = mkTypeAliased' (~p, !ty)
                            val new_map = update_map (ps, i+1)
                        in
                            LabMap.insert (new_map, l, ref new_ty)
                        end
              in
                  case n_pat = n_tys
                    of false => raise Fail "[ERROR] Number of patterns in tuple and types do not match."
                     | true  => S.RowType (update_map (patList, 1), tyvars)
              end
          | mkTypeAliased'' (LISTAtPatX patList, S.RowType(labmap, tyvars)) = 
              let
                  val n_pat = List.length patList
                  val n_tys = LabMap.numItems labmap

                  fun update_map ([], _) = labmap 
                    | update_map (p :: ps, i) = 
                        let
                            val l = Lab.fromInt i
                            val ty = case LabMap.find (labmap, l)
                                       of NONE => raise Fail "[ERROR] Incorrect numbered labels for tuple pattern."
                                        | SOME t => t
                            val new_ty = mkTypeAliased' (~p, !ty)
                            val new_map = update_map (ps, i+1)
                        in
                            LabMap.insert (new_map, l, ref new_ty)
                        end
              in
                  case n_pat = n_tys
                    of false => raise Fail "[ERROR] Number of patterns in list and types do not match."
                     | true  => S.RowType (update_map (patList, 1), tyvars)
              end
          (* The other cases do not have types inside them *)
          | mkTypeAliased'' (_, t) = t


        (* Collects the patterns (with annotations) used in every case of a match *)
        fun matchedPats (Match(fmrule, rest)@@_ : Match) :  Pat list = 
            let
                val FmruleX(pat, _, _) = ~fmrule
            in
                pat :: (? matchedPats rest)
            end

    end    	
end
