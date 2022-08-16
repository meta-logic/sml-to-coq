structure TyvarResolver = 
struct
local
    open SyntaxCore
    open ConvertorUtil
in

structure S = StaticObjectsCore
structure TV = TyVar
structure TN = TyName
structure CU = ConvertorUtil.TT

val tyvarCtx' = ref (TT.empty)


fun resolveType' (tyvarCtx : TT.set) (S.TyVar tyvar : S.Type') : TT.set * G.term option =
    if not (TT.member((!tyvarCtx'), (#name tyvar))) then
        (TT.add(tyvarCtx, (#name tyvar)), SOME (G.IdentTypTerm (checkLegal (#name tyvar))))
    else
        (tyvarCtx, SOME (G.IdentTypTerm (checkLegal (#name tyvar))))
  | resolveType' tyvarCtx (S.ConsType ([], tycon)) =
    (tyvarCtx, SOME (G.IdentTypTerm (#tycon tycon)))
  | resolveType' tyvarCtx (S.ConsType (tyseq, tycon))  =
    let
        fun resolveTySeq (_ : S.Type' ref, (tyvarCtx : TT.set, NONE : (G.term list) option))
            = (tyvarCtx, NONE)
          | resolveTySeq (t, (tyvarCtx, SOME tyseq)) = 
            (case resolveType' tyvarCtx (!t) of
                (_, NONE) => (tyvarCtx, NONE)
              | (tyvarCtx', SOME typ) => (tyvarCtx' ,SOME (typ :: tyseq)))
        val (tyvarCtx', typs) = List.foldr resolveTySeq (tyvarCtx, SOME []) tyseq
    in
        (case typs of
            NONE => (tyvarCtx, NONE)
          | SOME typs => (tyvarCtx', SOME (G.ExplicitTerm (#tycon tycon, typs))))
    end
  | resolveType' tyvarCtx (S.Determined typ) = resolveType tyvarCtx typ
  | resolveType' tyvarCtx (S.Undetermined _) =
    let
        val tyvar = TV.invent false
    in
        ((TT.add(tyvarCtx, (#name tyvar)), SOME (G.IdentTypTerm (checkLegal (#name tyvar)))))
    end
  | resolveType' tyvarCtx (S.FunType(typ1, typ2)) =
    let
        val (ctx, typ1) = resolveType' tyvarCtx (!typ1)
        val (ctx', typ2) = resolveType' ctx (!typ2)
        val typ = case (typ1, typ2) of (SOME typ1, SOME typ2) => SOME (G.ArrowTerm(typ1, typ2))
                                     | _ => NONE
    in
        (ctx', typ)
    end
  | resolveType' tyvarCtx _ = (tyvarCtx, NONE)

and resolveType (tyvarCtx : TT.set) (typ : S.Type) = 
    resolveType' tyvarCtx (!typ)

fun resolveTyvars (tyvarCtx : TT.set ref) (SOME typ : S.Type option) : G.term option =
    let
        val (tyvarContext, typ) = resolveType (!tyvarCtx) typ
    in
        if (TT.isEmpty tyvarContext) orelse not (isSome typ) orelse (TT.isSubset (tyvarContext, !tyvarCtx'))
        then NONE
        else (tyvarCtx' := TT.union((!tyvarCtx'), tyvarContext); tyvarCtx := tyvarContext; typ)
    end
  | resolveTyvars _ _ = NONE


fun getTyvars (SOME typ) =
    getTyvars' typ

and getTyvars' (S.TyVar tyvar) = [G.Name (checkLegal (#name tyvar))]
  | getTyvars' (S.ConsType ([], _)) = []
  | getTyvars' (S.ConsType(tyvars, _)) = List.foldl op@ [] (List.map getTyvars' (List.map ! tyvars))
  | getTyvars' (S.Undetermined _) = []
  | getTyvars' (S.Overloaded _) = []
  | getTyvars' (S.Determined typ) = getTyvars' (!typ)
  | getTyvars' (S.FunType(typ1, typ2)) = (getTyvars' (!typ1)) @ (getTyvars' (!typ2))
  | getTyvars' (S.RowType(typs, _)) = List.foldl op@ [] (List.map getTyvars' (List.map ! (LabMap.listItems typs)))

fun hasTyvars (typ : S.Type) : bool = hasTyvars' (!typ)

and hasTyvars' (S.TyVar tyvar)         = true
  | hasTyvars' (S.ConsType ([], _))    = false
  | hasTyvars' (S.ConsType(tyvars, _)) = List.exists hasTyvars tyvars
  | hasTyvars' (S.Undetermined _)      = false
  | hasTyvars' (S.Overloaded _)        = false
  | hasTyvars' (S.Determined typ)      = hasTyvars typ
  | hasTyvars' (S.FunType(typ1, typ2)) = (hasTyvars typ1) orelse (hasTyvars typ2)
  | hasTyvars' (S.RowType(labmap, _))  = List.exists hasTyvars (LabMap.listItems labmap)

fun isInvented id = String.sub(id, 0) = #"_"

fun union' (ctx' : TT.set, ctx : TT.set) : TT.set =
    TT.union (ctx', TT.filter isInvented ctx)

(* Should this be a real clear? (assign to TT.empty) *)
fun clear (ctx : TT.set ref) : unit = ctx := TT.filter isInvented (!ctx)

fun clearTyvars (discard : bool) (tyvarCtx : TT.set ref) : G.binder list =
    let
        val names = List.map (fn n => G.Name (checkLegal n)) (TT.listItems (!tyvarCtx))
        val union = if discard then union' else TT.union
    in
        case names of
            [] => []
          | _ => (tyvarCtx' := union (!tyvarCtx', !tyvarCtx); tyvarCtx := TT.empty;
                  if discard then clear (tyvarCtx') else ();
                 [G.MultipleBinders { names = names, typ = G.IdentTypTerm ("Type"), inferred = true }])
    end

fun rememberTyvars (tyvarCtx : TT.set ref) : unit =
    tyvarCtx' := union' (!tyvarCtx', !tyvarCtx)

end
end
