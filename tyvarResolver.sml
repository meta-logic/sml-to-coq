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
    if not (TT.member (!tyvarCtx') (#name tyvar)) then
        (TT.insert tyvarCtx (#name tyvar), SOME (G.IdentTerm (checkLegal (#name tyvar))))
    else
        (tyvarCtx, SOME (G.IdentTerm (checkLegal (#name tyvar))))
  | resolveType' tyvarCtx (S.ConsType ([], tycon)) =
    (tyvarCtx, SOME (G.IdentTerm (#tycon tycon)))
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
        ((TT.insert tyvarCtx (#name tyvar), SOME (G.IdentTerm (checkLegal (#name tyvar)))))
    end
  | resolveType' tyvarCtx _ = (tyvarCtx, NONE)

and resolveType (tyvarCtx : TT.set) (typ : S.Type) = 
    resolveType' tyvarCtx (!typ)

fun resolveTyvars (tyvarCtx : TT.set ref) (SOME typ : S.Type option) : G.term option =
    let
        val (tyvarContext, typ) = resolveType (!tyvarCtx) typ
    in
        if (TT.isEmpty tyvarContext) orelse not (isSome typ) orelse (TT.subset (tyvarContext, !tyvarCtx'))
        then NONE
        else (tyvarCtx' := TT.union (!tyvarCtx') tyvarContext; tyvarCtx := tyvarContext; typ)
    end
  | resolveTyvars _ _ = NONE

fun clearTyvars (tyvarCtx : TT.set ref) : G.binder list =
    let
        val names = List.map (fn n => G.Name (checkLegal n)) (TT.toList (!tyvarCtx))
    in
        case names of
            [] => []
         | _ => (tyvarCtx := TT.empty;
                 [G.MultipleBinders { names = names, typ = G.IdentTerm ("Type"), inferred = true }])
    end
end
end
