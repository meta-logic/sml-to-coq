functor AnnotationExtractor(val recordContext: (Gallina.sentence list) ref; val recordTracker: (Gallina.ident ConvertorUtil.LT.dict) ref) =
struct
open ConvertorUtil
open SyntaxCore
open AnnotationCore

structure S = StaticObjectsCore
structure TN = TyName
structure O = OverloadingClass

fun constyp2typ ctx (typs, tyname) =
    let
        val terms = List.map (typ2typ ctx) typs
        val tycon = checkLegal (TN.toString (tyname))
    in
        (case terms of [] => G.IdentTypTerm tycon | _ => G.ExplicitTerm(tycon, terms))
    end

and rowtyp2sent ctx (body, ident) =
    let 
        val field = G.Field (List.map (fn (id, ty) => (ident ^ "_" ^ checkLegal id, typ2typ ctx ty)) body)
    in
        G.RecordSentence [G.RecordBody {id = ident, binders = [], typ = NONE, consName = NONE, body = [field] }]
    end

and rowtyp2typ ctx (labmap : S.Type' ref S.LabMap, _) =
    let
        val (labs, typs) = ListPair.unzip(LabMap.listItemsi labmap)
        val body = ListPair.zip(labs, typs)
        val labs = orderLabs labs
    in
        if (tupleLabs labs) then G.InScopeTerm (G.ProductTerm (List.map (typ2typ ctx) typs), "type") 
        else
            case LT.find (!recordTracker) labs of
                SOME ident => G.IdentTypTerm (ident)
              | _ => let
                  val id = genIdent ()
                  val _ = recordTracker := LT.insert (!recordTracker) labs id
                  val _ = recordContext := rowtyp2sent ctx (body, id) :: !recordContext
              in
                  G.IdentTypTerm (id)
              end

    end

and typ2typ (ctx : TT.set ref) (typ : S.Type) : G.term =
    case !typ of
        S.TyVar(tyvar) => (ctx := TT.add(!ctx, (#name tyvar));(G.IdentTypTerm (checkLegal (#name tyvar))))
      (* We'll assume this is tuples and not records for now *)
      | S.RowType(rowtyp) => rowtyp2typ ctx (rowtyp)
      | S.FunType(inp, out) => G.ArrowTerm(typ2typ ctx inp, typ2typ ctx out)
      | S.ConsType(constyp) => constyp2typ ctx (constyp)
      | S.Determined typ => typ2typ ctx typ
      | S.Overloaded typ => G.IdentTypTerm(checkLegal (TN.toString (O.default typ)))

fun patannot2inputtyps (ctx : TT.set ref) (arity : int, A : Pat_attr) : G.term list =
    let
        val SOME (_, typ) = !(hd A)
    in
        if arity = 1 then [typ2typ ctx typ]
        else
            let
                val (S.RowType(typs , _)) = !typ
                val typs = LabMap.listItems typs
            in
                List.map (typ2typ ctx) typs
            end
    end

fun matchannot2outputtyp (ctx : TT.set ref) (A : Mrule_attr) : G.term =
    let
        val SOME typ = !(hd A)
        val S.FunType(_, out) = !typ
    in
        typ2typ ctx out
    end



end
