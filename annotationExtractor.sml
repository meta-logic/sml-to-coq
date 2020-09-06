structure AnnotationExtractor =
struct
open ConvertorUtil
open SyntaxCore
open AnnotationCore

structure S = StaticObjectsCore
structure TN = TyName
structure O = OverloadingClass

fun constyp2typ(typs, tyname) =
    let
        val terms = List.map typ2typ typs
        val tycon = checkLegal (TN.toString (tyname))
    in
        (case terms of [] => G.IdentTypTerm tycon | _ => G.ExplicitTerm(tycon, terms))
    end

and rowtyp2typ(labmap : S.Type' ref S.LabMap, _) =
    let
        val typs = LabMap.listItems labmap
    in
        G.InScopeTerm (G.ProductTerm (List.map typ2typ typs), "type") 
    end

and typ2typ(typ : S.Type) : G.term =
    case !typ of
        S.TyVar(tyvar) => (G.IdentTerm (#name tyvar))
      (* We'll assume this is tuples and not records for now *)
      | S.RowType(rowtyp) => rowtyp2typ(rowtyp)
      | S.FunType(inp, out) => G.ArrowTerm(typ2typ inp, typ2typ out)
      | S.ConsType(constyp) => constyp2typ(constyp)
      | S.Determined typ => typ2typ typ
      | S.Overloaded typ => G.IdentTerm(checkLegal (TN.toString (O.default typ)))

fun patannot2inputtyps (arity : int, A : Pat_attr) : G.term list =
    let
        val SOME (_, typ) = !(hd A)
    in
        if arity = 1 then [typ2typ typ]
        else
            let
                val (S.RowType(typs , _)) = !typ
                val typs = LabMap.listItems typs
            in
                List.map typ2typ typs
            end
    end

fun matchannot2outputtyp (A : Mrule_attr) : G.term =
    let
        val SOME typ = !(hd A)
        val S.FunType(_, out) = !typ
    in
        typ2typ out
    end



end
