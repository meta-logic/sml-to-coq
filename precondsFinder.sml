functor PrecondsFinder(val scon2term : SCon.SCon -> Gallina.term) =
struct
open ConvertorUtil
open SyntaxCore
open AnnotationCore
local
infix @@
in

structure S = StaticObjectsCore
structure TN = TyName
structure G = Gallina

datatype arg = Generic
             | Const of string * arg list
             | SCon of SCon.SCon
             | ListConst of arg list (* shortcut *)
             | InfixConst of string * (arg * arg)
             (* | Args of arg list *)

type args = (arg list) list

fun getTyName(typ : S.Type) : S.TyName =
    case !typ of
        S.Determined typ => getTyName typ
      | S.ConsType (_, tyname) => tyname

fun span(A : Pat_attr) : int =
    let
        val SOME (_, typ) = !(hd A)
        val tyname = getTyName (typ)
    in
        TN.span tyname
    end

fun toString lvid = LongVId.toString (~lvid)

fun generateArgs([] : (Pat list) list) : args = []
  | generateArgs (pats :: patsList) =
    let
        fun pat2arg (ATPat atpat @@ _ : Pat) : arg = atpat2arg atpat
          | pat2arg (CONPat(_, lvid, atpat)@@A) =
            let val args as [arg] = [atpat2arg atpat]
            in
                (case arg of Generic => if span(tl(A)) = 1 then Generic else Const(toString lvid, args)
                            | _ => Const(toString lvid, args))
            end
          | pat2arg (COLONPat(pat, _)@@_) = pat2arg pat
          | pat2arg (ASPat(_, _, _, pat)@@_) = pat2arg pat
          | pat2arg (INFIXPatX(_, lvid, TUPLEAtPatX([pat1, pat2])@@_)@@A) =
            let
                val arg1 = pat2arg pat1
                val arg2 = pat2arg pat2
            in
                (case (arg1, arg2) of (Generic, Generic) => if span(tl(A)) = 1 then Generic
                                                            else InfixConst(toString lvid, (arg1, arg2))
                                    | _ => InfixConst(toString lvid, (arg1, arg2)))
            end
        and atpat2arg (WILDCARDAtPat@@_ : AtPat) = Generic
          | atpat2arg (SCONAtPat(scon)@@_) = SCon (~scon)
          | atpat2arg (IDAtPat(_, lvid@@A)@@_) =
            let
                val SOME (_, status) = !(hd (tl A))
            in
                case status of
                    IdStatus.v => Generic
                  | _ => Const(toString (lvid@@A),[])
            end
          | atpat2arg (PARAtPat(pat)@@_) = pat2arg pat
          | atpat2arg (UNITAtPatX@@_) = Generic
          | atpat2arg (TUPLEAtPatX(pats)@@_) =
            let
                val args = List.map pat2arg pats
            in
                if List.all (fn x => x = Generic) args then Generic
                else Const("tuple", args)
            end
          | atpat2arg (LISTAtPatX(pats)@@_) = ListConst (List.map pat2arg pats)
    in
        (List.map pat2arg pats) :: (generateArgs patsList)
    end

fun flattenMatch(Match(FmruleX(ATPat(TUPLEAtPatX(pats)@@_)@@_, _, _)@@_, matcho)@@_ : Match) : (Pat list) list =
    pats :: (?flattenMatch matcho)

fun const(s : string) : G.term = G.IdentTerm s

fun arg2cond (pos : int) (arg : arg) : G.term =
    let
        val varCtx = ref [] : (G.name list) ref
        val varCtr = ref 1;
        fun arg2rhs (Generic) =
            let
                val ident = "y" ^ Int.toString(!varCtr)
                val name = G.Name(ident)
                val _ = (varCtx := name :: !varCtx; varCtr := !varCtr + 1)
            in
                G.IdentTerm ident
            end
          | arg2rhs (Const(s, [])) = const(s)
          | arg2rhs (Const(s, l)) = G.ApplyTerm(const s, List.map arg2Garg l)
          | arg2rhs (SCon(scon)) = scon2term scon
          | arg2rhs (ListConst(args)) = G.ListTerm (List.map arg2rhs args)
          (*| arg2rhs (InfixConst(s, (arg1, arg2))) = G.InfixTerm(const s, [arg2Garg arg1, arg2Garg arg2])*)
          | arg2rhs (InfixConst(s, (arg1, arg2))) = 
            G.InfixTerm(const s, 
                        [G.Arg ( G.TupleTerm [arg2rhs arg1, arg2rhs arg2] ) ])

        and arg2Garg arg = G.Arg (arg2rhs arg)
        fun ctx2binders() = List.map (fn n => G.SingleBinder {name = n, typ = NONE, inferred = false}) (List.rev (!varCtx))
        val rhs = arg2rhs arg
        val lhs = G.IdentTerm ("x"^Int.toString(pos))
    in
        case !varCtx of [] => G.EqualTerm(lhs, rhs)
                     | _ => G.ExistsTerm(ctx2binders(), G.EqualTerm(lhs, rhs))
    end

fun args2conds(pos : int, [] : arg list, conds : G.term list) : G.term list = List.rev conds
  | args2conds (pos, arg :: args, conds) = if arg = Generic then args2conds(pos+1, args, conds)
                                           else args2conds(pos+1, args, (arg2cond pos arg) :: conds)

fun conds2prop(prop, []) : G.term = prop
  | conds2prop (prop, x :: l) = conds2prop(G.ConjunctTerm(prop, x), l)

fun prop2formula(formula : G.term, [] : G.term list) : G.term = formula
  | prop2formula (formula, p::props) = prop2formula(G.DisjunctTerm(formula, p), props)

fun findPreconds(match@@A : Match) : Gallina.ebinder =
    let
        val pats = flattenMatch(match@@A)
        val args = generateArgs pats
        val conds = List.map (fn args => args2conds(1, args, [])) args
        val prop = List.map (fn conds => conds2prop (List.hd conds, List.tl conds)) conds
        val formula = prop2formula (List.hd prop, List.tl prop)
    in
        G.ESingleBinder {name = G.Name("H"), typ = formula, inferred = true}
    end
end
end
