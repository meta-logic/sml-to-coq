structure FunctionChecker = 
struct
local
    open SyntaxCore
    open ConvertorUtil
in

datatype state = RECURSIVE
                | NONRECURSIVE
                | MAYBE

fun orelseState (s1, s2) =
    case s1 of NONRECURSIVE => s2
             | RECURSIVE => s1
             | MAYBE => if s2 = RECURSIVE then s2 else s1

fun checkExp (id : string) (ATExp atexp : Exp'): bool =
    checkAtExp id (~atexp)
  | checkExp id (APPExp(exp, atexp)) =
    checkExp id (~exp) orelse checkAtExp id (~atexp)
  | checkExp id (COLONExp(exp, _)) = checkExp id (~exp)
  | checkExp id (FNExp match) = checkMatch id (~match)
  | checkExp id (CASEExpX(exp, match)) =
    checkExp id (~exp) orelse checkMatch id (~match)
  | checkExp id (IFExpX(exp1, exp2, exp3)) =
    checkExp id (~exp1) orelse checkExp id (~exp2)
    orelse checkExp id (~exp3)
  | checkExp id (ANDALSOExpX (exp1, exp2)) =
    checkExp id (~exp1) orelse checkExp id (~exp2)
  | checkExp id (ORELSEExpX (exp1, exp2)) =
    checkExp id (~exp1) orelse checkExp id (~exp2)
  | checkExp id (INFIXExpX(exp, atexp)) =
    checkExp id (~exp) orelse checkAtExp id (~atexp)

and checkAtExp (id : string) (SCONAtExp _ : AtExp') : bool = false
  | checkAtExp id (IDAtExp (_, lvid)) = id = lvid2id (~lvid)
  | checkAtExp id (RECORDAtExp _) = raise Fail "Unimplemented \n"
  | checkAtExp id (LETAtExp (dec, exp)) =
    (case checkDec id (~dec) of
         RECURSIVE => true
       | NONRECURSIVE => false
       | _ => checkExp id (~exp))
  | checkAtExp id (PARAtExp exp) = checkExp id (~exp)
  | checkAtExp id UNITAtExpX = false
  | checkAtExp id (TUPLEAtExpX expList) =
    List.foldl (fn (x, y) => x orelse y) false (% (checkExp id) expList)
  | checkAtExp id (LISTAtExpX expList) = 
    List.foldl (fn (x, y) => x orelse y) false (% (checkExp id) expList)


and checkMatch (id : string) (Match (mrule, match2) : Match') =
    checkMrule id (~mrule) orelse (case match2 of
                                   NONE => false
                                    |  SOME match' => checkMatch id (~match'))

and checkMrule (id : string) (Mrule (pat, exp) : Mrule') : bool=
    (case checkPat id (~pat) of
         RECURSIVE => true
       | NONRECURSIVE => false
       | _ => checkExp id (~exp))

and checkPat (id : string) (ATPat atpat : Pat') : state =
    checkAtPat id (~atpat)
  | checkPat id (CONPat(_, _, atpat)) = checkAtPat id (~atpat)
  | checkPat id (COLONPat (pat, _)) = checkPat id (~pat)
  | checkPat id (ASPat (_, vid, _, pat)) =
    if vid2id (~vid) = id then NONRECURSIVE else
    checkPat id (~pat)
  | checkPat id (INFIXPatX(_, longvid, atpat)) =
    if lvid2id (~longvid) = id then NONRECURSIVE else
    checkAtPat id (~atpat)

and checkAtPat (id : string) (WILDCARDAtPat : AtPat') : state = MAYBE
  | checkAtPat id (SCONAtPat _) = MAYBE
  | checkAtPat id (IDAtPat (_, lvid)) =
    if lvid2id (~lvid) = id then NONRECURSIVE else MAYBE
  | checkAtPat id (RECORDAtPat(SOME patrow)) = checkPatrow id (~patrow)
  | checkAtPat id (RECORDAtPat(_)) = MAYBE
  | checkAtPat id (PARAtPat pat) = checkPat id (~pat)
  | checkAtPat id UNITAtPatX = MAYBE
  | checkAtPat id (TUPLEAtPatX patList) =
    List.foldl orelseState MAYBE (% (checkPat id) patList)
  | checkAtPat id (LISTAtPatX patList) =
    List.foldl orelseState MAYBE (% (checkPat id) patList)

and checkPatrow id (DOTSPatRow) = MAYBE
  | checkPatrow id (FIELDPatRow(lab, pat, patrow2)) =
    case patrow2 of
        NONE => checkPat id (~pat)
      | SOME patrow' => 
        (case checkPatrow id (~patrow') of
             MAYBE => checkPat id (~pat)
           | res => res)

and checkDec (id : string) (VALDec (_, valbind)) : state = checkValBind id (~valbind)
  | checkDec id (TYPEDec _) = MAYBE
  | checkDec id (DATATYPEDec _) =
    raise Fail "Local datatype declaration isn't supported in Coq!\n"
  | checkDec id (DATATYPE2Dec _) = 
    raise Fail "Local datatype declaration isn't supported in Coq!\n"
  | checkDec id (ABSTYPEDec _) =
    raise Fail "Abstract type declaration isn't supported in Coq!\n"
  | checkDec id (EXCEPTIONDec _) =
    raise Fail "Exception declaration isn't supported in Coq!\n"
  | checkDec id (LOCALDec _) =
    raise Fail "Not yet Implemented!\n"
  | checkDec id (OPENDec _) =
    raise Fail "Not yet Implemented!\n"
  | checkDec id EMPTYDec = MAYBE
  | checkDec id (SEQDec (dec1, dec2)) =
    (case (checkDec id (~dec1)) of
        RECURSIVE => RECURSIVE
      | NONRECURSIVE => NONRECURSIVE
      | MAYBE => checkDec id (~dec2))

and checkValBind (id : string) (PLAINValBind (pat, exp, valbind2)) : state =
    if checkExp id (~exp) then RECURSIVE
    else (case valbind2 of
             NONE => checkPat id (~pat)
           | SOME valbind' =>
             (case checkValBind id (~valbind') of
                  MAYBE => checkPat id (~pat)
               |  res => res))
  | checkValBind id (RECValBind(valbind)) = checkValBind id (~valbind)
end
end
