(* COPYRIGHT (c) 1997 YALE FLINT PROJECT *)
(* monnier@cs.yale.edu *)

(* Converting the Standard PLambda.lexp into the FLINT IL *)
signature FLINTNM =
sig 
  val norm : PLambda.lexp -> FLINT.fundec
end (* signature FLINTNM *)

structure FlintNM : FLINTNM =
struct

local structure LT = PLambdaType
      structure FL = PFlatten		(* argument flattening *)
      structure DI = DebIndex
      structure PT = PrimTyc
      structure PO = PrimOp
      structure L  = PLambda
      structure F  = FLINT
      structure FU = FlintUtil
      structure DA = Access
      structure BT = BasicTypes
      structure PP = PrettyPrintNew
      structure PU = PPUtilNew
in

(* debugging *)
val say = Control_Print.say

val debugging = FLINT_Control.nmdebugging

fun debugmsg (msg : string) = 
    if !debugging then (say msg; say "\n") else ()
val pd = 15  (* debugging print depth *)

fun ppTycEnv (tenv: Lty.tycEnv) = 
    PP.with_default_pp
      (fn ppstrm => (PPLty.ppTycEnv pd ppstrm tenv; PU.pps ppstrm "\n"))

fun ppLty (lty: Lty.lty) = 
    PP.with_default_pp
      (fn ppstrm => (PPLty.ppLty pd ppstrm lty; PU.pps ppstrm "\n"))

fun debugLty (lty: Lty.lty) =
    if !debugging then ppLty lty else ()

fun debugLexp (lexp) = 
    if !debugging then
       PP.with_default_pp(fn ppstrm => PPLexp.ppLexp pd ppstrm lexp)
    else ()

val mkv = LambdaVar.mkLvar
val cplv = LambdaVar.dupLvar
val ident = fn le : L.lexp => le

val (iadd_prim, uadd_prim) = 
  let val lt_int = LT.ltc_int
      val intOpTy = LT.ltc_parrow(LT.ltc_tuple[lt_int,lt_int],lt_int)
      val addu = PO.ARITH{oper=PO.+, overflow=false, kind=PO.UINT 31}
   in (L.PRIM(PO.IADD,intOpTy,[]), L.PRIM(addu, intOpTy, []))
  end

fun bug msg = ErrorMsg.impossible("FlintNM: "^msg)


local val (trueDcon', falseDcon') = 
        let val lt = LT.ltc_arrow(LT.ffc_rrflint, [LT.ltc_unit], [LT.ltc_bool])
            fun h (Types.DATACON{name, rep, ...}) = (name, rep, lt)
         in (h BT.trueDcon, h BT.falseDcon)
        end

      fun boolLexp b = 
        let val v = mkv() and w = mkv()
            val dc = if b then trueDcon' else falseDcon'
         in F.RECORD(FU.rk_tuple, [], v, 
             F.CON(dc, [], F.VAR v, w, F.RET[F.VAR w]))
        end
in 

fun flint_prim (po as (d, p, lt, ts), vs, v, e) = 
  (case p
    of (PO.BOXED  | PO.UNBOXED | PO.CMP _ | PO.PTREQL | 
        PO.PTRNEQ | PO.POLYEQL | PO.POLYNEQ) =>
          (*** branch primops get translated into F.BRANCH ***)
          F.LET([v], F.BRANCH(po, vs, boolLexp true, boolLexp false), e)
     | (PO.GETRUNVEC | PO.GETHDLR | PO.GETVAR | PO.DEFLVAR) =>
          (*** primops that take zero arguments; argument types
               must be unit ***)
          let fun fix t = 
                LT.ltw_arrow(t, 
		(fn (ff,[t1],ts2) => 
		    (if LT.tc_eqv(t1, LT.tcc_unit) 
		     then LT.ltc_tyc(LT.tcc_arrow(ff, [], ts2))
		     else bug "unexpected zero-args prims 1 in flint_prim")
		  | _ => bug "flint_prim:t1"),
                fn _ => bug "unexpected zero-args prims 2 in flint_prim")
              val nlt = 
                LT.ltw_ppoly(lt, 
                   fn (ks, t) => LT.ltc_ppoly(ks, fix t),
                   fn _ => fix lt)
           in F.PRIMOP((d,p,nlt,ts), [], v, e)
          end
     | _ => 
          F.PRIMOP(po, vs, v, e))

end (* local flint_prim *)

(* force_raw freezes the calling conventions of a data constructor;
   strictly used by the CON and DATAcon only 
 *)
fun force_raw (pty) = 
  if LT.ltp_ppoly pty then
    let val (ks, body) = LT.ltd_ppoly pty
        val (aty, rty) = LT.ltd_parrow body
     in LT.ltc_ppoly(ks,
           LT.ltc_arrow(LT.ffc_rrflint, [FL.ltc_raw aty], [FL.ltc_raw rty]))
    end
  else 
    let val (aty, rty) = LT.ltd_parrow pty
     in LT.ltc_arrow(LT.ffc_rrflint, [FL.ltc_raw aty], [FL.ltc_raw rty])
    end (* function force_raw *)

fun tocon con =
    let val _ = 1
    in case con of
	L.INTcon x    => F.INTcon x
      | L.INT32con x  => F.INT32con x
      | L.INTINFcon _ => bug "INTINFcon"
      | L.WORDcon x   => F.WORDcon x
      | L.WORD32con x => F.WORD32con x
      | L.REALcon x   => F.REALcon x
      | L.STRINGcon x => F.STRINGcon x
      | L.VLENcon x   => F.VLENcon x
      | L.DATAcon x => bug "unexpected case in tocon"
    end

fun tofundec (venv,d,f_lv,arg_lv,arg_lty,body,isrec) =
    let val _ = (debugmsg "tofundec normalize argument:\n";
		 debugLty arg_lty;
		 debugmsg "\ntofundec normalize body: \n";
		 debugLexp body)
	val (body',body_lty) =
        (* first, we translate the body (in the extended env) *)
        tolexp (LT.ltInsert(venv, arg_lv, arg_lty, d), d) body
	val _ =  debugmsg ">>tofundec detuple arg type"
        (* detuple the arg type *)
	val ((arg_raw, arg_ltys, _), unflatten) = FL.v_punflatten arg_lty
        val _ = debugmsg ">>unflatten body"    
        (* now, we add tupling code at the beginning of the body *)
        val (arg_lvs, body'') = unflatten(arg_lv, body')
	val _ = debugmsg ">>construct return type"
	(* construct the return type if necessary *)
	val (body_raw, body_ltys, _) = FL.t_pflatten body_lty
	val rettype = if not isrec then NONE
		      else SOME(map FL.ltc_raw body_ltys, F.LK_UNKNOWN)
	val _ = debugmsg ">>Handle fcn or fct"
	val (f_lty, fkind) =
	    if (LT.ltp_tyc arg_lty andalso LT.ltp_tyc body_lty) then
		(* a function *)
		(LT.ltc_parrow(arg_lty, body_lty),
		 {isrec=rettype, known=false, inline=F.IH_SAFE,
		  cconv=F.CC_FUN(LT.ffc_var(arg_raw, body_raw))})
	    else 
		(* a functor *)
		(LT.ltc_pfct(arg_lty, body_lty),
		 {isrec=rettype, known=false, inline=F.IH_SAFE,
		  cconv=F.CC_FCT})
	val arg_ltys' =  map FL.ltc_raw arg_ltys
	val _ = debugmsg "<<tofundec"
    in ((fkind, f_lv, ListPair.zip(arg_lvs, arg_ltys'), body''),
	f_lty)
    end


(* used to translate expressions whose structure is the same
 * in Flint as in PLambda (either both binding or both non-binding)
 * a continuation is unnecessary *)
and tolexp (venv,d) lexp =
    let val _ = debugmsg ">>tolexp"
	fun default_tovalues () =
        tovalues(venv, d, lexp,
                fn (vals, lty) =>
		(F.RET vals, lty))
    val v = case lexp of
        L.APP (L.PRIM _, arg) => default_tovalues()
      | L.APP (L.GENOP _,arg) => default_tovalues()
      | L.APP (L.FN (arg_lv,arg_lty,body), arg_le) =>
	    tolexp (venv,d) (L.LET(arg_lv, arg_le, body))
      | L.APP (f,arg) =>
            (* first, evaluate f to a mere value *)
            tovalue(venv, d, f,
                    fn (f_val, f_lty) =>
                    (* then eval the argument *)
                    tovalues(venv, d, arg,
			     fn (arg_vals, arg_lty) =>
			     (* now find the return type *)
			     let val (_, r_lty) = 
                                   if LT.ltp_pfct f_lty then LT.ltd_pfct f_lty
                                   else LT.ltd_parrow f_lty
			     (* and finally do the call *)
			     in (F.APP(f_val,arg_vals), r_lty)
			     end))

      | L.FIX (lvs,ltys,lexps,lexp) =>
            (* first, let's setup the enriched environment with those funs *)
            let val venv' = ListPair.foldl (fn (lv,lty,ve) =>
                                   LT.ltInsert(ve, lv, lty, d))
                                  venv (lvs, ltys)

		fun map3 _ ([], _, _) = []
		  | map3 _ (_, [], _) = []
		  | map3 _ (_, _, []) = []
		  | map3 f (x :: xs, y :: ys, z :: zs) =
		      f (x, y, z) :: map3 f (xs, ys, zs)

                (* then translate each function in turn *)
                val funs = map3 (fn (f_lv,f_lty,L.FN(arg_lv,arg_lty,body)) =>
                                #1(tofundec(venv', d, 
					    f_lv, arg_lv, arg_lty, body, true))
				 | _ => bug "non-function in L.FIX")
				(lvs, ltys, lexps)

                (* finally, translate the lexp *)
                val (lexp',lty) = tolexp (venv',d) lexp
            in (F.FIX(funs,lexp'), lty)
            end

      | L.LET (lvar,lexp1,lexp2) =>
            tolvar(venv, d, lvar, lexp1,
                   fn lty1 =>
                   tolexp (LT.ltInsert(venv,lvar,lty1,d), d) lexp2)

      | L.RAISE (le, r_lty) => 
            tovalue(venv, d, le,
                    fn (le_val,le_lty) =>
                    let val (_, r_ltys, _) = FL.t_pflatten r_lty
                    in (F.RAISE(le_val, map FL.ltc_raw r_ltys), r_lty)
                    end)

      | L.HANDLE (body, handler) =>
            tovalue(venv, d, handler,
                    fn (h_val,h_lty) =>
                    let val (body', body_lty) = tolexp (venv, d) body
                    in (F.HANDLE(body', h_val), body_lty)
                    end)

      | L.SWITCH (le,acs,[],NONE) => bug "unexpected case in L.SWITCH"
	    (* tovalue(venv, d, le, fn _ => (F.RET[], [])) *)
      | L.SWITCH (le,acs,[],SOME lexp) =>
	    tovalue(venv, d, le, fn (v,lty) => tolexp (venv,d) lexp)
      | L.SWITCH (le,acs,conlexps,default) =>
	    let fun f (L.DATAcon((s,cr,lty),tycs,lvar),le) =
		    let val (lv_lty,_) = LT.ltd_parrow(LT.lt_pinst(lty,tycs))
			val newvenv = LT.ltInsert(venv,lvar,lv_lty,d)
			val (le, le_lty) = tolexp (newvenv,d) le
		    in
			((F.DATAcon((s, cr, force_raw lty),
				    map FL.tcc_raw tycs, lvar),
			  le),
			 le_lty)
		    end
		  | f (con,le) =
		    let val (lexp,lty) = tolexp (venv,d) le
		    in ((tocon con, lexp), lty)
		    end
	    in tovalue(venv, d, le,
		       fn (v, lty) =>
		       let val default = Option.map (#1 o tolexp(venv,d)) default
			   val conlexps = map f conlexps
			   val lty = #2 (List.hd conlexps)
		       in (F.SWITCH(v, acs, map #1 conlexps, default), lty)
		       end)
	    end
	    
      (* for mere values, use tovalues *)
      | _ => default_tovalues ()
    val _ = debugmsg "<<tolexp"
    in v 
    end

(*
 * tovalue: turns a PLambda lexp into a value+type and then calls
 * the continuation that will turn it into an Flint lexp+type
 * (ltyenv * DebIndex * L.lexp * ((value * lty) -> (F.lexp * lty list))) -> (F.lexp * lty)
 * 
 * - venv is the type environment for values
 * - conts is the continuation
 *)
and tovalue (venv,d,lexp,cont) =
    let val _ = debugmsg ">>tovalue"
	val _ = debugLexp lexp
	val _ = 1
    val v = case lexp of
        (* for simple values, it's trivial *)
        L.VAR v => cont(F.VAR v, LT.ltLookup(venv, v, d))
      | L.INT i => 
         ((i+i+2; cont(F.INT i, LT.ltc_int)) handle Overflow => 
            (let val _ = debugmsg "toValue INT Overflow"
		 val z = i div 2
                 val ne = L.APP(iadd_prim, L.RECORD [L.INT z, L.INT (i-z)])
              in tovalue(venv, d, ne, cont)
             end))
      | L.WORD i => 
         let val maxWord = 0wx20000000
          in if Word.<(i, maxWord) then cont(F.WORD i, LT.ltc_int)
             else let val x1 = Word.div(i, 0w2)
                      val x2 = Word.-(i, x1)
                      val ne = L.APP(uadd_prim, 
                                     L.RECORD [L.WORD x1, L.WORD x2])
                   in tovalue(venv, d, ne, cont)
                  end
         end
      | L.INT32 n => cont(F.INT32 n, LT.ltc_int32)
      | L.WORD32 n => cont(F.WORD32 n, LT.ltc_int32)
      | L.REAL x => cont(F.REAL x, LT.ltc_real)
      | L.STRING s => cont(F.STRING s, LT.ltc_string)

      (* for cases where tolvar is more convenient *)
      | _ => 
            let val lv = mkv()
            in tolvar(venv, d, lv, lexp, 
		      fn lty => (debugmsg ">>tovalue tolvar cont"; 
				 debugLexp lexp;
				 cont(F.VAR lv, lty)))
            end
    val _ = debugmsg "<<tovalue"
    in v
    end
		    
		    
(*
 * tovalues: turns a PLambda lexp into a list of values and a list of types
 * and then calls the continuation that will turn it into an Flint lexp+type
 *
 * (ltyenv * DebIndex * L.lexp * ((value list * lty list) -> (F.lexp * lty list))) -> (F.lexp * lty)
 * 
 * - venv is the type environment for values
 * - cont is the continuation
 *)
and tovalues (venv,d,lexp,cont) =
    let val _ = debugmsg ">>tovalues"
	val _ = debugLexp lexp
	val _ = 1
    val v = case lexp of
	L.RECORD (lexps) =>
	    lexps2values(venv,d,lexps,
			 fn (vals,ltys) =>
			 let val _ = debugmsg ">>tovalues continuation"
			     val _ = 
			 if length ltys = 0 then
			     debugmsg ("tovalues cont ltys null")
			 else if length ltys = 1 
			 then (debugmsg ("tovalues cont ltys singleton:\n");
			       debugLty (hd ltys))
			 else (debugmsg ("tovalues cont ltys > 1\n \
					\length is: "
					^ Int.toString (length ltys) ^
					"\nstarting with:\n");
			       debugLty (hd ltys))
			      fun scan [] = debugmsg "tovalues end of ltys"
				| scan (lts) =
				    let fun scan' ([], [], n) = ()
					  | scan' (x::xs, l::ls, n) = 
					    (debugmsg ("tovalues cont ltys ["^
						      Int.toString n ^"]:");
					     debugLexp l;
					     debugLty x;
					     scan' (xs, ls, n + 1))
					  | scan' _ = 
					    raise Fail "flintnm.sml:\
							\ tovalues::scan'"

				    in scan'(lts, lexps, 0)
				    end
                             val _ = scan ltys 
			     val lty = LT.ltc_tuple ltys
			     val _ = (debugmsg ("<<tovalues cont tupled");
				      debugLty lty)
			     val (_, ltys, _) = FL.t_pflatten lty
			     val _ = debugmsg "<<tovalues cont flatten"
			     val _ = (debugmsg (">>tovalues cont LT.lt_eqv");
				      debugLty lty)
			     val _ = debugmsg ">>tovalues cont LT.ltc_tuple"
			     val ltyst = (LT.ltc_tuple ltys)
			     val _ = (debugmsg ("<<tovalues cont LT.ltc_tuple");
				      debugLty ltyst)
			     val eqvLty = LT.lt_eqv(lty, LT.ltc_tuple ltys)
			     val _ = debugmsg "<<tovalues cont lt_eqv"
			 in
			     (* detect the case where flattening is trivial *)
			     if eqvLty then 
				 cont(vals,lty)
			     else
				 let val lv = mkv()
                                     val (_, pflatten) = FL.v_pflatten lty 
				     val (vs,wrap) = pflatten (F.VAR lv)
				     val (c_lexp,c_lty) = cont(vs, lty)
				     val _ = debugmsg "<<tovalues continuation"
				 in
				     (F.RECORD(FU.rk_tuple,
					       vals, lv, wrap c_lexp),
				      c_lty)
				 end
			 end)
			    
      | _ => tovalue(venv,d,lexp,
		     fn (v, lty) =>
		     let val (vs,wrap) = (#2(FL.v_pflatten lty)) v
			 val (c_lexp, c_lty) = cont(vs, lty)
		     in (wrap c_lexp, c_lty)
		     end)
    val _ = debugmsg "<<tovalues"
    in v
    end

(* eval each lexp to a value *)
and lexps2values (venv,d,lexps,cont) =
    let val _ = debugmsg ">>lexps2values"
	val _ = map debugLexp lexps
	val _ = 1

fun ppTycEnv tenv = 
    PrettyPrintNew.with_default_pp (fn ppstrm => PPLty.ppTycEnv 20 ppstrm tenv)
fun ppTyc tyc =
    PrettyPrintNew.with_default_pp (fn ppstrm => PPLty.ppTyc 20 ppstrm tyc)

	fun f [] (vals,ltys) = cont (rev vals, rev ltys)
	  | f (lexp::lexps) (vals,ltys) =
	    ((* This debugging printing is quadratic
		debugmsg ("lexps2values ltys:");
                map debugLty ltys; *)
	     tovalue(venv,d,lexp,
		     fn (v, lty) =>
                       ((* debugmsg ">>lexps2values tovalue";
			 debugLexp lexp;
			 debugmsg "lty:"; debugLty lty *)
		        f lexps (v::vals, lty::ltys))))
	    (* handle LtyKernel.tcUnbound (tenv,tyc) => 
		   (with_pp(fn s =>
                      (PU.pps s "*** lexps2values ***; PP.newline s;
                       lexp: \n"; 
		       PPLexp.printLexp lexp;
		       print "\ntype: \n";
		       ppTyc 20 s tyc; PP.newline s;
		       PU.pps s "tenv:"; PP.newline s;
		       ppTycEnv 20 s tenv;
                       raise LtyKernel.tcUnbound (tenv,tyc)))) *)
	val v = f lexps ([], [])
	val _ = debugmsg "<<lexp2values"
    in
	v
    end

(*
 * tolvar: same as tovalue except that it binds the value of the PLambda
 * to the indicated lvar and passes just the type to the continuation
 *)
and tolvar (venv,d,lvar,lexp,cont) =
    let val _ = debugmsg ">>tolvar"
	val _ = debugLexp lexp
	fun eta_expand (f, f_lty) =
            let val lv = mkv()
                val (arg_lty, ret_lty) = (LT.ltd_parrow f_lty)
            in tolvar(venv, d, lvar,
                      L.FN(lv, arg_lty, L.APP(f, L.VAR lv)),
                      cont)
            end

        (* inbetween tolvar and tovalue: it binds the lexp to a variable but
         * is free to choose the lvar and passes it to the continutation *)
        fun tolvarvalue (venv,d,lexp,cont) =
            tovalue(venv, d, lexp,
                    fn (v,lty) =>
                    case v of
                        F.VAR lv => cont(lv, lty)
                      | _ => let val lv = mkv()
                                 val (lexp',lty) = cont(lv, lty)
                             in (F.LET ([lv], F.RET [v], lexp'), lty)
                             end)

        fun PO_helper (arg,f_lty,tycs,filler) =
            (* invariants: primop's types are always fully closed *)
            let (* pty is the resulting FLINT type of the underlying primop,
                   r_lty is the result PLambda type of this primop expression,
                   and flat indicates whether we should flatten the arguments
                   or not. The results of primops are never flattened.
                 *)
		val _ = debugmsg ">>tolvar PO_helper"
                val (pty, r_lty, flat) = 
                  (case (LT.ltp_ppoly f_lty, tycs) 
                    of (true, _) => 
                         let val (ks, lt) = LT.ltd_ppoly f_lty
                             val (aty, rty) = LT.ltd_parrow lt
                             val r_lty = 
                               LT.lt_pinst(LT.ltc_ppoly(ks, rty), tycs)

                             val (_, atys, flat) = FL.t_pflatten aty 
                             (*** you really want to have a simpler
                                  flattening heuristics here; in fact,
                                  primop can have its own flattening
                                  strategy. The key is that primop's 
                                  type never escape outside.
                              ***)

                             val atys = map FL.ltc_raw atys
                             val nrty = FL.ltc_raw rty
                             val pty = LT.ltc_arrow(LT.ffc_rrflint,atys,[nrty])
                          in ( LT.ltc_ppoly(ks, pty), r_lty, flat)
                         end
                     | (false, []) => (* monomorphic case *)
                         let val (aty, rty) = LT.ltd_parrow f_lty
                             val (_, atys, flat) = FL.t_pflatten aty
                             val atys = map FL.ltc_raw atys
                             val nrty = FL.ltc_raw rty
                             val pty = LT.ltc_arrow(LT.ffc_rrflint,atys,[nrty])
                          in (pty, rty, flat)
                         end
                     | _ => bug "unexpected case in PO_helper")
                val r = if flat then
                 (* ZHONG asks: is the following definitely safe ?
                    what would happen if ltc_raw is not an identity function ?
                  *)
                  tovalues(venv, d, arg,
		     	   fn (arg_vals, arg_lty) =>
		     	   let val _ = debugmsg ">>tolvar PO_helper cont"
			       val (c_lexp, c_lty) = cont(r_lty)
		     	   (* put the filling inbetween *)
		     	   val r' = (filler(arg_vals, pty, c_lexp), c_lty)
			   val _ = debugmsg "<<tolvar PO_helper cont"
			   in r' 
		     	   end)  
                else 
                   tovalue(venv, d, arg,
		     	   fn (arg_val, arg_lty) =>
		     	   let val (c_lexp, c_lty) = cont(r_lty)
		     	   (* put the filling inbetween *)
		     	   in (filler([arg_val], pty, c_lexp), c_lty)
		     	   end)
	     val _ = debugmsg "<<tolvar PO_helper"
	    in r 
            end (* function PO_helper *)

        fun default_tolexp () =
            let val (lexp', lty) = tolexp (venv, d) lexp
                val (c_lexp, c_lty) = cont(lty)
                val (_, punflatten) = FL.v_punflatten lty 
                val (lvs,c_lexp') = punflatten (lvar, c_lexp)
            in (F.LET(lvs, lexp', c_lexp'), c_lty)
            end

(*         fun default_tovalue () = *)
(*             tovalue(venv, d, lexp, *)
(*                     fn (v,lty) => *)
(*                     let val (lexp', ltys) = cont(lty) *)
(*                     in (F.LET([lvar], F.RET[v], lexp'), ltys) *)
(*                     end) *)

    val r = case lexp of
      (* primops have to be eta-expanded since they're not valid
       * function values anymore in Flint *)
        L.PRIM (po,lty,tycs) => eta_expand(lexp, LT.lt_pinst(lty, tycs))
      | L.GENOP (dict,po,lty,tycs) => eta_expand(lexp, LT.lt_pinst(lty, tycs))

      | L.FN (arg_lv,arg_lty,body) =>
            (* translate the body with the extended env into a fundec *)
            let val (fundec as (fk,f_lv,args,body'), f_lty) =
		    tofundec(venv, d, lvar, arg_lv, arg_lty, body, false)
                val (lexp, lty) = cont(f_lty)
            in (F.FIX([fundec], lexp), lty)
            end

      (* this is were we really deal with primops *)
      | L.APP (L.PRIM ((po,f_lty,tycs)),arg) =>
	let val _ = debugmsg ">>tolvar L.APP"
	    val (lexp', lty') = 
            PO_helper(arg, f_lty, tycs,
                       fn (arg_vals,pty, c_lexp) =>
                       flint_prim((NONE, po, pty, map FL.tcc_raw tycs),
				  arg_vals, lvar, c_lexp))
	    val _ = debugmsg "<<tolvar L.APP"
	    val _ = debugLty lty'
	in (lexp', lty')
	end

      | L.APP (L.GENOP({default,table},po,f_lty,tycs),arg) =>
            let fun f ([],table,cont) = cont (table)
                  | f ((tycs,le)::t1,t2,cont) =
                tolvarvalue(venv,d,le,
                            fn (le_lv,le_lty) =>
                            f(t1, (map FL.tcc_raw tycs,le_lv)::t2, cont))
            (* first, eval default *)
            in tolvarvalue(venv,d,default,
                           fn (dflt_lv,dflt_lty) =>
                           (* then eval the table *)
                           f(table, [],
                             fn table' =>
                             PO_helper(arg, f_lty, tycs,
                                        fn (arg_vals,pty,c_lexp) =>
                                        flint_prim((SOME {default=dflt_lv, 
                                                          table=table'},
                                                    po, pty, 
                                                    map FL.tcc_raw tycs),
						   arg_vals, lvar, c_lexp))))
            end


      (*  | L.TFN ([], body) => bug "TFN[]" *)
      | L.TFN (tks, body) =>
            let val (body', body_lty) =
                  tovalue(venv, DI.next d, body, 
                          fn (le_val, le_lty) => (F.RET [le_val], le_lty))
                val lty = LT.ltc_ppoly(tks, body_lty)
                val (lexp', lty) = cont(lty)
		val args = map (fn tk => (mkv(), tk)) tks
            in  (F.TFN(({inline=F.IH_SAFE}, lvar, args, body'), lexp'),
                 lty)
            end

      (*  | L.TAPP (f,[]) => bug "TAPP[]" *)
      | L.TAPP (f,tycs) =>
            (* similar to APP *)
            tovalue(venv, d, f,
                    fn (f_val,f_lty) =>
                    let val f_lty = LT.lt_pinst(f_lty, tycs)
			val (c_lexp, c_lty) = cont(f_lty)
                    in  (F.LET([lvar], F.TAPP(f_val, map FL.tcc_raw tycs),
                               c_lexp), c_lty)
                    end)

      | L.ETAG (le,lty) =>
            tovalue(venv, d, le,
                    fn (le_lv, le_lty) =>
                    let val (c_lexp, c_lty) = cont(LT.ltc_etag lty)
                        val mketag = FU.mketag (FL.tcc_raw (LT.ltd_tyc lty))
				     handle LT.DeconExn => bug "etag in flintnm"
                    in (flint_prim(mketag, [le_lv], lvar, c_lexp), c_lty)
                    end)
      | L.CON ((s,cr,lty),tycs,le) =>
	    tovalue(venv, d, le,
		     fn (v,_) =>
		     let val r_lty = LT.lt_pinst(lty, tycs)
                         val (_,v_lty) = LT.ltd_parrow r_lty
			 val (c_lexp, c_lty) = cont(v_lty)
		     in (F.CON((s, cr, force_raw lty),
			       map FL.tcc_raw tycs, v, lvar, c_lexp),
			 c_lty)
		     end)

      | L.VECTOR (lexps,tyc) =>
	   lexps2values(venv,d,lexps,
			fn (vals, ltys) =>
			let val _ = debugmsg ">>tolvar VECTOR cont"
			    val lty = LT.ltc_tyc(LT.tcc_vector tyc)
			    val (c_lexp, c_lty) = cont(lty)
			in (F.RECORD(F.RK_VECTOR (FL.tcc_raw tyc),
				     vals, lvar, c_lexp),
			    c_lty)
			end)
      | L.RECORD lexps =>
	   lexps2values(venv,d,lexps,
			fn (vals, ltys) =>
			let val _ = debugmsg ">>tolvar RECORD cont"
			    val lty = LT.ltc_tuple ltys
			    val (c_lexp, c_lty) = cont(lty)
			in (F.RECORD(FU.rk_tuple,
                                     vals, lvar, c_lexp), c_lty)
			end)
      | L.SRECORD lexps =>
	   lexps2values(venv,d,lexps,
			fn (vals, ltys) =>
			let val _ = debugmsg ">>tolvar SRECORD cont"
			    val lty = LT.ltc_str(ltys)
			    val (c_lexp, c_lty) = cont(lty)
			in (F.RECORD(F.RK_STRUCT, vals, lvar, c_lexp), c_lty)
			end)

      | L.SELECT (n,lexp) =>
	    tovalue(venv, d, lexp,
		    fn (v, lty) =>
		    let val lty = (LT.lt_select(lty, n))
			val (c_lexp, c_lty) = cont(lty)
		    in (F.SELECT(v, n, lvar, c_lexp), c_lty)
		    end)

      | L.PACK (lty,otycs,ntycs,lexp) =>
            bug "PACK is not currently supported"
(*
	    tovalue(venv, d, lexp,
		    fn (v, v_lty) =>
		    let val nlty = LT.lt_pinst(lty, ntycs)
			val (c_lexp, c_lty) = cont(nlty)
		    in (F.PACK(lty,
			       map FL.tcc_raw otycs,
			       map FL.tcc_raw ntycs,
			       v, lvar, c_lexp),
			c_lty)
		    end)
*)

      (* these ones shouldn't matter because they shouldn't appear *)
(*       | L.WRAP _ => bug "unexpected WRAP in plambda" *)
(*       | L.UNWRAP _ => bug "unexpected UNWRAP in plambda" *)

      | _ => default_tolexp ()
    in (debugmsg "<<tolvar"; r)
    end (* function tolvar *)

fun norm (lexp as L.FN(arg_lv,arg_lty,e)) =
    let val r = 
	    (#1(tofundec(LT.initLtyEnv, DI.top, mkv(), arg_lv, arg_lty, e, false))
	     handle x => raise x)
    in (debugmsg "<<norm" (*; PPFlint.printFundec r *); r)
    end
  | norm _ = bug "unexpected toplevel lexp"

end (* toplevel local *)
end (* structure FlintNM *)
