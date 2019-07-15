(* Copyright 1996 by Bell Laboratories *)
(* cps.sml *)

structure CPS = struct

local structure PT = PrimTyc
      fun bug s = ErrorMsg.impossible ("CPS:" ^ s)
in

datatype record_kind
  = RK_VECTOR
  | RK_RECORD
  | RK_SPILL
  | RK_ESCAPE
  | RK_EXN
  | RK_CONT
  | RK_FCONT
  | RK_KNOWN
  | RK_BLOCK
  | RK_FBLOCK
  | RK_I32BLOCK

datatype pkind = VPT | RPT of int | FPT of int
datatype cty = INTt | INT32t | PTRt of pkind
             | FUNt | FLTt | CNTt | DSPt

structure P = struct
    (* numkind includes kind and size *)
    datatype numkind = INT of int | UINT of int | FLOAT of int

    datatype arithop = + | - | * | / | ~ | abs 
                     | fsqrt | fsin | fcos | ftan 
	             | lshift | rshift | rshiftl | andb | orb | xorb | notb
		     | rem | div | mod

    datatype cmpop = > | >= | < | <= | eql | neq

    (* fcmpop conforms to the IEEE std 754 predicates. *)
    datatype fcmpop 
      = fEQ (* = *)  | fULG (* ?<> *) | fUN (* ? *)   | fLEG (* <=> *) 
      | fGT (* > *)  | fGE  (* >= *)  | fUGT (* ?> *) | fUGE (* ?>= *) 
      | fLT (* < *)  | fLE  (* <= *)  | fULT (* ?< *) | fULE (* ?<= *) 
      | fLG (* <> *) | fUE  (* ?= *)  | fsgn

    (* These are two-way branches dependent on pure inputs *)
    datatype branch
      = cmp of {oper: cmpop, kind: numkind}    (* numkind cannot be FLOAT *)
      | fcmp of {oper: fcmpop, size: int}
      | boxed | unboxed | peql | pneq
      | streq | strneq 
          (* streq(n,a,b) is defined only if strings a and b have
	     exactly the same length n>1 *)

  (* These all update the store *)
    datatype setter
      = numupdate of {kind: numkind}
      | unboxedupdate | boxedupdate | update
      | unboxedassign | assign
      | sethdlr | setvar | uselvar | setspecial
      | free | acclink | setpseudo | setmark
      | rawstore of {kind: numkind}
      | rawupdate of cty

  (* These fetch from the store, never have functions as arguments. *)
    datatype looker
      = ! | subscript | numsubscript of {kind: numkind} | getspecial | deflvar
      | getrunvec | gethdlr | getvar | getpseudo
      | rawload of {kind: numkind}

  (* These might raise exceptions, never have functions as arguments.*)
    datatype arith
      = arith of {oper: arithop, kind: numkind}
      | test of int * int
      | testu of int * int
      | test_inf of int
      | round of {floor: bool, fromkind: numkind, tokind: numkind}

  (* These don't raise exceptions and don't access the store. *)
    datatype pure
      = pure_arith of {oper: arithop, kind: numkind}
      | pure_numsubscript of {kind: numkind}
      | length | objlength | makeref
      | extend of int * int
      | trunc of int * int
      | copy of int * int
      | extend_inf of int
      | trunc_inf of int
      | copy_inf of int
      | real of {fromkind: numkind, tokind: numkind}
      | subscriptv
      | gettag | mkspecial | wrap | unwrap | cast | getcon | getexn
      | fwrap | funwrap | iwrap | iunwrap | i32wrap | i32unwrap
      | getseqdata | recsubscript | raw64subscript | newarray0
      | rawrecord of record_kind option
         (* allocate uninitialized words from the heap *)
      | condmove of branch

    local 
      fun ioper (op > : cmpop)  = (op <= : cmpop)
	| ioper op <= = op >
	| ioper op <  = op >= 
	| ioper op >= = op <
	| ioper eql   = neq 
	| ioper neq   = eql

      fun foper fEQ   = fULG
	| foper fULG  = fEQ
	| foper fGT   = fULE
	| foper fGE   = fULT
	| foper fLT   = fUGE
	| foper fLE   = fUGT
	| foper fLG   = fUE
	| foper fLEG  = fUN
	| foper fUGT  = fLE
	| foper fUGE  = fLT
	| foper fULT  = fGE
	| foper fULE  = fGT
	| foper fUE   = fLG
	| foper fUN   = fLEG
	| foper fsgn  = bug "fsgn has no opposite"
    in 
      fun opp boxed = unboxed 
	| opp unboxed = boxed
	| opp strneq = streq 
	| opp streq = strneq
	| opp peql = pneq 
	| opp pneq = peql
	| opp (cmp{oper,kind}) = cmp{oper=ioper oper,kind=kind}
	| opp (fcmp{oper,size}) = fcmp{oper=foper oper, size=size}
    end

    val iadd = arith{oper=op +,kind=INT 31}
    val isub = arith{oper=op -,kind=INT 31}
    val imul = arith{oper=op *,kind=INT 31}
    val idiv = arith{oper=op /,kind=INT 31}
    val ineg = arith{oper=op ~,kind=INT 31}

    val fadd = arith{oper=op +,kind=FLOAT 64}
    val fsub = arith{oper=op -,kind=FLOAT 64}
    val fmul = arith{oper=op *,kind=FLOAT 64}
    val fdiv = arith{oper=op /,kind=FLOAT 64}
    val fneg = arith{oper=op ~,kind=FLOAT 64}

    val ieql = cmp{oper=eql,kind=INT 31}
    val ineq = cmp{oper=neq,kind=INT 31}
    val igt = cmp{oper=op >,kind=INT 31}
    val ige = cmp{oper=op >=,kind=INT 31}
    val ile = cmp{oper=op <=,kind=INT 31}
    val ilt = cmp{oper=op <,kind=INT 31}
(*  val iltu = cmp{oper=ltu, kind=INT 31} 
    val igeu = cmp{oper=geu,kind=INT 31}
*)
    val feql =fcmp{oper=fEQ, size=64}
    val fneq =fcmp{oper=fLG, size=64}
    val fgt  =fcmp{oper=fGT, size=64}
    val fge  =fcmp{oper=fGE, size=64}
    val fle  =fcmp{oper=fLE, size=64}
    val flt  =fcmp{oper=fLT, size=64}

    fun arity op ~ = 1
      | arity _ = 2

end (* P *)

type lvar = LambdaVar.lvar

datatype value 
  = VAR of lvar
  | LABEL of lvar
  | INT of int
  | INT32 of Word32.word
  | REAL of string
  | STRING of string
  | OBJECT of Unsafe.Object.object
  | VOID

datatype accesspath 
  = OFFp of int 
  | SELp of int * accesspath

datatype fun_kind
  = CONT           (* continuation functions *)
  | KNOWN          (* general known functions *)
  | KNOWN_REC      (* known recursive functions *)
  | KNOWN_CHECK    (* known functions that need a heap limit check *)
  | KNOWN_TAIL     (* tail-recursive kernal *)
  | KNOWN_CONT     (* known continuation functions *)
  | ESCAPE         (* before the closure phase, any user function;
	              after the closure phase, escaping user function *)
  | NO_INLINE_INTO (* before the closure phase,
		      a user function inside of which no in-line expansions
		      should be performed; 
		      does not occur after the closure phase *)

datatype cexp
  = RECORD of record_kind * (value * accesspath) list * lvar * cexp
  | SELECT of int * value * lvar * cty * cexp
  | OFFSET of int * value * lvar * cexp
  | APP of value * value list
  | FIX of function list * cexp
  | SWITCH of value * lvar * cexp list
  | BRANCH of P.branch * value list * lvar * cexp * cexp
  | SETTER of P.setter * value list * cexp
  | LOOKER of P.looker * value list * lvar * cty * cexp
  | ARITH of P.arith * value list * lvar * cty * cexp
  | PURE of P.pure * value list * lvar * cty * cexp
  (* experimental "raw C call" (Blume, 1/2001) *)
  | RCC of rcc_kind * string * CTypes.c_proto * value list * (lvar * cty) list * cexp
and rcc_kind = FAST_RCC | REENTRANT_RCC
withtype function = fun_kind * lvar * lvar list * cty list * cexp

fun hasRCC(cexp) = let
  fun chkList(c::rest) = hasRCC(c) orelse chkList(rest)
    | chkList [] = false
in 
  case cexp
  of RCC _ => true
   | RECORD(_, _, _, e) => hasRCC e
   | SELECT(_, _, _, _, e) => hasRCC e
   | OFFSET(_, _, _, e) => hasRCC e
   | APP _ => false
   | FIX(fl, e) => hasRCC(e) orelse chkList(map (fn (_, _, _, _, e) => e) fl)
   | SWITCH(_, _, ce) => chkList(ce)
   | BRANCH(_, _, _, c1, c2) => hasRCC(c1) orelse hasRCC(c2)
   | SETTER(_, _, e) => hasRCC(e)
   | LOOKER(_, _, _, _, e) => hasRCC(e)
   | ARITH(_, _, _, _, e) => hasRCC(e)
   | PURE(_, _, _, _, e) => hasRCC(e)
end

fun sizeOf(FLTt) = 64 
  | sizeOf(INTt | INT32t | PTRt _ | FUNt | CNTt | DSPt) = 32

fun isFloat(FLTt) = true
  | isFloat(INTt | INT32t | PTRt _ | FUNt | CNTt | DSPt) = false

fun isTagged(FLTt | INT32t) = false
  | isTagged(INTt | PTRt _ | FUNt | CNTt | DSPt) = true

fun ctyToString(INTt) =  "[I]"
  | ctyToString(INT32t) =  "[I32]"
  | ctyToString(FLTt) =  "[R]"
  | ctyToString(PTRt (RPT k)) =  ("[PR"^(Int.toString(k))^"]")
  | ctyToString(PTRt (FPT k)) =  ("[PF"^(Int.toString(k))^"]")
  | ctyToString(PTRt (VPT)) =  "[PV]"
  | ctyToString(FUNt) =  "[F]"
  | ctyToString(CNTt) =  "[C]"
  | ctyToString(DSPt) =  "[D]"

fun combinepaths(p,OFFp 0) = p
  | combinepaths(p,q) = 
    let val rec comb =
	fn (OFFp 0) => q
	 | (OFFp i) => (case q of
		          (OFFp j) => OFFp(i+j)
		        | (SELp(j,p)) => SELp(i+j,p))
	 | (SELp(i,p)) => SELp(i,comb p)
    in comb p
    end

fun lenp(OFFp _) = 0
  | lenp(SELp(_,p)) = 1 + lenp p

val BOGt = PTRt(VPT)  (* bogus pointer type whose length is unknown *)

local structure LT = LtyExtern
      val tc_real = LT.tcc_real
      val lt_real = LT.ltc_real
in

fun tcflt tc = if LT.tc_eqv(tc, tc_real) then true else false
fun ltflt lt = if LT.lt_eqv(lt, lt_real) then true else false

fun rtyc (f, []) = RPT 0
  | rtyc (f, ts) =
      let fun loop (a::r, b, len) = 
                if f a then loop(r, b, len+1) else loop(r, false, len+1)
            | loop ([], b, len) = if b then FPT len else RPT len  
       in loop(ts, true, 0)
      end

fun ctyc tc =
  LT.tcw_prim(tc, 
     fn pt => (if pt = PT.ptc_int31 then INTt
               else if pt = PT.ptc_int32 then INT32t
                    else if pt = PT.ptc_real then FLTt
                         else BOGt),
     fn tc => 
       LT.tcw_tuple (tc, fn ts => PTRt(rtyc(tcflt, ts)),
          fn tc => if LT.tcp_arrow tc then FUNt
                   else if LT.tcp_cont tc then CNTt
                        else BOGt))

fun ctype lt = 
  LT.ltw_tyc(lt, fn tc => ctyc tc,
      fn lt => 
        LT.ltw_str(lt, fn ts => PTRt(rtyc(fn _ => false, ts)), 
            fn lt => if LT.ltp_fct lt then FUNt
                     else if LT.ltp_cont lt then CNTt
                          else BOGt))

end (* local ctype *)

end (* top-level local *)
end (* structure CPS *)

