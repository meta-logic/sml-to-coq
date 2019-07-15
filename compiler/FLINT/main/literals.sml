(* literals.sml
 *
 * COPYRIGHT (c) 1998 Bell Labs, Lucent Technologies.
 * COPYRIGHT (c) 1998 YALE FLINT PROJECT.
 *)

signature LITERALS =
 sig
   type lit
   val litsplit : CPS.function -> CPS.function * lit
   val litToBytes : lit -> Word8Vector.vector
 end;

structure Literals : LITERALS = 
struct

structure W8V = Word8Vector

local structure LV = LambdaVar
      structure Intset = struct
	type intset = IntRedBlackSet.set ref
	fun new() = ref IntRedBlackSet.empty
	fun add set i = set := IntRedBlackSet.add(!set, i)
	fun mem set i =  IntRedBlackSet.member(!set, i)
	fun rmv set i = set := IntRedBlackSet.delete(!set, i)
      end
      open CPS
in

fun bug msg = ErrorMsg.impossible ("Literals: "^msg) 
val ident = fn x => x
fun mkv _ = LV.mkLvar()

(****************************************************************************
 *                         A MINI-LITERAL LANGUAGE                          *
 ****************************************************************************)
datatype lit_val
  = LI_INT of word
  | LI_STRING of string
  | LI_VAR of lvar

datatype block_kind
  = LI_RECORD		(* record of tagged ML values *)
  | LI_VECTOR		(* vector of tagged ML values *)

datatype lit_exp
  = LI_TOP of lit_val list
  | LI_BLOCK of (block_kind * lit_val list * lvar * lit_exp)
  | LI_F64BLOCK of (string list * lvar * lit_exp)
  | LI_I32BLOCK of (Word32.word list * lvar * lit_exp)

type lit = lit_exp

fun rk2bk CPS.RK_VECTOR	= LI_VECTOR
  | rk2bk CPS.RK_RECORD	= LI_RECORD
  | rk2bk _		= bug "rk2bk: unexpected block kind"

fun val2lit (CPS.VAR v) = LI_VAR v
  | val2lit (CPS.INT i) = LI_INT(Word.fromInt i)
  | val2lit (CPS.STRING s) = LI_STRING s
  | val2lit _ = bug "unexpected case in val2lit"

(****************************************************************************
 *                 TRANSLATING THE LITERAL EXP TO BYTES                     *
 ****************************************************************************)

(* Literals are encoded as instructions for a "literal machine."  The abstract
 * description of these instructions is as follows:
 *
 *	INT(i)			-- push the int31 literal i on the stack
 *	RAW32[i1,...,in]	-- form a 32-bit raw data record from the
 *				   i1..in and push a pointer to it.
 *	RAW64[r1,...,rn]	-- form a 64-bit raw data record from the
 *				   r1..rn and push a pointer to it.
 *	STR[c1,...,cn]		-- form a string from the characters c1..cn
 *				   and push it on the stack.
 *	LIT(k)			-- push the contents of the stack element
 *				   that is k slots from the top of the stack.
 *	VECTOR(n)		-- pop n elements from the stack, make a vector
 *				   from them and push a pointer to the vector.
 *	RECORD(n)		-- pop n elements from the stack, make a record
 *				   from them and push a pointer.
 *	RETURN			-- return the literal that is on the top of the
 *				   stack.
 *)

fun w32ToBytes' (w, l) =
	Word8.fromLargeWord(Word32.>>(w, 0w24)) ::
	Word8.fromLargeWord(Word32.>>(w, 0w16)) ::
	Word8.fromLargeWord(Word32.>>(w, 0w8)) ::
	Word8.fromLargeWord w :: l
fun w32ToBytes w = w32ToBytes' (w, [])
fun w31ToBytes w = w32ToBytes(Word31.toLargeWordX w)
fun intToBytes i = w32ToBytes(Word32.fromInt i)
fun intToBytes' (i, l) = w32ToBytes'(Word32.fromInt i, l)
fun strToBytes s = map Byte.charToByte (explode s)

val emit_MAGIC = W8V.fromList[0wx19, 0wx98, 0wx10, 0wx22]
fun emit_DEPTH n = W8V.fromList(intToBytes n)
fun emit_INT i = W8V.fromList(0wx01 :: w31ToBytes i)
fun emit_RAW32 [i] = W8V.fromList(0wx02 :: w32ToBytes i)
  | emit_RAW32 l =
      W8V.fromList(0wx03 :: (intToBytes'(length l, List.foldr w32ToBytes' [] l)))
fun emit_RAW64 [r] = W8V.fromList(0wx04 :: strToBytes r)
  | emit_RAW64 l = W8V.concat(
      W8V.fromList(0wx05 :: intToBytes(length l)) :: map Byte.stringToBytes l)
fun emit_STR s = W8V.concat[
	W8V.fromList(0wx06 :: intToBytes(size s)),
	Byte.stringToBytes s
      ]
fun emit_LIT k = W8V.fromList(0wx07 :: intToBytes k)
fun emit_VECTOR n = W8V.fromList(0wx08 :: intToBytes n)
fun emit_RECORD n = W8V.fromList(0wx09 :: intToBytes n)
val emit_RETURN = W8V.fromList[0wxff]

fun litToBytes (LI_TOP[]) = W8V.fromList[]
  | litToBytes litExp = let
      fun depth (LI_TOP ls, d, maxDepth) = Int.max(maxDepth, d+length ls)
	| depth (LI_BLOCK(_, ls, _, rest), d, maxDepth) =
	    depth (rest, d+1, Int.max(maxDepth, d+length ls))
	| depth (LI_F64BLOCK(ls, _, rest), d, maxDepth) =
	    depth (rest, d+1, Int.max(maxDepth, d+length ls))
	| depth (LI_I32BLOCK(ls, _, rest), d, maxDepth) =
	    depth (rest, d+1, Int.max(maxDepth, d+length ls))
      fun emitLitExp (env, exp, code) = let
	    fun emitLitVals ([], _, code) = code
	      | emitLitVals (lit::r, d, code) = let
		  val instr = (case lit
			 of (LI_INT i) => emit_INT i
			  | (LI_STRING s) => emit_STR s
			  | (LI_VAR v) => let
			      fun f ([], _) = bug "unbound lvar"
			        | f (v'::r, d) = if (v = v') then d else f(r, d+1)
			      in
				emit_LIT(f (env, d))
			      end
			(* end case *))
		  in
		    emitLitVals (r, d+1, instr::code)
		  end
	    fun emitBlock (LI_RECORD, ls, code) =
		  emit_RECORD(length ls) :: emitLitVals(ls, 0, code)
	      | emitBlock (LI_VECTOR, ls, code) =
		  emit_VECTOR(length ls) :: emitLitVals(ls, 0, code)
	    fun emitF64Block (ls, code) =
		  emit_RAW64(map IEEERealConst.realconst ls) :: code
	    fun emitI32Block (ls, code) = emit_RAW32 ls :: code
	    in
	      case exp
	       of (LI_TOP ls) => emit_RETURN :: emitBlock(LI_RECORD, ls, code)
		| (LI_BLOCK(bk, ls, v, rest)) =>
		    emitLitExp (v::env, rest, emitBlock(bk, ls, code))
		| (LI_F64BLOCK(ls, v, rest)) =>
		    emitLitExp (v::env, rest, emitF64Block(ls, code))
		| (LI_I32BLOCK(ls, v, rest)) =>
		    emitLitExp (v::env, rest, emitI32Block(ls, code))
	      (* end case *)
	    end
      val maxDepth = depth (litExp, 0, 1)
      val code = emit_MAGIC
	    :: emit_DEPTH maxDepth
	    :: List.rev(emitLitExp([], litExp, []))
      in
	W8V.concat code
      end


(****************************************************************************
 *                    LIFTING LITERALS ON FLINT                             *
 ****************************************************************************)
(*
fun liftlits body = bug "FLINT version currently not implemented yet"

fun litsplit (FK_FCT, f, [(v, t)], body) = 
      if LT.ltp_str t then
        let val (nbody, lit, llt) = liftlits body
            val nt = LT.ltc_str ((LT.ltd_str t)@[llt])
         in ((FK_FCT, f, [(v, nt)], body), lit)
        end
      else bug "unexpected FLINT header in litsplit (case 1)"
  | litsplit _ = bug "unexpected FLINT header in litsplit (case 2)"
*)

(****************************************************************************
 *                    LIFTING LITERALS ON CPS                               *
 ****************************************************************************)
datatype info 
  = ZZ_STR of string
  | ZZ_FLT of string
  | ZZ_RCD of record_kind * value list

exception LitInfo

datatype rlit = RLIT of string * word
fun toRlit s = RLIT(s, HashString.hashString s)
fun fromRlit (RLIT(s, _)) = s
fun rlitcmp (RLIT(s1,i1), RLIT(s2,i2)) = 
  if i1 < i2 then LESS
  else if i1 > i2 then GREATER else String.compare(s1, s2)
structure RlitDict = RedBlackMapFn(struct type ord_key = rlit
                                        val compare = rlitcmp
                                 end)

(* lifting all literals from a CPS program *)
fun liftlits (body, root, offset) = 
  let (* the list of record, string, or real constants *)
      val m : info IntHashTable.hash_table = IntHashTable.mkTable(32, LitInfo)
      val freevars : lvar list ref = ref []
      fun addv x = (freevars := (x :: (!freevars)))

      (* check if an lvar is used by the main program *)
      val refset : Intset.intset = Intset.new()
      val used : lvar -> unit = Intset.add refset 
      val isUsed : lvar -> bool = Intset.mem refset

      (* memoize the information on which corresponds to what *)
      fun enter (v, i) = (IntHashTable.insert m (v, i); addv v)
      fun const (VAR v) = ((IntHashTable.lookup m v; true) handle _ => false)
        | const (INT _ | INT32 _ | REAL _ | STRING _) = true
        | const _ = bug "unexpected case in const"

      fun cstlit (VAR v) = ((IntHashTable.lookup m v; true) handle _ => false)
        | cstlit (REAL _ | STRING _) = true
        | cstlit _ = false

      (* register a string literal *)
      local val strs : string list ref = ref []
            val strsN : int ref = ref 0
            val sdict = ref (RlitDict.empty)
            val srtv = mkv()
            val srtval = VAR srtv
      in
      fun entStr s = 
        let val v = mkv()  (** should hash to remove duplicates **)
            val sd = !sdict
            val rlit = toRlit s
            val n = 
              (case RlitDict.find(sd, rlit)
                of SOME k => k
                 | _ => let val _ = (strs := (s :: (!strs)))
                            val k = !strsN
                            val _ = (strsN := (k+1)) 
                            val _ = (sdict := (RlitDict.insert(sd, rlit, k)))
                         in k
                        end)
         in (VAR v, fn ce => SELECT(n, srtval, v, BOGt, ce))
        end

(* old definition of entStr
        
        let val sd = !sdict
            val rlit = toRlit s
         in (case RlitDict.peek(sd, rlit)
              of SOME v => (VAR v, ident)
               | _ => let val v = mkv()
                          val _ = (enter(v, ZZ_STR s); used v)
                          val _ = (sdict := RlitDict.insert(sd, rlit, v))
                       in (VAR v, ident)
                      end)
        end
*)

      fun appStr () = 
        let fun g (a::r, z) = g(r, (STRING a)::z)  
              | g ([], z) = z (* reverse to reflecting the correct order *)
            val allStrs = !strs
         in case !strs
             of [] => ()
              | xs => (enter(srtv, ZZ_RCD(RK_RECORD, g(xs,[]))); used srtv)
        end
      end (* local of processing string literals *)
      
      (** a special treatment of real constants *)
      local val reals : string list ref = ref []
            val realsN : int ref = ref 0
            val rdict = ref (RlitDict.empty)
            val rrtv = mkv()
            val rrtval = VAR rrtv
      in				       
      fun entReal s = 
        let val v = mkv()  (** should hash to remove duplicates **)
            val rd = !rdict
            val rlit = toRlit s
            val n = 
              (case RlitDict.find(rd, rlit)
                of SOME k => k
                 | _ => let val _ = (reals := (s :: (!reals)))
                            val k = !realsN
                            val _ = (realsN := (k+1)) 
                            val _ = (rdict := (RlitDict.insert(rd, rlit, k)))
                         in k
                        end)
         in (VAR v, fn ce => SELECT(n, rrtval, v, FLTt, ce))
        end

      fun appReal () = 
        let fun g (a::r, z) = g(r, (REAL a)::z)  
              | g ([], z) = z (* reverse to reflecting the correct order *)
            val allReals = !reals
         in case !reals 
             of [] => ()
              | xs => (enter(rrtv, ZZ_RCD(RK_FBLOCK, g(xs,[]))); used rrtv)
        end
      end (* local of special treatment of real constants *)

      (* translation on the CPS values *)
      fun lpsv u = 
        (case u
          of REAL s => entReal s
           | STRING s => entStr s
           | VAR v => (used v; (u, ident))
           | _ => (u, ident))

      fun lpvs vs = 
        let fun g (u, (xs, hh)) = 
              let val (nu, nh) = lpsv u 
               in (nu::xs, nh o hh) 
              end
         in foldr g ([], ident) vs
        end

      (* if all fields of a record are "constant", then we lift it *)
      fun field ul = 
        let fun h ((x, OFFp 0)::r, z, rsflag) = 
                 if const x then h(r, x::z, rsflag orelse (cstlit x)) else NONE
              | h ([], z, rsflag) = if rsflag then SOME(rev z) else NONE
              | h _ = bug "unexpected case in field"
         in h (ul, [], false)
        end

      (* register a constant record *)
      fun record (rk, ul, v) =
        (case field ul
          of SOME xl => (enter(v, ZZ_RCD(rk, xl)); ident)
           | NONE =>
               let fun g ((u, p as OFFp 0), (r, hh)) = 
                         let val (nu, nh) = lpsv u
                          in ((nu, p)::r, nh o hh)
                         end
                     | g _ = bug "unexpected non-zero OFFp in record"
                   val (nl, hdr) = foldr g ([], ident) ul
                in fn ce => hdr(RECORD(rk, nl, v, ce))
               end)

      (* register a wrapped float literal *)
      fun wrapfloat (u, v, t) = 
        if const u then (enter(v, ZZ_RCD(RK_FBLOCK, [u])); ident)
        else let val (nu, hh) = lpsv u
              in (fn ce => hh(PURE(P.fwrap, [nu], v, t, ce)))
             end

      (* fetch out the literal information *)
      fun getInfo () = 
        let val _ = appReal()   (* register all Reals as a record *)
            val _ = appStr()   (* register all Strings as a record *)
            val allvars = !freevars
            val exports = List.filter isUsed allvars

            val toplit = 
              let fun g ([], z) = LI_TOP z
                    | g (x::r, z) = 
                         (case IntHashTable.lookup m x
                           of ZZ_STR s => g(r, (LI_STRING s)::z)
                            | _ => g(r, (LI_VAR x)::z))
               in g(exports, [])
              end

            fun mklit (v, lit) = let
		fun unREAL (CPS.REAL s) = s
		  | unREAL _ = bug "unREAL"
		fun unINT32 (CPS.INT32 w) = w
		  | unINT32 _ = bug "unINT32"
	    in
		case IntHashTable.lookup m v of
		    (ZZ_FLT _) => (* float is wrapped *)
                    bug "currently we don't expect ZZ_FLT in mklit"
                  (* LI_F64BLOCK([s], v, lit) *)
                  | (ZZ_STR s) => 
                    bug "currently we don't expect ZZ_STR in mklit"
                  (* lit   --- or we could inline string *)
                  | (ZZ_RCD(CPS.RK_FBLOCK, vs)) =>
		    LI_F64BLOCK(map unREAL vs, v, lit)
                 | (ZZ_RCD(CPS.RK_I32BLOCK, vs)) =>
		   LI_I32BLOCK(map unINT32 vs, v, lit)
                 | (ZZ_RCD(rk, vs)) => 
                     LI_BLOCK(rk2bk rk, map val2lit vs, v, lit)
	    end

            (** build up the literal structure *)
            val lit = foldl mklit toplit allvars

            val n = length exports
            val hdr = 
              if n = 0 then ident
              else let val rv = mkv()
                       val rval = VAR rv
                       val rhdr = 
                         fn ce => SELECT(offset, root, rv, PTRt(RPT n), ce)

                       fun mkhdr (v, (i, hh)) = 
                         let val nh = 
                               (case IntHashTable.lookup m v
                                 of (ZZ_FLT _) => bug "ZZ_FLT in mkhdr"
                                      (* (fn ce => 
                                           (SELECT(i, rval, w, PTRt(FPT 1),
                                            SELECT(0, VAR w, v, FLTt, ce)))) *)
                                  | (ZZ_STR s) => bug "ZZ_STR in mkhdr"
                                      (* (fn ce => 
                                            SELECT(i, rval, v, BOGt, ce)) *)
                                  | (ZZ_RCD (rk, vs)) =>
                                      let val n = length vs
                                          val t = 
                                            case rk 
                                             of RK_FBLOCK => PTRt(FPT n)
                                              | RK_VECTOR => BOGt
                                              | _ => PTRt(RPT n)
                                       in fn ce => SELECT(i, rval, v, t, ce)
                                      end)
                          in (i+1, hh o nh)
                         end
                    in #2 (foldr mkhdr (0, rhdr) exports)
                   end
         in (lit, hdr)
        end (* function getInfo *)

      fun lpfn (fk, f, vl, cl, e) = (fk, f, vl, cl, loop e)

      and loop ce =
        (case ce
          of RECORD (rk, ul, v, e) => record (rk, ul, v) (loop e)
           | SELECT (i, u, v, t, e) => 
               let val (nu, hh) = lpsv u
                in hh(SELECT(i, nu, v, t, loop e))
               end
           | OFFSET _ => bug "unexpected OFFSET in loop"
           | APP (u, ul) => 
               let val (nu, h1) = lpsv u
                   val (nl, h2) = lpvs ul
                in h1(h2(APP(nu, nl)))
               end
           | FIX (fns, e) => FIX(map lpfn fns, loop e)
           | SWITCH (u, v, es) => 
               let val (nu, hh) = lpsv u
                in hh(SWITCH(nu, v, map loop es))
               end
           | BRANCH (p, ul, v, e1, e2) => 
               let val (nl, hh) = lpvs ul
                in hh(BRANCH(p, nl, v, loop e1, loop e2))
               end
           | SETTER (p, ul, e) => 
               let val (nl, hh) = lpvs ul
                in hh(SETTER(p, nl, loop e))
               end
           | LOOKER (p, ul, v, t, e) =>
               let val (nl, hh) = lpvs ul
                in hh(LOOKER(p, nl, v, t, loop e))
               end
           | ARITH (p, ul, v, t, e) =>
               let val (nl, hh) = lpvs ul
                in hh(ARITH(p, nl, v, t, loop e))
               end
           | PURE (P.fwrap, [u], v, t, e) => wrapfloat (u, v, t) (loop e)
           | PURE (p, ul, v, t, e) => 
               let val (nl, hh) = lpvs ul
                in hh(PURE(p, nl, v, t, loop e))
               end
	   | RCC (k, l, p, ul, vtl, e) =>
	       let val (nl, hh) = lpvs ul
	        in hh(RCC(k, l, p, nl, vtl, loop e))
	       end)

      val newbody = loop body
      val (lit, hdr) = getInfo ()
   in (hdr newbody, lit)
  end

(* the main function *)
fun litsplit (fk, f, vl as [_,x], [CNTt, t as PTRt(RPT n)], body) = 
      let val nt = PTRt(RPT (n+1))
          val (nbody, lit) = liftlits(body, VAR x, n)
       in ((fk, f, vl, [CNTt, nt], nbody), lit)
      end
  | litsplit _ = bug "unexpected CPS header in litsplit"

end (* toplevel local *)
end (* Literals *)
