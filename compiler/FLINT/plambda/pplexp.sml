(* Copyright 1997 by Bell Laboratories *)
(* pplexp.sml *)

(* _Real_ pretty printing for plambda lexp *)

signature PPLEXP =
sig

  val conToString : PLambda.con -> string
  val ppLexp : int -> PrettyPrintNew.stream -> PLambda.lexp -> unit
  val ppMatch : StaticEnv.staticEnv ->  
                  (Absyn.pat * PLambda.lexp) list -> unit
  val ppFun : PrettyPrintNew.stream -> PLambda.lexp -> LambdaVar.lvar -> unit

  val stringTag : PLambda.lexp -> string

end (* signature PPLEXP *)


structure PPLexp : PPLEXP = 
struct

local structure A = Absyn
      structure DA = Access
      structure S = Symbol
      structure PP = PrettyPrintNew
      structure PU = PPUtilNew
      structure LT = PLambdaType
      open PLambda PPUtilNew
in 

fun bug s = ErrorMsg.impossible ("PPLexp: "^s)

val lvarName = LambdaVar.lvarName

fun app2(f, [], []) = ()
  | app2(f, a::r, b::z) = (f(a, b); app2(f, r, z))
  | app2(f, _, _) = bug "unexpected list arguments in function app2"
  
fun conToString (DATAcon((sym, _, _), _, v)) = ((S.name sym) ^ "." ^ (lvarName v))
  | conToString (INTcon i) = Int.toString i
  | conToString (INT32con i) = "(I32)" ^ (Int32.toString i)
  | conToString (INTINFcon i) = "(II)" ^ IntInf.toString i
  | conToString (WORDcon i) = "(W)" ^ (Word.toString i)
  | conToString (WORD32con i) = "(W32)" ^ (Word32.toString i)
  | conToString (REALcon r) = r
  | conToString (STRINGcon s) = PU.mlstr s
  | conToString (VLENcon n) = Int.toString n

(** use of complex in printLexp may lead to stupid n^2 behavior. *)
fun complex le = 
  let fun h l = List.exists g l

      and g (FN(_, _, b)) = g b
        | g (FIX(vl, _, ll, b)) = true
        | g (APP(FN _, _)) = true
        | g (APP(l, r)) = g l orelse g r

        | g (LET _) = true
        | g (TFN(_, b)) = g b
        | g (TAPP(l, [])) = g l 
        | g (TAPP(l, _)) = true
        | g (GENOP(_,_,_,_)) = true
        | g (PACK(_, _, _, l)) = g l
       
        | g (RECORD l) = h l
        | g (SRECORD l) = h l
        | g (VECTOR (l, _)) = h l
        | g (SELECT(_, l)) = g l

        | g (SWITCH _) = true
        | g (CON(_, _, l)) = true
(*      | g (DECON(_, _, l)) = true *)

        | g (HANDLE _) = true 
        | g (RAISE(l, _)) = g l
        | g (ETAG (l, _)) = g l

        | g (WRAP(_, _, l)) = g l
        | g (UNWRAP(_, _, l)) = g l
        | g _ = false

   in g le
  end

fun ppLexp (pd:int) ppstrm (l: lexp): unit = 
    let val {openHOVBox, openHVBox, closeBox, break, newline, pps, ppi, ...} =
            en_pp ppstrm
(*
	val ppList' : {pp:PP.stream -> 'a -> unit, sep: string} -> 'a list -> unit =
              fn x => PPLty.ppList ppstrm x
	       (* eta-expansion of ppList to avoid value restriction *) 
*)
        val ppLexp' = ppLexp (pd-1) ppstrm
        val ppLty' = PPLty.ppLty (pd-1) ppstrm
        val ppTyc' = PPLty.ppTyc (pd-1) ppstrm
        fun br0 n = PP.break ppstrm {nsp=0,offset=n}
        fun br1 n = PP.break ppstrm {nsp=1,offset=n}
        fun br(n,m) = PP.break ppstrm {nsp=n,offset=m}
        fun ppClosedSeq (start,sep,close) ppfn elems =
            PU.ppClosedSequence ppstrm
              {front = (fn s => PP.string s start),
               back = (fn s => PP.string s close),
               sep = (fn s => PP.string s sep),
               pr = ppfn,
               style = PU.INCONSISTENT}
              elems

        fun ppl pd (VAR v) = pps (lvarName v)
          | ppl pd (INT i) = ppi i
          | ppl pd (WORD i) = (pps "(W)"; pps (Word.toString i))
          | ppl pd (INT32 i) = (pps "(I32)"; pps(Int32.toString i))
          | ppl pd (WORD32 i) = (pps "(W32)"; pps(Word32.toString i))
          | ppl pd (REAL s) = pps s
          | ppl pd (STRING s) = pps (mlstr s)
          | ppl pd (ETAG (l,_)) = ppl pd l

          | ppl pd (RECORD l) =
            if pd < 1 then pps "<REC>" else
              (openHOVBox 3;
               pps "RCD";
               ppClosedSeq ("(",",",")") (fn s => ppl (pd-1)) l;
               closeBox ())

          | ppl ps (SRECORD l) =
            if pd < 1 then pps "<REC>" else
              (openHOVBox 4;
               pps "SRCD";
               ppClosedSeq ("(",",",")") (fn s => ppl (pd-1)) l;
               closeBox ())

          | ppl pd (le as VECTOR (l, _)) =
            if pd < 1 then pps "<VEC>" else
              (openHOVBox 3;
               pps "VEC";
               ppClosedSeq ("(",",",")") (fn s => ppl (pd-1)) l;
               closeBox ())

          | ppl pd (PRIM(p,t,ts)) = 
            if pd < 1 then pps "<PRIM>" else
            (openHOVBox 4;
              pps "PRM(";
              openHOVBox 0;
               pps(PrimOp.prPrimop p); pps ","; br1 0;
               ppLty' t; 
	       pps ",";
	       br1 0;
               ppClosedSeq ("[",",","]") (PPLty.ppTyc (pd-1)) ts;
              closeBox();
              pps ")";
             closeBox ())

          | ppl pd (l as SELECT(i, _)) =
            if pd < 1 then pps "<SEL>" else
            let fun gather(SELECT(i,l)) =
                      let val (more,root) = gather l
                       in  (i :: more,root)
                      end
                  | gather l = (nil, l)

                val (path,root) = gather l
                fun ipr (i:int) = pps(Int.toString i)
             in openHOVBox 2;
                ppl (pd-1) root;
                ppClosedSeq ("[",",","]") (fn s => ppi) (rev path);
                closeBox ()
            end

          | ppl pd (FN(v,t,l)) = 
            if pd < 1 then pps "<FN>" else
            (openHOVBox 3; pps "FN(";
              pps(lvarName v); pps ":"; br1 0; ppLty' t; pps ",";
              if complex l then newline() else ();
              ppl (pd-1) l; pps ")";
             closeBox())

          | ppl pd (CON((s, c, lt), ts, l)) = 
            if pd < 1 then pps "<FN>" else
            (openHOVBox 4;
              pps "CON(";
              openHOVBox 1; pps "("; pps(S.name s); pps ",";
               pps(DA.prRep c); pps ",";
               ppLty' lt; pps ")";
              closeBox ();
              pps ","; br1 0;
              ppClosedSeq ("[",",","]") (PPLty.ppTyc (pd-1)) ts;
              pps ","; br1 0;
              ppl (pd-1) l; pps ")";
             closeBox())

(*
        | ppl (DECON((s, c, lt), ts, l)) = 
            (pps "DECON(("; pps(S.name s); pps ","; ppsrep c; pps ",";
             ppLty lt; pps "), ["; plist(prTyc, ts, ","); pps "], ";
             if complex l then (indent 4; ppl l; pps ")"; undent 4)
             else (g l; pps ")"))
*)
          | ppl pd (APP(FN(v,_,l),r)) = 
            if pd < 1 then pps "<LET*>" else
            (openHOVBox 5;
              pps "(APP)";
              ppl (pd-1) (LET(v, r, l));
             closeBox())
        
          | ppl pd (LET(v, r, l)) = 
            if pd < 1 then pps "<LET>" else
            (openHVBox 2;
              openHOVBox 4;
               pps (lvarName v); br1 0; pps "="; br1 0; ppl (pd-1) r;
              closeBox();
              newline();
              ppl (pd-1) l;
             closeBox())

          | ppl pd (APP(l, r)) = 
            if pd < 1 then pps "<APP>" else
            (pps "APP(";
             openHVBox 0;
             ppl (pd-1) l; pps ","; br1 0; ppl (pd-1) r;
             closeBox();
             pps ")")

          | ppl pd (TFN(ks, b)) = 
            if pd < 1 then pps "<TFN>" else
            (openHOVBox 0;
             pps "TFN(";
             openHVBox 0;
             ppClosedSeq ("(",",",")") (PPLty.ppTKind (pd-1)) ks; br1 0;
             ppl (pd-1) b;
             closeBox();
             pps ")";
             closeBox())
                  
          | ppl pd (TAPP(l, ts)) = 
            if pd < 1 then pps "<TAP>" else
            (openHOVBox 0;
              pps "TAPP(";
              openHVBox 0;
               ppl (pd-1) l; br1 0;
               ppClosedSeq ("[",",","]") (PPLty.ppTyc (pd-1)) ts;
              closeBox();
              pps ")";
             closeBox()) 

          | ppl pd (GENOP(dict, p, t, ts)) = 
            if pd < 1 then pps "<GEN>" else
            (openHOVBox 4;
              pps "GEN(";
              openHOVBox 0;
               pps(PrimOp.prPrimop p); pps ","; br1 0;
               ppLty' t; br1 0;
               ppClosedSeq ("[",",","]") (PPLty.ppTyc (pd-1)) ts;
              closeBox();
              pps ")";
             closeBox ())

          | ppl pd (PACK(lt, ts, nts, l)) = 
            if pd < 1 then pps "<PACK>" else
            (openHOVBox 0;
              pps "PACK("; 
              openHVBox 0;
               openHOVBox 0;
                app2 (fn (tc,ntc) =>
                        (pps "<"; ppTyc' tc; pps ","; ppTyc' ntc;
                         pps ">,"; br1 0),
                     ts, nts);
               closeBox(); br1 0;
               ppLty' lt; pps ","; br1 0;
               ppl (pd-1) l;
              closeBox();
              pps ")";
             closeBox())

          | ppl pd (SWITCH (l,_,llist,default)) =
            if pd < 1 then pps "<SWI>" else
            let fun switch [(c,l)] =
                      (openHOVBox 2;
                       pps (conToString c); pps " =>"; br1 0; ppl (pd-1) l;
                       closeBox())
                  | switch ((c,l)::more) = 
                      (openHOVBox 2;
                       pps (conToString c); pps " =>"; br1 0; ppl (pd-1) l;
                       closeBox();
                       newline();
                       switch more)
                  | switch [] = () (* bug "unexpected case in switch" *)

             in openHOVBox 3;
                pps "SWI";
                ppl (pd-1) l; newline();
                pps "of ";
                openHVBox 0;
                switch llist;
                case (default,llist)
                 of (NONE,_) => ()
                  | (SOME l,nil) => (openHOVBox 2; pps "_ =>"; br1 0; ppl (pd-1)l;
                                     closeBox())
                  | (SOME l,_) => (newline();
                                   openHOVBox 2;
                                   pps "_ =>"; br1 0; ppl (pd-1) l;
                                   closeBox());
                closeBox();
                closeBox()
            end

          | ppl pd (FIX(varlist,ltylist,lexplist,lexp)) =
            if pd < 1 then pps "<FIX>" else
            let fun flist([v],[t],[l]) =
                      let val lv = lvarName v
                          val len = size lv + 2
                       in pps lv; pps ": "; ppLty' t; pps " :: ";
                          ppl (pd-1) l
                      end
                  | flist(v::vs,t::ts,l::ls) =
                      let val lv = lvarName v
                          val len = size lv + 2
                       in pps lv; pps ": "; ppLty' t; pps " :: ";
                          ppl (pd-1) l; newline();
                          flist(vs,ts,ls)
                      end
                  | flist(nil,nil,nil) = ()
                  | flist _ = bug "unexpected cases in flist"

             in openHOVBox 0;
                pps "FIX(";
                openHVBox 0; flist(varlist,ltylist,lexplist); closeBox();
                newline(); pps "IN ";
                ppl (pd-1) lexp;
                pps ")";
                closeBox()
            end

          | ppl pd (RAISE(l,t)) = 
            if pd < 1 then pps "<RAISE>" else
            (openHOVBox 0;
              pps "RAISE(";
              openHVBox 0;
               ppLty' t; pps ","; br1 0; ppl (pd-1) l;
              closeBox();
              pps ")";
             closeBox())

          | ppl pd (HANDLE (lexp,withlexp)) =
            if pd < 1 then pps "<HANDLE>" else
            (openHOVBox 0;
             pps "HANDLE"; br1 0; ppl (pd-1) lexp;
             newline();
             pps "WITH"; br1 0; ppl (pd-1) withlexp;
             closeBox())

          | ppl pd (WRAP(t, _, l)) = 
            if pd < 1 then pps "<WRAP>" else
            (openHOVBox 0;
              pps "WRAP("; ppTyc' t; pps ",";
              newline();
              ppl (pd-1) l; 
              pps ")";
             closeBox())

          | ppl pd (UNWRAP(t, _, l)) = 
            if pd < 1 then pps "<WRAP>" else
            (openHOVBox 0;
              pps "UNWRAP("; ppTyc' t; pps ",";
              newline();
              ppl (pd-1) l; 
              pps ")";
             closeBox())

   in ppl pd l; newline(); newline()
  end

(* ppMatch : StaticEnv.statenv * (Absyn.pat * lexp) list -> unit *)
fun ppMatch env (rules: (Absyn.pat * lexp) list) =
    let val pd = !Control.Print.printDepth
        fun ppMatch' ppstrm ((p,r)::more) = 
                 (PP.openHVBox ppstrm (PP.Rel 0);
                   PP.openHOVBox ppstrm (PP.Rel 2);
                    PPAbsyn.ppPat env ppstrm (p,pd);
                    PP.string ppstrm " =>"; PP.break ppstrm {nsp=1,offset=2};
                    ppLexp pd ppstrm r;
                   PP.closeBox ppstrm;
                   PP.newline ppstrm;
                   ppMatch' ppstrm more;
                  PP.closeBox ppstrm)
               | ppMatch' _ [] = ()
    in PP.with_default_pp (fn ppstrm => ppMatch' ppstrm rules)
    end

fun ppFun ppstrm l v =
  let fun last (DA.LVAR x) = x 
        | last (DA.PATH(r,_)) = last r
        | last _ = bug "unexpected access in last"

      fun find le =
        case le
          of VAR w => 
               if (v=w)
               then PU.pps ppstrm ("VAR " ^ lvarName v ^ " is free in <lexp>\n")
               else ()
           | l as FN(w,_,b) => if v=w then ppLexp 20 ppstrm l else find b
           | l as FIX(vl,_,ll,b) =>
             if List.exists (fn w => v=w) vl then ppLexp 20 ppstrm l
             else (app find ll; find b)
           | APP(l,r) => (find l; find r)
           | LET(w,l,r) => (if v=w then ppLexp 20 ppstrm l else find l; find r)
           | PACK(_,_,_,r) => find r
           | TFN(_, r) => find r
           | TAPP(l, _) => find l
           | SWITCH (l,_,ls,d) =>
             (find l; app (fn(_,l) => find l) ls;
              case d of NONE => () | SOME l => find l)
           | RECORD l => app find l 
           | SRECORD l => app find l 
           | VECTOR (l, t) => app find l 
           | SELECT(_,l) => find l
           | CON((_, DA.EXN p, _), _, e) => (find(VAR(last p)); find e)
           | CON(_,_,e) => find e
(*
         | DECON((_, DA.EXN p, _), _, e) => (find(VAR(last p)); find e)
         | DECON(_,_,e) => find e  
*)
           | HANDLE(e,h) => (find e; find h) 
           | RAISE(l,_) => find l
           | INT _ => () | WORD _ => () 
           | INT32 _ => () | WORD32 _ => () 
           | STRING _ => () | REAL _ => ()
           | ETAG (e,_) => find e
           | PRIM _ => ()
           | GENOP ({default=e1,table=es}, _, _, _) => 
             (find e1; app (fn (_, x) => find x) es)
           | WRAP(_, _, e) => find e
           | UNWRAP(_, _, e) => find e

   in find l
  end

fun stringTag (VAR _) = "VAR"
  | stringTag (INT _) = "INT"
  | stringTag (INT32 _) = "INT32"
  | stringTag (WORD _) = "WORD"
  | stringTag (WORD32 _) = "WORD32"
  | stringTag (REAL _) = "REAL"
  | stringTag (STRING _) = "STRING"
  | stringTag (PRIM _) = "PRIM"
  | stringTag (GENOP _) = "GENOP"
  | stringTag (FN _) = "FN"
  | stringTag (FIX _) = "FIX"
  | stringTag (APP _) = "APP"
  | stringTag (LET _) = "LET"
  | stringTag (TFN _) = "TFN"
  | stringTag (TAPP _) = "TAPP"
  | stringTag (ETAG _) = "ETAG"
  | stringTag (RAISE _) = "RAISE"
  | stringTag (HANDLE _) = "HANDLE"
  | stringTag (CON _) = "CON"
  | stringTag (SWITCH _) = "SWITCH"
  | stringTag (VECTOR _) = "VECTOR"
  | stringTag (RECORD _) = "RECORD"
  | stringTag (SRECORD _) = "SRECORD"
  | stringTag (SELECT _) = "SELECT"
  | stringTag (PACK _) = "PACK"
  | stringTag (WRAP _) = "WRAP"
  | stringTag (UNWRAP _) = "UNWRAP"

end (* toplevel local *)
end (* struct PPLexp *)
