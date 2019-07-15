(* mk-record.sig --- translate a CPS.RECORD to MLRISC
 *
 * COPYRIGHT (c) 1996 AT&T Bell Laboratories.
 *
 *)

signature MK_RECORD = sig
  structure T : MLTREE

  val record : 
    {desc     : T.rexp, 
     fields   : (T.rexp * CPS.accesspath) list,
     mem      : CPSRegions.region,
     hp       : int,              (* heap pointer offset (from allocptr) *)
     emit     : T.stm -> unit,
     markPTR  : T.rexp -> T.rexp, (* mark this as an ml object ptr (for gc) *) 
     markComp : T.rexp -> T.rexp  (* mark the component type (for gc) *)
    } -> int

  val frecord : 
    {desc     : T.rexp, 
     fields   : (T.mlrisc * CPS.accesspath) list,
     mem      : CPSRegions.region,
     hp       : int,
     emit     : T.stm -> unit,
     markPTR  : T.rexp -> T.rexp,
     markComp : T.fexp -> T.fexp
    } -> int
end

