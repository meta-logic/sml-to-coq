(* hppagen.sml
 *
 * COPYRIGHT (c) 1996 Bell Laboratories.
 *
 *)

structure HppaMC = 
  FLINTComp(
    structure Gen = HppaCG
    fun collect epthunk = (HppaCG.finish ();
			   CodeString.getCodeString (epthunk ())))


