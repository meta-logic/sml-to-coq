(* machspec.sml
 *
 * COPYRIGHT (c) 1995 AT&T Bell Laboratories.
 *
 *)

structure HppaSpec : MACH_SPEC = 
struct

    open DefaultMachSpec

    val architecture	= "hppa"
    val spillAreaSz	= 4000
    val initialSpillOffset = 116
    val numRegs		= 17	(* length HppaCpsRegs.miscregs + 3 *)
    val numFloatRegs	= 25
      (* length HppaCpsRegs.floatregs + length HppaCpsRegs.savedfpregs *)
    val bigEndian	= true
    val startgcOffset	= ~28
    val constBaseRegOffset = 8192

    val ML_STATE_OFFSET = ~40
    val VProcOffMSP = 4
    val InMLOffVSP = 8
    val LimitPtrMaskOffVSP = 200
end
