(*
 * PPC specific backend
 *)
structure PPCCG = 
  MachineGen
  ( structure MachSpec   = PPCSpec
    val abi_variant      = NONE
    structure T		 = PPCMLTree
    structure CB	 = CellsBasis
    structure ClientPseudoOps = PPCClientPseudoOps
    structure PseudoOps  = PPCPseudoOps
    structure Ext        = SMLNJMLTreeExt(* generic extension *)
    structure CpsRegs    = PPCCpsRegs
    structure InsnProps  = PPCProps
    structure Asm        = PPCAsmEmitter
    structure Shuffle    = PPCShuffle

    structure CCalls     =
      PPCMacOSX_CCalls (structure T = PPCMLTree)

    structure OmitFramePtr = struct
      structure CFG=PPCCFG
      structure I=PPCInstr
      val vfp = PPCCpsRegs.vfp
      (* no rewriting necessary, backend does not change sp *)
      fun omitframeptr _ = ()
    end

    structure MLTreeComp=
       PPC(structure PPCInstr = PPCInstr
           structure PPCMLTree = PPCMLTree
           structure PseudoInstrs=
               PPCPseudoInstr(structure Instr=PPCInstr)
           structure ExtensionComp = SMLNJMLTreeExtComp
               (structure I = PPCInstr
                structure T = PPCMLTree
		structure CFG = PPCCFG
		structure TS = PPCMLTreeStream
               )
           val bit64mode=false
           val multCost=ref 6 (* an estimate *)
         )

    structure Jumps =
       PPCJumps(structure Instr=PPCInstr
		structure MLTreeEval=PPCMLTreeEval
                structure Shuffle=PPCShuffle)

    structure BackPatch =
       BBSched2(structure CFG = PPCCFG
                structure Jumps = Jumps
		structure Props = PPCProps
                structure Emitter = PPCMCEmitter)

    structure RA = 
       RISC_RA
         (structure I         = PPCInstr
          structure CFG       = PPCCFG
          structure CpsRegs   = PPCCpsRegs
          structure InsnProps = InsnProps 
          structure Rewrite   = PPCRewrite(PPCInstr) 
	  structure SpillInstr= PPCSpillInstr(PPCInstr)
          structure Asm       = PPCAsmEmitter
          structure SpillHeur = ChaitinSpillHeur
          structure Spill     = RASpill(structure InsnProps = InsnProps
                                        structure Asm = PPCAsmEmitter)

          structure SpillTable = SpillTable(PPCSpec)

          val architecture = PPCSpec.architecture

	  datatype spillOperandKind = SPILL_LOC | CONST_VAL
	  type spill_info = unit

          fun beforeRA _ = SpillTable.spillInit()

          val sp = I.C.stackptrR
          val spill = CPSRegions.spill

          fun pure _ = false

          structure Int = 
          struct
             val avail     = PPCCpsRegs.availR
             val dedicated = PPCCpsRegs.dedicatedR

	     fun mkDisp loc = T.LI(T.I.fromInt(32, SpillTable.getRegLoc loc))

             fun spillLoc{info, an, cell, id} = 
		  {opnd=I.Displace{base=sp, disp=mkDisp(RAGraph.FRAME id), mem=spill},
		   kind=SPILL_LOC}

             val mode = RACore.NO_OPTIMIZATION
         end
         structure Float =
         struct
             val avail     = PPCCpsRegs.availF
             val dedicated = PPCCpsRegs.dedicatedF

	     fun mkDisp loc = T.LI(T.I.fromInt(32, SpillTable.getFregLoc loc))

	     fun spillLoc(S, an, loc) = 
		I.Displace{base=sp, disp=mkDisp(RAGraph.FRAME loc), mem=spill}

             val mode = RACore.NO_OPTIMIZATION
         end
        )
  )
