functor SparcPseudoInstrs
   (Instr : SPARCINSTR where Region=CPSRegions) : SPARC_PSEUDO_INSTR = 
struct
  structure I = Instr
  structure C = Instr.C

  type format1 =
       {r:CellsBasis.cell, i:I.operand, d:CellsBasis.cell} *
       (I.operand -> CellsBasis.cell) -> I.instruction list

  type format2 =
       {i:I.operand, d:CellsBasis.cell} *
       (I.operand -> CellsBasis.cell) -> I.instruction list

  fun error msg = MLRiscErrorMsg.impossible ("SparcPseudoInstrs."^msg)

  val delta = SparcSpec.framesize	(* initial value of %fp - %sp *)

  (* runtime system dependent; the numbers are relative to %sp but
   * we need offsets relative to %fp, hence the adjustment by delta *)
  val floatTmpOffset = I.IMMED (88 - delta)
  val umulOffset = I.IMMED (80 - delta)
  val smulOffset = I.IMMED (72 - delta)
  val udivOffset = I.IMMED (84 - delta)
  val sdivOffset = I.IMMED (76 - delta)

  val stack = CPSRegions.stack

  val native = true  (* use native versions of the instructions? *)

  fun umul_native({r, i, d}, reduceOpnd) =
      [I.arith{a=I.UMUL,r=r,i=i,d=d}]

  val TNE = I.ticc{t=I.BNE,cc=I.ICC,r=C.r0,i=I.IMMED 7}
  val TVS = I.ticc{t=I.BVS,cc=I.ICC,r=C.r0,i=I.IMMED 7}

      (* overflows iff Y != (d ~>> 31) *)
  fun smult_native({r, i, d}, reduceOpnd) =
      let val t1 = C.newReg()
          val t2 = C.newReg()
      in  [I.arith{a=I.SMUL,r=r,i=i,d=d},
           I.shift{s=I.SRA,r=d,i=I.IMMED 31,d=t1},
           I.rdy{d=t2},
           I.arith{a=I.SUBCC,r=t1,i=I.REG t2,d=C.r0},
           TNE
          ] 
      end

  fun smul_native({r, i, d}, reduceOpnd) =
      [I.arith{a=I.SMUL,r=r,i=i,d=d}]

  fun udiv_native({r,i,d},reduceOpnd) = 
      [I.wry{r=C.r0,i=I.REG C.r0},
       I.arith{a=I.UDIV,r=r,i=i,d=d}]

   (* May overflow if MININT div -1 *)
  fun sdivt_native({r,i,d},reduceOpnd) = 
      let val t1 = C.newReg()
      in  [I.shift{s=I.SRA,r=r,i=I.IMMED 31,d=t1},
           I.wry{r=t1,i=I.REG C.r0},
           I.arith{a=I.SDIVCC,r=r,i=i,d=d},
           TVS
          ]
      end

  fun sdiv_native({r,i,d},reduceOpnd) =
      let val t1 = C.newReg()
      in  [I.shift{s=I.SRA,r=r,i=I.IMMED 31,d=t1},
           I.wry{r=t1,i=I.REG C.r0},
           I.arith{a=I.SDIV,r=r,i=i,d=d}
          ]
      end

  (* 
   * Registers %o2, %o3 are used to pass arguments to ml_mul and ml_div 
   * Result is returned in %o2.
   *)
  val r10 = C.GPReg 10
  val r11 = C.GPReg 11

  fun callRoutine(offset,reduceOpnd,r,i,d) =   
  let val addr = C.newReg()
      val defs = C.addReg(r10,C.empty) 
      val uses = C.addReg(r10,C.addReg(r11,C.empty))
      fun copy{dst, src, tmp} = 
	  I.COPY{k=CellsBasis.GP, sz=32, dst=dst, src=src, tmp=tmp}
  in
      [copy{src=[r,reduceOpnd i],dst=[r10,r11],tmp=SOME(I.Direct(C.newReg()))},
       I.load{l=I.LD,r=C.frameptrR,i=offset,d=addr,mem=stack},
       I.jmpl{r=addr,i=I.IMMED 0,d=C.linkReg,defs=defs,uses=uses,
              cutsTo=[],nop=true,mem=stack},
       copy{src=[r10],dst=[d],tmp=NONE}
      ]
  end

  fun umul({r, i, d}, reduceOpnd) = callRoutine(umulOffset,reduceOpnd,r,i,d)
  fun smultrap({r, i, d}, reduceOpnd) = callRoutine(smulOffset,reduceOpnd,r,i,d)
  fun udiv({r, i, d}, reduceOpnd) = callRoutine(udivOffset,reduceOpnd,r,i,d)
  fun sdivtrap({r, i, d}, reduceOpnd) = callRoutine(sdivOffset,reduceOpnd,r,i,d)

  fun cvti2d({i, d}, reduceOpnd) = 
      [I.store{s=I.ST,r=C.frameptrR,i=floatTmpOffset,d=reduceOpnd i,mem=stack},
       I.fload{l=I.LDF,r=C.frameptrR,i=floatTmpOffset,d=d,mem=stack},
       I.fpop1{a=I.FiTOd,r=d,d=d}
      ]
  fun cvti2s _ = error "cvti2s"
  fun cvti2q _ = error "cvti2q"

     (* Generate native versions of the instructions *)
  val umul32 = if native then umul_native else umul
  val smul32 : format1 =
      if native then smul_native else (fn _ => error "smul32")
  val smul32trap = if native then smult_native else smultrap
  val udiv32 = if native then udiv_native else udiv
  val sdiv32 : format1 =
      if native then sdiv_native else (fn _ => error "sdiv32")
  val sdiv32trap = if native then sdivt_native else sdivtrap

  val overflowtrap32 = (* tvs 0x7 *)
                       [I.ticc{t=I.BVS,cc=I.ICC,r=C.r0,i=I.IMMED 7}]
  val overflowtrap64 = [] (* not needed *)


end

