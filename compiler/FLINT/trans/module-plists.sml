(* module-plist.sml
 *
 * (C) 2001 Lucent Technologies, Bell Labs
 *)

(* module property lists.  Used only in translate *)

structure ModulePropLists =
struct

  val { getFn = strEntityLty, setFn = setStrEntityLty, ... } = let
      fun holder (e: Modules.strEntity) = #properties e
      fun init _ = NONE: (PLambdaType.lty * DebIndex.depth) option
  in
      PropList.newProp (holder, init)
  end

  val { getFn = fctEntityLty, setFn = setFctEntityLty, ... } = let
      fun holder (e: Modules.fctEntity) = #properties e
      fun init _ = NONE: (PLambdaType.lty * DebIndex.depth) option
  in
      PropList.newProp (holder, init)
  end

  val { getFn = sigLty, setFn = setSigLty, ... } = let
      fun holder (e: Modules.sigrec) = #properties e
      fun init _ = NONE: (PLambdaType.lty * DebIndex.depth) option
  in
      PropList.newProp (holder, init)
  end

  val { getFn = dtfLtyc, setFn = setDtfLtyc, ... } = let
      fun holder (f: Types.dtypeFamily) = #properties f
      fun init _ = NONE: (PLambdaType.tyc * DebIndex.depth) option
  in
      PropList.newProp (holder, init)
  end

(* [DBM:2016/9/15] This is now defined in SigPropList (ElabData/basics/sig-plist.sml)
  val { getFn = sigBoundeps, setFn = setSigBoundeps, ... } = let
      fun holder (e: Modules.sigrec) = #properties e
      fun init _ = NONE: (EntPath.entPath * PLambdaType.tkind) list option
  in
      PropList.newProp (holder, init)
  end
*)
						       
end (* structure ModulePropLists *)
