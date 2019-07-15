(* backend/amd64-stdcall.sml
 *
 * (C) 2006 The Fellowship of SML/NJ
 *)
local
    (* turn on "fast-fp"... *)
    val _ = MLRiscControl.flag "x86-fast-fp" := true
in
structure AMD64StdCallBackend =
          BackendFn (structure M = AMD64MC (structure CCallParams = struct
					      val frameAlign = 16 (* 4? *)
					      val returnSmallStructsInRegs = false
					    end
                                          val abi_variant = NONE)
		     val cproto_conv = "stdcall")
end
