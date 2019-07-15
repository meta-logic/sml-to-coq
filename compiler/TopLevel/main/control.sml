(* control.sml *)
(* COPYRIGHT (c) 1995 AT&T Bell Laboratories *)

(* Match compiler controls *)
structure Control_MC : MCCONTROL =
struct

  val priority = [10, 10, 4]
  val obscurity = 2
  val prefix = "compiler-mc"

  val registry = ControlRegistry.new { help = "match compiler settings" }

  val _ = BasicControl.nest (prefix, registry, priority)

  val bool_cvt = ControlUtil.Cvt.bool

  val nextpri = ref 0

  fun flag (n, h, d) = let
      val r = ref d
      val p = !nextpri
      val ctl = Controls.control { name = n,
                                   pri = [p],
                                   obscurity = obscurity,
                                   help = h,
                                   ctl = r }
  in
      nextpri := p + 1;
      ControlRegistry.register
          registry
          { ctl = Controls.stringControl bool_cvt ctl,
            envName = SOME (ControlUtil.EnvName.toUpper "COMPILER_MC_" n) };
      r
  end

  val printArgs = flag ("print-args", "arguments print mode", false)
  val printRet = flag ("print-ret", "return print mode", false)
  val bindNoVariableWarn =
      flag ("nobind-warn", "whether to warn if no variables get bound",
            false)
  val bindNonExhaustiveWarn =
      flag ("warn-non-exhaustive-bind",
            "whether to warn on non-exhaustive bind", true)
  val bindNonExhaustiveError =
      flag ("error-non-exhaustive-bind",
            "whether non-exhaustive bind is an error", false)
  val matchNonExhaustiveWarn =
      flag ("warn-non-exhaustive-match",
            "whether to warn on non-exhaustive match", true)
  val matchNonExhaustiveError =
      flag ("error-non-exhaustive-match",
            "whether non-exhaustive match is an error", false)
  (* matchExhaustiveError overrides matchExhaustiveWarn *)
  val matchRedundantWarn =
      flag ("warn-redundant", "whether to warn on redundant matches", true)
  val matchRedundantError =
      flag ("error-redundant", "whether a redundant match is an error", true)
  (* matchRedundantError overrides matchRedundantWarn *)
(*
    val expandResult =
	flag ("expand-result", "whether to expand result of match", false)
*)
end (* structure Control_MC *)


(* Code generation controls (including some used in FLINT?) *)
structure Control_CG : CGCONTROL =
struct
  val priority = [10, 11, 2]
  val obscurity = 6
  val prefix = "cg"

  val registry = ControlRegistry.new { help = "code generator settings" }

  val _ = BasicControl.nest (prefix, registry, priority)

  val b = ControlUtil.Cvt.bool
  val i = ControlUtil.Cvt.int
  val r = ControlUtil.Cvt.real
  val sl = ControlUtil.Cvt.stringList

  val nextpri = ref 0

  fun new (c, n, h, d) = let
      val r = ref d
      val p = !nextpri
      val ctl = Controls.control { name = n,
                                   pri = [p],
                                   obscurity = obscurity,
                                   help = h,
                                   ctl = r }
  in
      nextpri := p + 1;
      ControlRegistry.register
          registry
          { ctl = Controls.stringControl c ctl,
            envName = SOME (ControlUtil.EnvName.toUpper "CG_" n) };
      r
  end

  val tailrecur = new (b, "tailrecur", "?", true)
  val recordopt = new (b, "recordopt", "?", true)
  val tail = new (b, "tail", "?", true)
  val allocprof = new (b, "allocprof", "?", false)
  val closureprint = new (b, "closureprint", "?", false)
  val closureStrategy = new (i, "closure-strategy", "?", 0)
  val lambdaopt = new (b, "lambdaopt", "?", true)
  val cpsopt = new (sl, "cpsopt", "cps optimizer phases", [
	  "first_contract", "eta", "zeroexpand", "last_contract"
	])
  (* ["first_contract", "eta", "uncurry", "etasplit",
      "cycle_expand", "eta", "last_contract" ] *)
  val rounds = new (i, "rounds", "max # of cpsopt rounds", 10)
  val path = new (b, "path", "?", false)
  val betacontract = new (b, "betacontract", "?", true)
  val eta = new (b, "eta", "?", true)
  val selectopt = new (b, "selectopt", "?", true)
  val dropargs = new (b, "dropargs", "?", true)
  val deadvars = new (b, "deadvars", "?", true)
  val flattenargs = new (b, "flattenargs", "?", false)
  val extraflatten = new (b, "extraflatten", "?", false)
  val switchopt = new (b, "switchopt", "?", true)
  val handlerfold = new (b, "handlerfold", "?", true)
  val branchfold = new (b, "branchfold", "?", false)
  val arithopt = new (b, "arithopt", "?", true)
  val betaexpand = new (b, "betaexpand", "?", true)
  val unroll = new (b, "unroll", "?", true)
  val knownfiddle = new (b, "knownfiddle", "?", false)
  val invariant = new (b, "invariant", "?", true)
  val targeting = new (i, "targeting", "?", 0)
  val lambdaprop = new (b, "lambdaprop", "?", false)
  val newconreps = new (b, "newconreps", "?", true)
  val boxedconstconreps = ElabControl.boxedconstconreps
  val unroll_recur = new (b, "unroll-recur", "?", true)
  val sharepath = new (b, "sharepath", "?", true)
  val staticprof = new (b, "staticprof", "?", false)
  val hoistup = new (b, "hoistup", "?", false)
  val hoistdown = new (b, "hoistdown", "?", false)
  val recordcopy = new (b, "recordcopy", "?", true)
  val recordpath = new (b, "recordpath", "?", true)
  val verbose = new (b, "verbose", "?", false)
  val debugcps = new (b, "debugcps", "?", false)
  val misc4 = new (i, "misc4", "?", 0)
  val argrep = new (b, "argrep", "?", true)
  val bodysize = new (i, "bodysize", "?", 20)
  val reducemore = new (i, "reducemore", "?", 15)
  val alphac = new (b, "alphac", "?", true)
  val comment = new (b, "comment", "?", false)
  val knownGen = new (i, "known-gen", "?", 0)
  val knownClGen = new (i, "known-cl-gen", "?", 0)
  val escapeGen = new (i, "escape-gen", "?", 0)
  val calleeGen = new (i, "callee-gen", "?", 0)
  val spillGen = new (i, "spill-gen", "?", 0)
  val foldconst = new (b, "foldconst", "?", true)
  val etasplit = new (b, "etasplit", "?", true)
  val printit = new (b, "printit", "whether to show CPS", false)
  val printsize = new (b, "printsize", "?", false)
  val scheduling = new (b, "scheduling", "?", true)
  val cse = new (b, "cse", "?", false)
  val optafterclosure = new (b, "opt-after-closure", "?", false)
  val uncurry = new (b, "uncurry", "?", true)
  val ifidiom = new (b, "if-idiom", "?", true)
  val comparefold = new (b, "comparefold", "?", true)
  val csehoist = new (b, "csehoist", "?", false)
  val rangeopt = new (b, "rangeopt", "?", false)
  val icount = new (b, "icount", "?", false)
  val debugRep = new (b, "debug-rep", "?", false)
  val checklty1 = new (b, "checklty1", "?", false)
  val checklty2 = new (b, "checklty2", "?", false)
  val checklty3 = new (b, "checklty3", "?", false)
  val checkcps1 = new (b, "checkcps1", "?", false)
  val checkcps2 = new (b, "checkcps2", "?", false)
  val checkcps3 = new (b, "checkcps3", "?", false)
  val checkcps = new (b, "checkcps", "?", false)
  val flatfblock = new (b, "flatfblock", "?", true)
  val deadup = new (b, "deadup", "?", true)
  val pollChecks = new (b, "poll-checks", "?", false)
  val pollRatioAtoI = new (r, "poll-ratio-a-to-i", "?", 1.0)

  val printFlowgraphStream = ref TextIO.stdOut

  val memDisambiguate = new (b, "mem-disambiguate", "?", false)
  val controlDependence = new (b, "control-dependence", "?", false)
  val flinton = new (b, "flinton", "?", true)

  val compdebugging = new (b, "compdebugging", "?", false)

end (* structure Control_CG *)


structure Control : CONTROL =
struct

  local
      val priority = [10, 10, 9]
      val obscurity = 4
      val prefix = "control"

      val registry = ControlRegistry.new
                         { help = "miscellaneous control settings" }

      val _ = BasicControl.nest (prefix, registry, priority)

      val bool_cvt = ControlUtil.Cvt.bool

      val nextpri = ref 0

      fun register (n, h, r) = let
	    val p = !nextpri
	    val ctl = Controls.control {
		    name = n,
		    pri = [p],
		    obscurity = obscurity,
		    help = h,
		    ctl = r
		  }
	    in
	      nextpri := p + 1;
              ControlRegistry.register registry {
		  ctl = Controls.stringControl bool_cvt ctl,
		  envName = SOME (ControlUtil.EnvName.toUpper "CONTROL_" n)
		};
	      r
	    end

    (* `new (n, h, d)` defines new control reference with default value `d` and registers
     * it with name `n` and help message `h`.
     *)
      fun new (n, h, d) = let
	    val r = ref d
	    in
	      register (n, h, r)
	    end

  in

    structure Print : PRINTCONTROL = Control_Print

    structure ElabData : ELABDATA_CONTROL = ElabDataControl

    structure Elab : ELAB_CONTROL = ElabControl

    structure MC : MCCONTROL = Control_MC

    structure FLINT = FLINT_Control

    structure MLRISC = MLRiscControl

    structure CG : CGCONTROL = Control_CG

    open BasicControl
    (* provides: val printWarnings = ref true
     *)
    open ParserControl
    (* provides: val primaryPrompt = ref "- "
		 val secondaryPrompt = ref "= "
		 val overloadKW = ref false
		 val lazysml = ref false
		 val quotation = ref false
     *)

    val debugging = new ("debugging", "?", false)
    val printAst = new ("printAst", "whether to print Ast representation", false)
    val printAbsyn = register ("printAbsyn", "whether to print Absyn representation", ElabControl.printAbsyn)
    val interp = new ("interp", "?", false)

    val progressMsgs = new ("progressMsgs", "?", false)
(*
    val debugLook = ref false
    val debugCollect = ref false
    val debugBind = ref false
*)
    val trackExn =
	new ("track-exn",
	     "whether to generate code that tracks exceptions", true)
    (* warning message when call of polyEqual compiled: *)
    val polyEqWarn =
	new ("poly-eq-warn", "whether to warn about calls of polyEqual", true)
    val indexing = new ("indexing", "?", false)
    val instSigs = new ("inst-sigs", "?", true)

    val preserveLvarNames = new ("preserve-names", "?", false)
    (* these are really all the same ref cell: *)
    val saveit : bool ref = ElabData.saveLvarNames
    val saveAbsyn : bool ref = saveit
    val saveLambda : bool ref = saveit
    val saveConvert : bool ref = saveit
    val saveCPSopt : bool ref = saveit
    val saveClosure : bool ref = saveit

    structure LambdaSplitting = struct
	datatype globalsetting = Off | Default of int option
	type localsetting = int option option
	val UseDefault : localsetting = NONE
	fun Suggest s : localsetting = SOME s
	fun parse "off" = SOME Off
	  | parse "on" = SOME (Default NONE)
	  | parse s = Option.map (Default o SOME) (Int.fromString s)
	fun show Off = "off"
	  | show (Default NONE) = "on"
	  | show (Default (SOME i)) = Int.toString i
	local
	    val registry = ControlRegistry.new
			       { help = "cross-module inlining" }

	    val priority = [10, 10, 0, 1]

	    val _ = BasicControl.nest ("inline", registry, priority)

	    val cvt = { tyName = "Control.LambdaSplitting.globalsetting",
			fromString = parse, toString = show }
	    val state_r = ref (Default NONE)
	    val ctl = Controls.control
			  { name = "split-aggressiveness",
			    pri = [0],
			    obscurity = 1,
			    help = "aggressiveness of lambda-splitter",
			    ctl = state_r }
	    val _ = ControlRegistry.register
			registry
			{ ctl = Controls.stringControl cvt ctl,
			  envName = SOME "INLINE_SPLIT_AGGRESSIVENESS" }
	in
   	    fun set x = Controls.set (ctl, x)
	    fun get () =
		case Controls.get ctl of
		    Off => NONE
		  | Default d => d
	    fun get' NONE = get ()
	      | get' (SOME a) =
		(case Controls.get ctl of
		     Off => NONE
		   | Default _ => a)
	end
    end
    val tdp_instrument = TDPInstrument.enabled

    end (* local *)

end (* structure Control *)
