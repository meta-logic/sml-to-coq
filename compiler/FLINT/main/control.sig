(* control.sig *)

signature FLINTCONTROL =
sig

    val print		: bool ref   (* show IR *)
    val printPhases	: bool ref   (* show phases *)
    val printFctTypes   : bool ref   (* show functor types *)
    val phases		: string list ref  (* determine phases and their order *)

    val tmdebugging     : bool ref   (* TransTypes debugging *)
    val trdebugging     : bool ref   (* Translate debugging *)
    val nmdebugging     : bool ref   (* Plambda normalization (FlintNM) *)
    val redebugging     : bool ref   (* reify phase debugging (Reify) *)
    val rtdebugging     : bool ref   (* runtime types debugging (RuntimeType) *)

    val inlineThreshold	: int ref    (* inline threshold *)
    (* val splitThreshold	: int ref *)
    val unrollThreshold	: int ref    (* unroll threshold *)
    val maxargs		: int ref    (* to put a cap on arity raising *)
    val dropinvariant	: bool ref

    val specialize	: bool ref   (* whether to specialize *)
    (* val liftLiterals	: bool ref *)
    val sharewrap	: bool ref   (* whether to share wrappers *)
    val saytappinfo	: bool ref   (* for verbose typelifting *)

    (* FLINT internal type-checking controls *)
    val check		: bool ref    (* typecheck IR? *)
    val checkDatatypes	: bool ref    (* typecheck datatypes *)
    val checkKinds	: bool ref    (* check kinds *)
    val plchk           : bool ref    (* type check plambda after translate *)

    (* for use in FLINT/main/flintcomp.sml *)
    val recover : (int -> unit) ref

    (* only for temporary debugging *)
    val misc		: int ref

end (* signature FLINTCONTROL *)
