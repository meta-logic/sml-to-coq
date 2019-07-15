(* code-obj.sml
 *
 * COPYRIGHT (c) 1998 Bell Labs, Lucent Technologies.
 *
 * An interface for manipulating code objects.
 *)

structure CodeObj :> CODE_OBJ =
  struct

    structure W8A = Word8Array
    structure W8V = Word8Vector
    type object = Unsafe.Object.object

    datatype code_object = C of {
	entrypoint : int ref,
	obj : Word8Array.array
      }

    type csegments = {
	c0 : code_object,
	cn : code_object list, 
	data : Word8Vector.vector
      }

    type executable = object -> object

  (* raised by input when there are insufficient bytes *)
    exception FormatError

    local
      structure CI = Unsafe.CInterface
    in
    val allocCode : int -> W8A.array =
	  CI.c_function "SMLNJ-RunT" "allocCode"
    val mkLiterals : W8V.vector -> object = CI.c_function "SMLNJ-RunT" "mkLiterals"
    val mkExec : W8A.array * int -> executable = CI.c_function "SMLNJ-RunT" "mkExec"
    end (* local *)

  (* Allocate an uninitialized code object.
   *)
    fun alloc n =
	(if (n <= 0) then raise Size else ();
	 C { entrypoint = ref 0, obj = allocCode n })

  (* Allocate a code object of the given size and initialize it
   * from the input stream.
   * NOTE: someday, we might read the data directly into the code
   * object, but this will require hacking around with the reader.
   *)
    fun input (inStrm, sz) = let
	  val (co as C{obj, ...}) = alloc sz
	  val data = BinIO.inputN (inStrm, sz)
	  in
	    if (W8V.length data < sz)
	      then (
		Control_Print.say(concat[
		    "Bin file format error: expected ", Int.toString sz,
		    " bytes, but only found ", Int.toString(W8V.length data)
		  ]);
		raise FormatError)
	      else ();
	    W8A.copyVec{src=data, dst=obj, di=0};
	    co
	  end

  (* Output a code object to the given output stream *)
    fun output (outStrm, C{obj, ...}) = (
	  BinIO.output(outStrm, Unsafe.cast obj);
	  BinIO.flushOut outStrm)

  (* View the code object as an updatable array of bytes. *)
    fun bytes (C{obj, ...}) = obj

  (* View the code object as an executable.  This has the side-effect
   * of flushing the instruction cache.
   *)
    fun exec (C{obj, entrypoint = ref ep }) = mkExec (obj, ep)

  (* return the size of the code object *)
    fun size (C{obj, ...}) = W8A.length obj

    fun entrypoint (C c) = !(#entrypoint c)

    fun set_entrypoint (C c, ep) = #entrypoint c := ep

  end;
