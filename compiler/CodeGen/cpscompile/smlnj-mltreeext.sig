(* We might use different extensions, but they all have to agree on
 * this signature...
 * (In particular, we want to use the extensions already provided by
 * MLRISC for the x86 and Sparc.) 
 *)
signature SMLNJ_MLTREE_EXT = sig
   type ('s,'r,'f,'c) sx
   type ('s,'r,'f,'c) rx
   type ('s,'r,'f,'c) ccx
   datatype ('s,'r,'f,'c) fx = 
       FSINE of 'f
     | FCOSINE of 'f
     | FTANGENT of 'f
end
