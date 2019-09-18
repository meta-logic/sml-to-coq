structure Convertor = 
struct
    structure G = Gallina;
    open Annotation
    open ConvertorProgram    
    infix @@;

  fun convert(source : string) : G.sentence list = 
    let
      val ((J, B_BIND), (B_STAT, B_DYN), s) =  Sml.lib()
      val parseArgs = (J, B_BIND)
      val elabArgs = (J, B_BIND, B_STAT)
      val (J', program) = Sml.parse1 parseArgs (NONE, source)
      val B_STAT' = Program.elabProgram true (B_STAT, program)
      (*val x @@ _ = x;*)
      (*val SyntaxProgram.Program(x) = x;*)
(*    val (x, _) = x;
      val x @@ _ = x;
      val SyntaxModule.STRDECTopDec x = x;
      val (x, _) = x;
      val x @@ _ = x;
      val SyntaxModule.DECStrDec x = x;*)
    in
      program2sents program
    end


end
