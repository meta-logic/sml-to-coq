structure Convertor = 
struct
    structure G = Gallina;
    open Annotation
    open ConvertorProgram    
    infix @@;

  fun convert'(source : string) : G.sentence list = 
    let
      val ((J, B_BIND), (B_STAT, B_DYN), s) =  Sml.lib()
      val parseArgs = (J, B_BIND)
      val elabArgs = (J, B_BIND, B_STAT)
      val (J', program) = Sml.parse1 parseArgs (NONE, source)
      val B_STAT' = Program.elabProgram true (B_STAT, program)
      val s'      = ref s      
      val B_DYN'  = Program.evalProgram true ((s', B_DYN), program)      
(*      val p @@ _ = program;
      val Program p = p;
      val (p, _) = p;
      val p @@ _ = p;
      val STRDECTopDec p = p;      
      val (p, _) = p;
      val p @@ _ = p;
      val DECStrDec p = p;
      val p @@ a = p;
      *)
    in
      program2sents program 
    end

  fun convert(source: string) : G.sentence list =
    let
      val ins = TextIO.openIn source 
      fun loop ins = 
       case TextIO.inputLine ins of 
          SOME line => line :: loop ins 
        | NONE      => [] 
      val codeList = loop ins before TextIO.closeIn ins 
      val code = String.concat codeList  
    in 
      convert' code
    end

end
