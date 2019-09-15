structure Toplevel = 
struct
    structure G = Gallina;
    open Annotation;
    infix @@;

  fun convert(source : string) : G.sentence list = 
    let
      val arg = Sml.parseArg (Sml.lib());
      val x = Sml.parse1 arg (NONE, source);
      val (_, x) = x;
      val x @@ _ = x;
      val SyntaxProgram.Program(x) = x;
      val (x, _) = x;
      val x @@ _ = x;
      val SyntaxModule.STRDECTopDec x = x;
      val (x, _) = x;
      val x @@ _ = x;
      val SyntaxModule.DECStrDec x = x;
    in
      Convertor.dec2sents x
    end


end
