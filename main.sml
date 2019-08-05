Control.Print.printLength := 1000;
Control.Print.printDepth := 100;

structure Main = 
struct
	structure F = ElabModFn (structure SM = SigMatch);
	structure T = ElabTopFn(structure ElabMod = F);
(*	structure S = StaticEnv;
*)  


  fun getAST (filename: string) = 
    let
      val f = TextIO.openIn (filename)
      val source = Source.newSource (filename, f, true, ErrorMsg.defaultConsumer())
    in
      SmlFile.parse source
    end

  fun getAbsyn (filename : string) = 
  	let
  		val f = TextIO.openIn (filename)
  		val source = Source.newSource (filename, f, false, ErrorMsg.defaultConsumer())
  		val ast = getAST filename
  		val cc : ElabUtil.compInfo = 
  			CompInfo.mkCompInfo {mkMkStamp = fn () => Stamps.newGenerator (), 
  			source = source, transform = fn (x : Absyn.dec) => x}
      (* PrimEnv is in compiler/Semant/statenv and it has all the basic types 
        Also, check compiler/MAP lines 212 to 221 for full explanation *)
  		val (absyn, _) = T.elabTop (ast, PrimEnv.primEnv, cc)

  	in
  		absyn
  	end

end
