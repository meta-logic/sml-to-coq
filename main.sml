Control.Print.printLength := 1000;
Control.Print.printDepth := 100;

structure Main = 
struct
	structure F = ElabModFn (structure SM = SigMatch);
	structure T = ElabTopFn(structure ElabMod = F);
	structure S = StaticEnv;


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
  		val (absyn, _) = T.elabTop (ast, S.empty, cc)

  	in
  		absyn
  	end

end
