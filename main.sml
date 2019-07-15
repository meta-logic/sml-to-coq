Control.Print.printLength := 1000;
Control.Print.printDepth := 100;

structure Main = 
struct

  fun getAST (filename: string) = 
    let
      val f = TextIO.openIn (filename)
      val source = Source.newSource (filename, f, true, ErrorMsg.defaultConsumer())
    in
      SmlFile.parse source
    end

end
