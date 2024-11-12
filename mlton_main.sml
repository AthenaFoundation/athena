fun express_main(arg0,args) =
 let 
     fun process() =  (case args of
                          [arg1,arg2] =>
			    let val [port_spec, port_value] = [arg1,arg2]
			        val _ = Repl.init(NONE)
			    in
			      if port_spec = "-p" orelse port_spec = "-port" then
  	  		        (case Int.fromString(port_value) of
                                    SOME(p) => (Thread.spawn(fn () => AthenaServer.cmlMain(p)); Thread.run())
 		                  | _ => Basic.fail("\nInvalid port number, an integer was expected.\n"))
                              else Basic.fail("\nPort option (-p or -port) expected as the first argument")
 			    end)
     val _ = process()
 in
   OS.Process.success
 end

val _ = express_main("",CommandLine.arguments())
