(*============================================================================================================

Assuming that the executable produced by running make_athena_binary_for_linux or make_athena_binary_for_mac 
is named "athena", you can run the system in a number of ways: 

./athena                                -> Start the Athena REPL
./athena foo.ath                        -> Load foo.ath first and then start the Athena REPL
./athena foo.ath quit          	        -> Load foo.ath and then quit 
./athena -port <number>                 -> Start an Athena TCP server running on port <number>
./athena -port <number> -file foo.ath   -> Load foo.ath first and then start an Athena TCP server on port <number>

============================================================================================================*)


fun mlton_main(arg0,args) = 
  let fun M(file_name_option:string option,quit_after) =              
             (print("\nWelcome to Athena!\n");
              print("\nType an expression or deduction at the\nprompt below, ");
              print("and press Enter to evaluate it.\n");
	          print("\nTo exit Athena, type \"quit\" at the prompt\nand press Enter.\n");
              if quit_after then
                 Athena.runWithStarterFileAndQuit(file_name_option)
	      else 		  
                 Athena.runWithStarterFile(file_name_option);
	      OS.Process.success) 
(**      
      val i = initializeXSB()
**)
  in
    (case args of
       [] => M(NONE,false)
     | [file_name] => M(SOME(file_name),false)
     | [arg_1,arg_2] => if arg_1 = "-port" orelse arg_1 = "--port" then
                           let val port_num_opt = Int.fromString(arg_2)
                           in
                              (case port_num_opt of 
                                  SOME(port_num) => (Thread.spawn(fn () => AthenaServer.startServer(port_num,NONE)); Thread.run(); OS.Process.success)
                                | _ => (print("\nInvalid port number."); OS.Process.failure))
                           end 
                        else M(SOME(arg_1),true)          
     | [arg_1,arg_2,arg_3,arg_4] =>  
                       if (arg_1 = "-port" orelse arg_1 = "--port") andalso (arg_3 = "--file" orelse arg_3 = "-file") then
                             let val port_num_opt = Int.fromString(arg_2)
                                 val starter_file = arg_4
                             in
                                (case port_num_opt of 
                                    SOME(port_num) => (Thread.spawn(fn () => AthenaServer.startServer(port_num,SOME(starter_file))); Thread.run(); OS.Process.success)
                                  | _ => (print("\nInvalid port number."); OS.Process.failure))
                             end
                       else 
                             M(SOME(arg_1),true)
     | file_name::(_::_) => M(SOME(file_name),true))
   end
   
val _ = mlton_main("",CommandLine.arguments())
