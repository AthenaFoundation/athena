(*======================================================================

Main file. 

=======================================================================*)

structure Athena = 

struct
                                                       
fun runWithStarterFile(file_name) =
   let fun loop() = let val res = Repl.getInputAndProcess()
                        val _ = HashTable.clear(Repl.top_loaded_files_ht)                    
                    in
                      if res = 0 then () else loop()
                    end
   in		    
      (Repl.init(file_name);
       print("\nReady...\n");
       loop();
       OS.Process.success)
   end

fun startServer(port_number,starter_file_option) = 
  let val _ = Repl.init(starter_file_option)
      val env = ref(SemanticValues.valEnv({val_map=SemanticValues.empty_val_map,mod_map=SemanticValues.empty_mod_map}))
      val eval_env = Semantics.top_val_env
      val cmd = "(start-athena-server " ^ (Int.toString port_number) ^ ")"
      val process = !Semantics.processString
      val _ = process(cmd,[],env,eval_env)
  in
     OS.Process.success
  end

fun runWithStarterFileAndQuit(file_name) = 
   (Repl.init(file_name);
    print("\nDone...\n");
    OS.Process.success)

fun run() = let val _ = Options.first_time := true
            in runWithStarterFile(NONE) end 

(**
fun run() = let val _ = Options.first_time := true
            in ExpressServer.startServerOnPort(10000) end 
**)
(**

-- XSB-specific code, commented out by default:

val initXSB = _import "initXSB" public: unit -> int
val doXSBCommand = _import "doXSBCommand" public: SML_With_C_Interaction.pointer -> int
val answerQuery = _import "answerQuery" public: SML_With_C_Interaction.pointer * int -> SML_With_C_Interaction.pointer

fun initializeXSB() =
    let val _ = initXSB()
        val _ = print("\nAbout to start XSB...\n")
    in
      doXSBCommand(SML_With_C_Interaction.SMLString2CString("consult('./athena_init.P')."));
    end
	       
**)

(****************************************************************************************************************
Assuming that the executable you've produced is named "athena", run the following:

./athena                                -> Starts the Athena REPL
./athena foo.ath                        -> Loads foo.ath first and then starts the Athena REPL
./athena foo.ath quit          	        -> Loads foo.ath and then quits 
./athena -port <number>                 -> Starts an Athena TCP server running on port <number>
./athena -port <number> -file foo.ath   -> Loads foo.ath and then starts an Athena TCP server on port <number>

*****************************************************************************************************************)

fun main(arg0,args) = 
  let fun M(file_name_option:string option,quit_after) =              
             (print("\nWelcome to Athena!\n");
              print("\nType an expression or deduction at the\nprompt below, ");
              print("and press Enter to evaluate it.\n");
	          print("\nTo exit Athena, type \"quit\" at the prompt\nand press Enter.\n");
              if quit_after then
                 runWithStarterFileAndQuit(file_name_option)
	      else 		  
                 runWithStarterFile(file_name_option);
	      OS.Process.success) 
(**      
      val i = initializeXSB()
      val _ = 
**)
  in
    (case args of
       [] => M(NONE,false)
     | [file_name] => M(SOME(file_name),false)
     | [arg_1,arg_2] => if arg_1 = "-port" orelse arg_1 = "--port" then
                           let val port_num_opt = Int.fromString(arg_2)
                           in
                              (case port_num_opt of 
                                  SOME(port_num) => startServer(port_num,NONE)
                                | _ => (print("\nInvalid port number."); OS.Process.failure))
                           end 
                        else M(SOME(arg_1),true)          
     | [arg_1,arg_2,arg_3,arg_4] => 
                       if (arg_1 = "-port" orelse arg_1 = "--port") andalso (arg_3 = "--file" orelse arg_3 = "-file") then
                           let val port_num_opt = Int.fromString(arg_2)
                               val starter_file = arg_4
                           in
                              (case port_num_opt of 
                                  SOME(port_num) => startServer(port_num,SOME(starter_file))
                                | _ => (print("\nInvalid port number."); OS.Process.failure))
                           end 
                       else M(SOME(arg_1),true)
     | file_name::(_::_) => M(SOME(file_name),true))
   end
   
end 
