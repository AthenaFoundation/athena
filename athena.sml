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
       loop())
   end

fun runWithStarterFileAndQuit(file_name) = 
   (Repl.init(file_name);
    print("\nDone...\n"))

fun run() = runWithStarterFile(NONE)

(**

-- XSB-specific code, commented out by default:

val initXSB = _import "initXSB" public: unit -> int
val doXSBCommand = _import "doXSBCommand" public: SML_With_C_Interaction.pointer -> int
val answerQuery = _import "answerQuery" public: SML_With_C_Interaction.pointer * int -> SML_With_C_Interaction.pointer

fun initializeXSB() =
    let val _ = initXSB()
        val _ = print("\nAbout to start XSB...\n")
    in
      doXSBCommand(SML_With_C_Interaction.SMLString2CString("consult('./athenaInit.P')."));
    end
	       
**)

fun main1(arg0,args) = 
  let fun M(file_name_option:string option) =              
             (print("\nWelcome to Athena!\n");
              print("\nType an expression or deduction at the\nprompt below, ");
              print("and press Enter to evaluate it.\n");
	          print("\nTo exit Athena, type \"quit\" at the prompt\nand press Enter.\n");
              runWithStarterFile(file_name_option);
	      OS.Process.success) 
(**      
      val i = initializeXSB()
      val _ = 
**)
  in
    (case args of
       [] => M(NONE)
     | file_name::_ => M(SOME(file_name)))
   end

fun main(arg0,args) = main1(arg0,args)

end 
