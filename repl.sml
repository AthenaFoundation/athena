(*======================================================================

Code for implementing Athena's interactive REPL (read-eval-print loop),
most notably processInput.

=======================================================================*)

structure Repl =

struct

structure A = AbstractSyntax
structure ATV = AthTermVar
structure AT = AthTerm
structure N = Names
structure SM = DefinitionProcessor
structure S = Symbol
structure MS = ModSymbol
structure SV = SemanticValues

val preProcessPhrase = SV.preProcessPhrase
val preProcessExp = SV.preProcessExp
val preProcessExpLst = SV.preProcessExpLst
val preProcessPatternLst = SV.preProcessPatternLst
val preProcessPhraseLst = SV.preProcessPhraseLst

val first_time = Options.first_time

val top_loaded_files_ht : (string,bool) HashTable.hash_table = 
       HashTable.mkTable(HashString.hashString, op = ) (109,Basic.Never)

fun pcf(str) = if str = "" then "" else str^", "

fun printLoadedFiles(loaded_files : (string,bool) HashTable.hash_table) = 
  let val files_and_bools = HashTable.listItemsi(loaded_files)
      val res = Basic.printListStr(files_and_bools,fn (f,b) => f, " || ")
  in
     res
  end

fun debugPrint(_) = ()
            
fun showFreeIds(phr,mod_path) = 
 let val (new_phrase,vars,fids) = preProcessPhrase(phr,mod_path)
     val fid_strings = map MS.name (MS.listModSymbols fids)
 in
       Basic.printList(fid_strings,Basic.id)
 end

fun getDirName(fileName) = 
    let fun cutBeforeSlash(lst) = 
	    (case lst of
		 nil => (explode ".")
	       | #"/"::rest => rest
	       | _::rest => (cutBeforeSlash rest))
    in
	(implode 
	     (rev 
		  (cutBeforeSlash 
		       (rev (explode fileName)))))
    end

(* This is a no-op atm: *)

fun cleanUp() = ()

fun saveSignature () = 
       let fun addLst([],set) = set
             | addLst((msym,_)::rest,set) = addLst(rest,MS.add(msym,set))
           val struc_table_listing  = MS.listItemsi(Data.structure_table) 
           val constructor_table_listing = MS.listItemsi(Data.constructor_table)
           val fsym_table_listing = MS.listItemsi(Data.fsym_table)
           val sort_abbreviations_listing = MS.listItemsi(Data.sort_abbreviations)
           val sort_table_listing = MS.listItemsi(SortOrder.sort_table)
           val struc_table_set = addLst(struc_table_listing,MS.empty_set)
           val constructor_table_set = addLst(constructor_table_listing,MS.empty_set)
           val fsym_table_set = addLst(fsym_table_listing,MS.empty_set)
           val sort_abbreviations_set = addLst(sort_abbreviations_listing,MS.empty_set)
           val sort_table_set = addLst(sort_table_listing,MS.empty_set)
       in
           {struc_table_set=struc_table_set,constructor_table_set=constructor_table_set,
            fsym_table_set=fsym_table_set,sort_abbreviations_set=sort_abbreviations_set,
            sort_table_set=sort_table_set}
       end

fun restoreSignature({struc_table_set,constructor_table_set,fsym_table_set,sort_abbreviations_set,sort_table_set}) = 
       let val struc_table_listing  = List.map (fn (a,_) => a) (MS.listItemsi(Data.structure_table))
           val _ = MS.restoreTable(struc_table_listing,struc_table_set,Data.structure_table)

           val constructor_table_listing  = List.map (fn (a,_) => a) (MS.listItemsi(Data.constructor_table))
           val _ = MS.restoreTable(constructor_table_listing,constructor_table_set,Data.constructor_table)

           val fsym_table_listing  = List.map (fn (a,_) => a) (MS.listItemsi(Data.fsym_table))
           val _ = MS.restoreTable(fsym_table_listing,fsym_table_set,Data.fsym_table)

           val sort_abbreviations_listing  = List.map (fn (a,_) => a) (MS.listItemsi(Data.sort_abbreviations))
           val _ = MS.restoreTable(sort_abbreviations_listing,sort_abbreviations_set,Data.sort_abbreviations)

           val sort_table_listing  = List.map (fn (a,_) => a) (MS.listItemsi(Data.sort_table))
           val _ = MS.restoreTable(sort_table_listing,sort_table_set,Data.sort_table)
       in
          ()
       end

fun handleException(e) = 
let
in
    (case e of
       Semantics.EvalError(msg,pos_opt) => 
         let val msg' = Semantics.makeErrorWithPosInfo(msg,pos_opt)
         in
           (print("\n"^msg'^"\n");
            print(Semantics.summarizeTopCallStack());
            if (!Options.stack_trace orelse !Options.detailed_stack_trace) then
                (print("\nDetailed call stack: \n");Semantics.printCallStack();print("\n"))
            else ())
         end
     | Semantics.AthenaError(msg) => let val (_,right_pos) = Semantics.chooseAthenaErrorPosition()
                                         val msg' = Semantics.makeErrorWithPosInfo(msg,SOME(right_pos))
                                     in
                                       (print("\n"^msg'^"\n");
                                        print(Semantics.summarizeTopCallStack()))
                                     end
     | TopEnv.Halt => ()     
     | _ => print(Semantics.exceptionToString(e)))
end
           
fun pathToString(path) = if null(path) then "[]" else Basic.printListStr(path,Symbol.name,".")

fun endsIn(s1,s) = Basic.prefix(rev(explode(s)),rev(explode(s1)))

fun addExtension(s) = if endsIn(s,".ath") then s else s ^ ".ath"

fun defineAutoStructureInduction(absyn_struc:A.absyn_structure as {name,pos,obtype_params,constructors,free},mod_path,env,eval_env) = 
        let val con_names: Symbol.symbol list = map (fn r => #name(r)) constructors
	    val full_con_names = map (fn con_name => 
                                           MS.makeName(mod_path,con_name)) con_names					   
	    val struc_name_str = S.name(name)
	    val full_struc_name_str = MS.makeName(mod_path,name)
	    val poly = not(null(obtype_params))
	    val counter = ref(0)
	    val type_vars = Basic.printListStr(map (fn _ => "'T" ^ Int.toString(Basic.incAndReturn(counter))) obtype_params,fn x => x," ")
	    val uvar_type = if type_vars = "" then full_struc_name_str else "(" ^ full_struc_name_str ^ " " ^ type_vars ^ ")"
            val define_line = "(define (" ^ (Basic.downcaseString struc_name_str) ^ "-induction g)\n"
            val dlet_line_0 = "(dlet ((goal-property (match g ((some-sent _) (" ^ (N.getSafeName "property-from-induction-goal") ^ " g)) (_ g)))\n"
            val dlet_line_1 = "(v (fresh-var \"" ^ uvar_type ^ "\"))\n"
            val dlet_line_2 = "(goal (forall v (goal-property v)))\n"	                 
            val dlet_line_3 = "(v (" ^ (N.getSafeName "qvar-of") ^ " goal)))\n"
	    val prequel = define_line ^ dlet_line_0 ^ dlet_line_1 ^ dlet_line_2 ^ dlet_line_3 
	    fun makeConstructorLine(c:A.absyn_structure_constructor as {name,argument_types,...}) = 
	         let val arity = length(argument_types)
		     val con_name = name
		     val full_con_name = MS.makeName(mod_path,con_name)
		     val full_con_name = if poly andalso null(argument_types) then full_con_name ^ ":(sort-of v)" else full_con_name
		     val con_name_str = S.name(name)
		     val pattern = if (arity < 1) then "(bind state " ^ full_con_name ^ ")"
		                   else "(bind state (" ^ full_con_name ^ " " ^ (Basic.printListStr((List.map (fn _ => "_") argument_types),fn x => x, " ")) ^ "))"
                     val body = "(!" ^ (N.getSafeName "prove") ^ " (goal-property state))"
		 in
                    "(" ^ pattern ^ " " ^ body ^ ")"
		 end
            val lines = Basic.printListStr(map makeConstructorLine constructors,fn x => x,"\n")
	    val by_ind_part = "(by-induction goal\n" 
	    val cmd = prequel ^ by_ind_part ^ lines ^ ")))\n"
            val process = !Semantics.processString
       in 
          if (struc_name_str = "Boolean") then () else process(cmd,mod_path,env,eval_env)
       end

fun defineAutoStructureInductionWith(absyn_struc:A.absyn_structure as {name,pos,obtype_params,constructors,free},mod_path,env,eval_env) = 
        let val con_names: Symbol.symbol list = map (fn r => #name(r)) constructors
	    val full_con_names = map (fn con_name => 
                                           MS.makeName(mod_path,con_name)) con_names					   
	    val struc_name_str = S.name(name)
	    val full_struc_name_str = MS.makeName(mod_path,name)
	    val poly = not(null(obtype_params))
	    val counter = ref(0)
	    val type_vars = Basic.printListStr(map (fn _ => "'T" ^ Int.toString(Basic.incAndReturn(counter))) obtype_params,fn x => x," ")
	    val uvar_type = if type_vars = "" then full_struc_name_str else "(" ^ full_struc_name_str ^ " " ^ type_vars ^ ")"
            val define_line = "(define (" ^ (Basic.downcaseString struc_name_str) ^ "-induction-with g m)\n"
	    fun makeDLet(f) = 
                    let val dlet_line_0 = "(dlet ((goal-property (match g ((some-sent _) (" ^ (N.getSafeName "property-from-induction-goal") ^ " g)) (_ g)))\n"
		        val dlet_line_1 = "(v (fresh-var \"" ^ uvar_type ^ "\"))\n"
			val dlet_line_2 = "(goal (forall v (goal-property v)))\n"	                 
			val dlet_line_3 = "(v (" ^ (N.getSafeName "qvar-of") ^ " goal)))\n"	  
 	                fun makeConstructorLine(c:A.absyn_structure_constructor as {name,argument_types,...}) = 
 	                    let val arity = length(argument_types)
 			        val con_name = name
				val full_con_name_0 = MS.makeName(mod_path,con_name)
		                val full_con_name = if poly andalso null(argument_types) then full_con_name_0 ^ ":(sort-of v)" else full_con_name_0
		                val con_name_str = S.name(name)
		                val pattern = if (arity < 1) then "(bind state " ^ full_con_name ^ ")"
		                             else "(bind state (" ^ full_con_name ^ " " ^ (Basic.printListStr((List.map (fn _ => "_") argument_types),fn x => x, " ")) ^ "))"
                                val body = f(full_con_name_0,"(goal-property state)")
		            in
                              "(" ^ pattern ^ " " ^ body ^ ")"
	 	            end           
	                 val lines =  Basic.printListStr(map makeConstructorLine constructors,fn x => x,"\n")
	                 val by_ind_part = "(by-induction goal\n" 
			 val prequel = dlet_line_0  ^ dlet_line_1  ^ dlet_line_2 ^ dlet_line_3 
                     in
                         prequel ^ by_ind_part ^ lines ^ "))\n"
                     end
            val dmatch_line_1 = "(dmatch m ((some-method _) " ^ (makeDLet (fn (c,goal) => "(!m " ^ goal ^ ")")) ^ ")"
	    fun makeMethod(c) = "(try (m \"" ^ c ^ "\") (m (string->id \"" ^ c ^ "\")))"
            val dmatch_line_2 = "\n(_ " ^ (makeDLet (fn (c,goal) => "(!" ^ (makeMethod c) ^ " " ^ goal ^ ")")) ^ ")"
	    val cmd = define_line ^ dmatch_line_1 ^ dmatch_line_2 ^ "))\n"
            val process = !Semantics.processString
       in 
          if (struc_name_str = "Boolean") then () else process(cmd,mod_path,env,eval_env)
       end

fun updateEvalEnv(eval_env,old_val_map,old_mod_map,new_module,new_module_name,mod_path) = 
      eval_env := SV.valEnv({val_map=old_val_map,mod_map=Symbol.enter(old_mod_map,new_module_name,new_module)})

fun insertSubmodule(eval_env:SV.value_environment,
                    mod_path:Symbol.symbol list,
		    new_mod_name:Symbol.symbol,
		    new_mod_value:SV.module) = 
  let val (val_map,mod_map) = Semantics.getValAndModMaps(eval_env)
  in
    (case mod_path of
        [] => SV.valEnv({val_map=val_map,mod_map=Symbol.enter(mod_map,new_mod_name,new_mod_value)})
      | M::rest => (case Symbol.lookUp(mod_map,M) of
                       SOME({mod_name,env,open_mod_directives}) =>
                         let val env' = insertSubmodule(env,rest,new_mod_name,new_mod_value)
                         in
                           SV.valEnv({val_map=val_map,mod_map=Symbol.enter(mod_map,M,{mod_name=mod_name,env=env',open_mod_directives=open_mod_directives})})
                         end
                     | _ => let val M_temp:SV.module = {mod_name=MS.makeModSymbol'([],M),
		                                        open_mod_directives=[],
							env=SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.empty_mapping})}
                                val mod_map' = Symbol.enter(mod_map,M,M_temp)
                                val eval_env' = SV.valEnv({val_map=val_map,mod_map=mod_map'})
                            in
                               insertSubmodule(eval_env',mod_path,new_mod_name,new_mod_value)
                            end ))
  end

fun auxLoadFile(file_name,mod_path,env,eval_env,pos,loaded_files_ht) = 
    let val file_name = addExtension(file_name)
        fun alreadyLoaded(file) = 
          let val res = (HashTable.find loaded_files_ht file)
          in
          (case  res of
              SOME(_) => true
            | _ => false)
          end
        val _ = Parse.setLinePos(1,0) 
    in
	case Paths.findFileWithName(file_name)
	 of NONE => print("\n"^A.posToString(pos)^": Error: Unable to open file "^file_name^".\n")
	  | SOME(full_path) =>
	    if alreadyLoaded(full_path)
	    then ()
	    else  
  		let val loader = !Paths.current_file
		    val _ = Paths.current_file := full_path
                    val _ = HashTable.insert loaded_files_ht (full_path,true)
		    val _ = SM.alwaysPrint("\nLoading file \"" ^ full_path ^ "\"\n") 
		    val istream = (TextIO.openIn full_path)
		    val (user_input_lst_from_file:A.user_input list, msg) = 
                        (case Basic.isThereLineThatStartsWith(istream,"START_LOAD")
			  of (true, lines_read) => (print("\nParsing from stream....\n");
						    Parse.setLinePos(lines_read+1,0);
						   (Parse.parse_from_stream(istream),""))
                           | _ => ((TextIO.closeIn istream); (Parse.parse(full_path), "")))
		    val _ =
			(if msg = "" then (List.app (fn i => processInputWithTopValBackUpRefreshed(i, mod_path,env,eval_env,file_name,loaded_files_ht))
			    	                    user_input_lst_from_file)
			 else print("\n"^msg^"\n"))
		in
		   Paths.current_file := loader 
                end
    end 
and processModuleExtension(module:A.module_entry as {module_name,module_contents,module_file,...},mod_path,returned_env,eval_env,loaded_files_ht) = 
       let val starting_top_ab = (!(ABase.top_assum_base))
           val (mod_sym,mod_pos) = (#name(module_name),#pos(module_name))
           fun emptyModule(name) = let val m:SV.module = {mod_name=name,open_mod_directives=[],env=SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.empty_mapping})} 
                                   in m end
           val mod_path' = mod_path@[mod_sym]
	   val mod_path_name' = Basic.printListStr(mod_path',Symbol.name,".")
           val starting_open_mod_paths_val = (!Paths.open_mod_paths)
           val starting_open_mod_directives_val = (!Paths.open_mod_directives)           
           val (starting_eval_env,error_msg) = (!eval_env,ref "")
	   val starting_mod_ab_ht = 
	       (case (HashTable.find Prop.module_ab_table mod_path_name') of
                   SOME(ht) => ht
                 | _ => let val ht:(Prop.prop,string option) HashTable.hash_table = HashTable.mkTable(Prop.hash, Prop.alEq) (23,Prop.HT)	
		        in ht end)
           val sort_signature as {struc_table_set,constructor_table_set,fsym_table_set,sort_abbreviations_set,sort_table_set} = saveSignature()
           val _ = let val (val_map2,mod_map2) = Semantics.getValAndModMaps(!eval_env)
                       val ((existing_val_map,existing_mod_map),existing_open_mod_directives) = 
                                (case Symbol.lookUp(mod_map2,mod_sym) of
                                    SOME({mod_name,env,open_mod_directives}) => (Semantics.getValAndModMaps(env),open_mod_directives)
                                  | _ => Semantics.evError("No module named "^(Symbol.name(mod_sym))^" is visible here.",SOME(mod_pos)))
                       val _ = Paths.open_mod_directives := existing_open_mod_directives
                       val _ = Paths.open_mod_paths := mod_path'::(existing_open_mod_directives@(!(Paths.open_mod_paths)))
                       val mod_path' = mod_path@[mod_sym]
                       val new_module_name = MS.makeModSymbol(mod_path,mod_sym,Symbol.symbol(A.makeModString(mod_path,mod_sym)))
                       val (val_map1,mod_map1) = Semantics.getValAndModMaps(!returned_env)
                       val (val_map1',mod_map1') = (val_map1,Symbol.enter(mod_map1,mod_sym,emptyModule(new_module_name)))
                       val (val_map2',mod_map2') = (Symbol.augment(val_map2,existing_val_map),
                                                    Symbol.augment(mod_map2,existing_mod_map))


                       val returned_env' = ref(SV.valEnv({val_map=existing_val_map,mod_map=Symbol.enter(existing_mod_map,mod_sym,emptyModule(new_module_name))}))
                       val _  = eval_env := SV.valEnv({val_map=val_map2',mod_map=mod_map2'})
                       val _ = List.app (fn user_input => processInput(user_input,mod_path',returned_env',eval_env,!module_file,loaded_files_ht)) 
                                                                       module_contents
                       val new_module:SV.module =  
                               let val (v,m) = Semantics.getValAndModMaps(!returned_env')
                                   val (m',_) = Symbol.removeBinding(m,mod_sym)
                               in
                                 {mod_name=new_module_name,open_mod_directives=(!Paths.open_mod_directives),env=SV.valEnv({val_map=v,mod_map=m'})}
                               end
                       val (val_map1'',mod_map1'') = Semantics.getValAndModMaps(!returned_env')
                       val (val_map2'',mod_map2'') = Semantics.getValAndModMaps(!eval_env)
                       val _ = returned_env := SV.valEnv({val_map=val_map1',mod_map=Symbol.enter(mod_map1,mod_sym,new_module)})
                   in
                      eval_env := SV.valEnv({val_map=val_map2,mod_map=Symbol.enter(mod_map2,mod_sym,new_module)})
                   end handle ex => (error_msg := Semantics.exceptionToString(ex);
                                     Paths.open_mod_paths := starting_open_mod_paths_val;
                                     Paths.open_mod_directives := starting_open_mod_directives_val;
                                     eval_env := starting_eval_env;
				     (HashTable.insert Prop.module_ab_table (mod_path_name',starting_mod_ab_ht));
                                     ABase.top_assum_base := starting_top_ab;
                                     restoreSignature(sort_signature);
                                     let val full_module_name = SV.qualifyName((#name(module_name)),mod_path)
                                         val msg = !error_msg
                                     in 
                                       if msg = "" then 
                                         SM.myPrint("\nModule "^(MS.name full_module_name)^
					            " was not successfully extended.\n")
                                          else 
                                              SM.myPrint("\n"^msg^"\n\nModule "^(MS.name full_module_name)^
					                 " was not successfully extended.\n") 
                                     end;
				     raise SemanticValues.GenEx("",NONE))
           val _ = Paths.open_mod_paths := starting_open_mod_paths_val
           val _ = Paths.open_mod_directives := starting_open_mod_directives_val
           val full_module_name = SV.qualifyName((#name(module_name)),mod_path)
       in
          if !error_msg = "" then SM.myPrint("\nModule "^(MS.name full_module_name)^" extended.\n")
          else SM.myPrint((!error_msg)^"\nModule "^(MS.name full_module_name)^" was not extended.\n")
       end                     
and processModule(module:A.module_entry as {module_name,module_contents,module_file,...},mod_path,returned_env,eval_env,loaded_files_ht) = 
       let val starting_top_ab = (!(ABase.top_assum_base))
           val mod_sym = #name(module_name)
           fun emptyModule(name) = let val m:SV.module = {mod_name=name,open_mod_directives=[],env=SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.empty_mapping})} 
                                   in m end
           val mod_path' = mod_path@[mod_sym]
           val starting_open_mod_paths_val = (!Paths.open_mod_paths)
           val starting_open_mod_directives_val = (!Paths.open_mod_directives)
           val _ = Paths.open_mod_directives := [] 
	   val _ = if (!Options.fundef_mlstyle_option) then	
	             (if (eval_env = SV.top_val_env) then print("\nSAME TWO ENVIRONMENTS!\n") else print ("\nUnequal environments!\n") )
                   else ()
           val (starting_eval_env,starting_top_env,error_msg) = (!eval_env,!SV.top_val_env,ref "")
           val sort_signature as {struc_table_set,constructor_table_set,fsym_table_set,sort_abbreviations_set,sort_table_set} = saveSignature()
           val _ = (let val _ = Paths.open_mod_paths := mod_path'::starting_open_mod_paths_val
                        val new_module_name = MS.makeModSymbol(mod_path,mod_sym,Symbol.symbol(A.makeModString(mod_path,mod_sym)))
                        val (val_map1,mod_map1) = Semantics.getValAndModMaps(!returned_env)
                        val (val_map1',mod_map1') = (val_map1,Symbol.enter(mod_map1,mod_sym,emptyModule(new_module_name)))
                        val (val_map2,mod_map2) = Semantics.getValAndModMaps(!eval_env)
                        val (val_map2',mod_map2') = (val_map2,Symbol.enter(mod_map2,mod_sym,emptyModule(new_module_name)))
                        val returned_env' = ref(SV.valEnv({val_map=SV.empty_val_map,mod_map=SV.empty_mod_map}))
                        val _ = List.app (fn user_input => processInput(user_input,mod_path',returned_env',eval_env,!module_file,loaded_files_ht)) 
                                                                        module_contents
                        val new_module:SV.module =  
                            let val (v,m) = Semantics.getValAndModMaps(!returned_env')
                                val m' = m 
                            in
                               {mod_name=new_module_name,open_mod_directives=(!Paths.open_mod_directives),env=SV.valEnv({val_map=v,mod_map=m'})}
                            end
                        val (val_map1'',mod_map1'') = Semantics.getValAndModMaps(!returned_env')
                        val (val_map2'',mod_map2'') = Semantics.getValAndModMaps(!eval_env)
                        val _ = returned_env := SV.valEnv({val_map=val_map1',mod_map=Symbol.enter(mod_map1,mod_sym,new_module)})
			val _ = if (!Options.fundef_mlstyle_option) then 
			        print("\nWill now augment the module part of top_val_env with this module: " ^ 
			             SV.modEnvToString(MS.nameAsSymbol(new_module_name),new_module))
				 else ()
			val _ = updateEvalEnv(eval_env,val_map2,mod_map2,new_module,mod_sym,mod_path)
                        val _ = eval_env := insertSubmodule(!eval_env,mod_path,mod_sym,new_module)
			val _ = if (!Options.fundef_mlstyle_option) then 
			           let val _ = print("\nCurrent modpath: " ^ Basic.printListStr(mod_path,Symbol.name,"/"))
				   in
  			             print("\nHere's top_val_env after this addition:\n" ^ (SV.envToString(!eval_env)) ^ "\n=============\n")
				   end
				 else ()
                    in
                       ()
                    end) handle ex => (error_msg := Semantics.exceptionToString(ex);
                                       Paths.open_mod_paths := starting_open_mod_paths_val;
				       Paths.open_mod_directives := starting_open_mod_directives_val;
                                       eval_env := starting_eval_env;
				       SV.top_val_env := starting_top_env;
				       let val mod_name= Basic.printListStr(mod_path',Symbol.name,".")
				       in
				          (HashTable.remove Prop.module_ab_table mod_name; ()) handle _ => () 
   				       end;
                                       ABase.top_assum_base := starting_top_ab;
                                       restoreSignature(sort_signature);
                                       let val full_module_name = SV.qualifyName((#name(module_name)),mod_path)
                                           val msg = !error_msg
                                       in 
                                          if msg = "" then 
                                             SM.myPrint("\nModule "^(MS.name full_module_name)^" was not successfully defined.\n")
                                          else 
                                              SM.myPrint("\n"^msg^"\n\nModule "^(MS.name full_module_name)^" was not successfully defined.\n") 
                                       end;
                                       raise SemanticValues.GenEx("",NONE))
           val full_module_name = SV.qualifyName((#name(module_name)),mod_path)
           val _ = Paths.open_mod_paths := starting_open_mod_paths_val
           val _ = Paths.open_mod_directives := starting_open_mod_directives_val
         in
            if !error_msg = "" then (SM.myPrint("\nModule "^(MS.name full_module_name)^" defined.\n"))
            else let val _  = print("\nModule definition error. Here's the current value of open_mod_paths: "^
                                   (Basic.printListStr((!Paths.open_mod_paths),pathToString,", "))^"\n\n")
                 in
                    SM.myPrint("\n"^(!error_msg)^"\nModule "^(MS.name full_module_name)^" was not successfully defined.\n")  
                 end
         end 
and processInputWithTopValBackUpRefreshed(user_input,mod_path,env,eval_env,file,loaded_files_ht) = 
       (SV.top_val_env_backup := !SV.top_val_env;
        processInput(user_input,mod_path,env,eval_env,file,loaded_files_ht))
and processInput(user_input,mod_path,env,eval_env,file,loaded_files_ht) = 
    (**
        processInput processes AST user_input (see abSyn.ml) from the given file.
        The loaded_files_ht parameter is a hash table of file names (strings) loaded when
        processing user_input. It serves only to stop infinite loops from load-dependency
        cycles due to files that mutually include each other.
     **)
    let val _ = Semantics.resetPosStack() 
        val _ = Paths.current_mod_path := mod_path
    in
	(case user_input
	  of A.structureInput(some_absyn_structure) => 
             (SM.processStructuresDefinition([SM.expandSortAbbreviationsInStrucDef(some_absyn_structure,mod_path)],env,eval_env,mod_path);
	      let val s = !Options.silent_mode
                  val _ = Options.silent_mode := true  
                  val _ = let val _ = defineAutoStructureInduction(some_absyn_structure,mod_path,env,eval_env);
 	                      val _ = defineAutoStructureInductionWith(some_absyn_structure,mod_path,env,eval_env)
			  in
			    ()
                          end handle _ => (Options.silent_mode := s)
              in 
	         Options.silent_mode := s
              end)
           | A.structuresInput(some_absyn_structure_list) => 
             SM.processStructuresDefinition(
             SM.expandSortAbbreviationsInStrucDefLst(some_absyn_structure_list,mod_path),env,eval_env,mod_path)
           | A.subSortDeclaration(domain1,pos1,domain2,pos2) => 
	     SM.processSubSortDeclaration(domain1,pos1,domain2,pos2,"\nOK.\n")
           | A.subSortsDeclaration(domains_and_positions,(domain,pos)) => SM.processSubSortsDeclaration(domains_and_positions,domain,pos)
           | A.moduleInput(m) => processModule(m,mod_path,env,eval_env,loaded_files_ht)
           | A.moduleExtension(m) => processModuleExtension(m,mod_path,env,eval_env,loaded_files_ht)
           | A.domainInput(some_absyn_domain) => 
             SM.processDomainDeclaration(some_absyn_domain,mod_path)
           | A.domainsInput(some_absyn_domain_lst) => 
             SM.processDomainsDeclaration(some_absyn_domain_lst,mod_path)
           | A.functionSymbolInput(some_absyn_fsym_list) => 
             SM.processFSymListDeclaration(List.map (fn a => SM.expandSortAbbreviationsInFSymDecl(a,mod_path))
						    some_absyn_fsym_list,mod_path,env,eval_env)
           | A.constantSymbolInput(some_absyn_fsym_list) => 
             SM.processFSymListDeclaration(List.map (fn a => SM.expandSortAbbreviationsInFSymDecl(a,mod_path))
						    some_absyn_fsym_list,mod_path,env,eval_env)
           | A.phraseInput(some_phrase) => 
             let val (new_phrase,vars,fids) = preProcessPhrase(some_phrase,mod_path)
             in
		 (SM.processPhrase(new_phrase,env,eval_env,fids,mod_path);
		  cleanUp())
             end
           | A.symbolDefinitionInput(some_sym_def as {name,pos,condition,abbreviated}:A.absyn_symbol_definition) => 
             let val (new_cond,vars,fids) = preProcessExp(condition,mod_path)
		 val new_def:A.absyn_symbol_definition = {name=name,condition=new_cond,abbreviated=abbreviated,pos=pos}
             in
		 (SM.processSymbolDefinition(new_def,fids,mod_path,env,eval_env);
		  cleanUp())
             end
           | A.direcInput(A.exitAthena(_)) => (Util.killAthena())
           | A.direcInput(A.addDemon(dexp,pos)) =>                    
             let val (dexp',vars,fids) = preProcessExp(dexp,mod_path)
             in 
		 SM.processDemonAdd(dexp',fids,false)
             end
           | A.direcInput(A.addDemons(dexps,pos)) =>                    
             let val (dexps',vars,fids) = preProcessExpLst(dexps,mod_path)
             in 
		 SM.processDemonLstAdd(dexps',fids)
             end
           | A.direcInput(A.setFlag(flag,value)) => SM.setFlag(flag,value)
           | A.direcInput(A.expandNextProof(_)) => (Options.expand_proof := true;
                                                    SM.myPrint("\nOK.\n"))
           | A.direcInput(A.printStackTrace(pos)) => (Semantics.printCallStack();print("\n"))
           | A.direcInput(A.setPrecedence(params,e)) => 
             let val (e',vars,fids) = preProcessExp(e,mod_path)
             in
		 (SM.processPrecedenceDeclarations(params,e',env,eval_env,fids);SM.myPrint("\nOK.\n"))
             end
           | A.direcInput(A.setAssoc(msyms_and_positions,b)) => (SM.processAssocDeclarations(msyms_and_positions,b))
           | A.direcInput(A.loadFile(file_name_exp, pos)) => 
             let val (file_name_exp',vars,fids) = preProcessExp(file_name_exp,mod_path)
		 val v = SM.processPhraseAndReturn(A.exp file_name_exp',env,eval_env,fids,mod_path)
             in
		 (case Semantics.isStringValConstructive(v) of
                      SOME(file_name) => auxLoadFile(file_name, mod_path,env,eval_env, pos,loaded_files_ht)
                    | _ => Semantics.evError("Wrong kind of value found here;\n"^(Semantics.expect(Semantics.stringLCType,v)),
					  SOME(A.posOfExp(file_name_exp))))
             end
           | A.direcInput(A.addPath(file_name_exp, pos)) =>
             let
		 val (file_name_exp', vars, fids) = preProcessExp(file_name_exp,mod_path)
		 val v = SM.processPhraseAndReturn(A.exp file_name_exp', env,eval_env,fids,mod_path)
             in
		 (case Semantics.isStringValConstructive(v)
                   of SOME(dir_name) =>
		      (SM.myPrint("\nAdded \"" ^ (Paths.addPath dir_name) ^ "\" to search path\n")
		       handle Paths.InvalidPath(msg) => Semantics.evError(msg, SOME(A.posOfExp(file_name_exp))))
		    | _ => Semantics.evError("Wrong kind of value found here;\n" ^ 
					  (Semantics.expect(Semantics.stringLCType, v)),
					  SOME(A.posOfExp(file_name_exp))))
             end
           | A.direcInput(A.expandInput(phrase_list,phrase,pos)) => 
             let val (phrase_list',vars,fids) = preProcessPhraseLst(phrase_list,mod_path)
		 val (phrase',vars',fids') = preProcessPhrase(phrase,mod_path)
             in 
		 (SM.processInputExpansionLst(phrase_list',phrase',env,eval_env,pos,MS.union(fids,fids'),mod_path);
		  SM.ok())
             end
           | A.direcInput(A.transformOutput(phrase1,phrase2,pos_record)) => 
             let val ([phrase1',phrase2'],vars,fids) = preProcessPhraseLst([phrase1,phrase2],mod_path)
             in 
		 (SM.processOutputTransformation(phrase1',phrase2',env,eval_env,pos_record,fids,mod_path);
		  SM.ok())
             end
           | A.direcInput(A.overload(phrase_pair_list,pos,inv as {inverted})) => 
             let fun f(phrase1,phrase2,pos0,pos1,pos2) = 
                     let val ([phrase1',phrase2'],vars,fids) = preProcessPhraseLst([phrase1,phrase2],mod_path)
                     in 
			 (SM.processOverload(phrase1',phrase2',env,eval_env,pos,pos0,pos1,pos2,fids,mod_path,file,inv))
                     end
             in 
		 ((List.app f phrase_pair_list);SM.ok())
             end
           | A.direcInput(A.sortDefinition(name,def,is_private)) => 
             let val (new_def,vars,fids) = preProcessPhrase(def,mod_path)
             in
		 (SM.processSortDefinition(name,new_def,fids,mod_path,env,eval_env,file,is_private);
		  cleanUp())
             end
           | A.direcInput(A.definitionLst(patterns,list_name_option,def,pos,is_private)) => 
             let val (new_pats,vars,val_of_ids) = SV.preProcessPatternLst'(patterns,mod_path)
		 val (new_def,vars',fids) = preProcessPhrase(def,mod_path)
             in
	        (SM.processDefinitionLst(new_pats,list_name_option,pos,new_def,env,eval_env,fids,(ATV.listVars vars)@(ATV.listVars vars'),file,is_private,mod_path);
		 cleanUp())
             end
           | A.direcInput(A.definition(name,def,is_private)) => 
             let 
                 val (new_def,vars,fids) = preProcessPhrase(def,mod_path)
             in
		 (SM.processDefinition(name,new_def,fids,mod_path,env,eval_env,file,is_private);
		  cleanUp())
             end
           | A.direcInput(A.definitions(defs,is_private)) => 
             let val (syms,exps) = ListPair.unzip(defs)
		 val (exps',vars,fids) = preProcessExpLst(exps,mod_path)
		 val  new_defs = ListPair.zip(syms,exps')
             in
		 (SM.processDefinitions(new_defs,fids,env,eval_env,file,is_private,mod_path);
		  cleanUp())
             end
	   | A.direcInput(A.openModule(msyms_and_positions)) => 
	       SM.processOpenModules(msyms_and_positions,env,eval_env,mod_path)
	   | A.direcInput(A.ruleDefinition(sym,exp)) =>
             let val (exp',vars,fids) = preProcessExp(exp,mod_path)
             in
		 (SM.processRuleDefinition(sym,exp',fids,env,eval_env);
		  cleanUp())
             end
           | A.direcInput(A.clear_assum_base) => SM.processClearAssumBase() 
           | A.direcInput(A.assertAsgn(param,exp)) => 
             let val (exp',vars,fids) = preProcessExp(exp,mod_path)
             in
		 (SM.processAssertion(exp',env,eval_env,fids,mod_path,file,{assertion_name=SOME(param),close=false});
		  cleanUp())
             end
           | A.direcInput(A.assertClose(exps)) => 
             let val (exps',vars,fids) = preProcessExpLst(exps,mod_path)
             in
		 (SM.processAssertions(exps',env,eval_env,fids,mod_path,file,true);
		  cleanUp())
             end
           | A.direcInput(A.assertCloseAsgn(param_exp_list)) => 
             let fun doOne(param,exp) = 
                     let val (exp',vars,fids) = preProcessExp(exp,mod_path)
                     in
			 SM.processAssertion(exp',env,eval_env,fids,mod_path,file,{assertion_name=SOME(param),close=true})
                     end
             in
		 (List.map doOne param_exp_list;
		  cleanUp())
             end
           | A.direcInput(A.assert(exps)) => 
             let val (exps',vars,fids) = preProcessExpLst(exps,mod_path)
             in
		 (SM.processAssertions(exps',env,eval_env,fids,mod_path,file,false);
		  cleanUp())
             end
	   | A.direcInput(A.findModel(exp,pos)) => 
             let val (exp', vars, fids) = preProcessExp(exp,mod_path)
             in
		 (processFindModel(exp', fids, pos, file, loaded_files_ht);
		  cleanUp())
             end
           | A.direcInput(A.retract(exps)) => 
             let val (exps',vars,fids) = preProcessExpLst(exps,mod_path)
             in
		 (SM.processRetractions(exps',env,eval_env,fids);
		  cleanUp())
             end) (* end of the user_input case analysis *)
    end
and processFindModel(e, fids, pos, file, loaded_files_ht) = 
    let val (v_opt,error_msg) = (SOME(Semantics.evalExp(e,Semantics.top_val_env,!SM.top_assum_base)),"")
            handle Semantics.EvalError(x) => (NONE,"\n"^(Semantics.makeErrorWithPosInfo x)^"\n")	
    in
       (case v_opt of SOME(Semantics.listVal(vals)) => ())
    end

fun printable(c) =  Int.>(Char.ord(c),32)

fun whiteSpace(c) = not(printable(c))

fun ps2string({lp,rp,lb,rb,lcb,rcb,os}) = ("\nlp: "^(Int.toString(lp))^", rp: "^(Int.toString(rp))^
                                          ", lb: "^(Int.toString(lb))^", rb: "^(Int.toString(rb))^
                                          ", lcb: "^(Int.toString(lcb))^", rcb: "^(Int.toString(rcb))^
                                          ", os: "^(Basic.boolToString(os)))

fun isBackSlash(c) = Char.ord(c) = 92

fun isDoubleQuote(c) = Char.ord(c) = 34

fun findFirstDoubleQuote([]) = []
  | findFirstDoubleQuote(str as x::y::more) = 
     if isBackSlash(x) then findFirstDoubleQuote(more)
     else if isDoubleQuote(x) then y::more
          else findFirstDoubleQuote(y::more)
  | findFirstDoubleQuote(str as x::more) = 
     if isDoubleQuote(x) then more else findFirstDoubleQuote(more)
 
fun checkParens(char_list,paren_state as {lp,rp,lb,rb,lcb,rcb,os}) = 
      let fun loop([],s) = s 
            | loop(c::rest,s as {lp,rp,lb,rb,lcb,rcb,os}) = 
                  (case c of
                      #"(" => loop(rest,{lp=lp+1,rp=rp,lb=lb,rb=rb,lcb=lcb,rcb=rcb,os=os})
                    | #")" => loop(rest,{lp=lp,rp=rp+1,lb=lb,rb=rb,lcb=lcb,rcb=rcb,os=os})
                    | #"[" => loop(rest,{lp=lp,rp=rp,lb=lb+1,rb=rb,lcb=lcb,rcb=rcb,os=os})
                    | #"]" => loop(rest,{lp=lp,rp=rp,lb=lb,rb=rb+1,lcb=lcb,rcb=rcb,os=os})
                    | #"{" => loop(rest,{lp=lp,rp=rp,lb=lb,rb=rb,lcb=lcb+1,rcb=rcb,os=os})
                    | #"}" => loop(rest,{lp=lp,rp=rp,lb=lb,rb=rb,lcb=lcb,rcb=rcb+1,os=os})
                    | #"\"" => if os then loop(rest,{lp=lp,rp=rp,lb=lb,rb=rb,lcb=lcb,rcb=rcb,os=false})
                               else (case (findFirstDoubleQuote rest) of
                                        [] => {lp=lp,rp=rp,lb=lb,rb=rb,lcb=lcb,rcb=rcb,os=true}
                                      | cl => loop(cl,{lp=lp,rp=rp,lb=lb,rb=rb,lcb=lcb,rcb=rcb,os=false}))
                    | _ => loop(rest,s))
         val res = if os then loop(findFirstDoubleQuote char_list,paren_state) else loop(char_list,paren_state)
      in 
         res
      end

fun balancedParentheses({lp,rp,lb,rb,lcb,rcb,os}) = rp >= lp andalso rb >= lb andalso rcb >= lcb andalso not(os)
      
fun getFirstLine(true_lines) = let val true_line = explode(Basic.readLine())
                                         val true_line' = if true_line = [#"\n"] then [#" ",#"\n"] else true_line
                                     in
                                        (case Basic.skipAll(true_line,whiteSpace) of 
                                            [] => getFirstLine(true_line'::true_lines)
                                          | res => (res,true_line'::true_lines))
                                     end

      fun superImplode([],res) = res
        | superImplode(line_list::more,res) = superImplode(more,(Basic.flatten line_list)@res)

fun getInputFromPrompt() = 
  let val leading_reserved = ["assume","pick-any", "conclude", "pick-witness", "pick-witnesses", "by-cases", 
                              "by-induction", "match", "try","{", "begin", "datatype-cases"]
      fun isOneProperId(line) = List.all printable line  
      val nl = #"\n"
      fun endsWithStop((#"P")::(#"O")::(#"T")::(#"S")::_) = true
        | endsWithStop((#"F")::(#"O")::(#"E")::_) = true
        | endsWithStop((#";")::(#";")::_) = true
        | endsWithStop(_) = false 
      fun endsWithClosingMark(c::rest,opening_char) = (c = #")" andalso opening_char = #"(") orelse
                                                      (c = #"]" andalso opening_char = #"[") orelse
                                                      (c = #"}" andalso opening_char = #"{")
        | endsWithClosingMark(_) = false
      fun getFirstLine(true_lines) = let val true_line = explode(Basic.readLine())
                                         val true_line' = if true_line = [#"\n"] then [#" ",#"\n"] else true_line
                                     in
                                        (case Basic.skipAll(true_line,whiteSpace) of 
                                            [] => getFirstLine(true_line'::true_lines)
                                          | res => (res,rev(true_line'::true_lines)))
                                     end
      val (first_line,true_lines) = getFirstLine([])
      val first_line_char = hd first_line 
      fun finished(rev_line,paren_state) = (balancedParentheses(paren_state) andalso 
                                              endsWithClosingMark(rev_line,first_line_char)) orelse endsWithStop(rev_line) 
      val first_line_with_tail_white_space_stripped = rev(Basic.skipAll(rev first_line,whiteSpace))
      val init_paren_state = checkParens(first_line,{lp=0,rp=0,lb=0,rb=0,lcb=0,rcb=0,os=false})
      val first_line_suffices = let val line = first_line_with_tail_white_space_stripped
                                    val str = implode line 
                                    val res = (balancedParentheses(init_paren_state) andalso isOneProperId(line) 
                                               andalso not(Basic.isMember(str,leading_reserved)))
                                          orelse finished(rev line,init_paren_state)
                           in
                              res 
                           end
      fun superImplode([],res) = res
        | superImplode(line_list::more,res) = superImplode(more,(Basic.flatten line_list)@res)

      fun loop(paren_state,all_lines) = 
          let val (line,true_lines) = getFirstLine([])
              val rev_line_with_white_space_stripped = Basic.skipAll(rev line,whiteSpace)
              val line' = rev (nl::rev_line_with_white_space_stripped)
              val paren_state' = checkParens(line',paren_state)
              val no_more = finished(rev_line_with_white_space_stripped,paren_state')
          in
             if no_more then implode(superImplode(true_lines::all_lines,[]))
             else loop(paren_state',true_lines::all_lines)
          end
     val res = if first_line_suffices then (let val r = implode (Basic.flatten(rev true_lines)) in r end)
               else let val r = loop(init_paren_state,[true_lines])
                    in
                       r
                    end
  in 
     res
  end

fun getDirectInput() = 
    (print("\n>");
     Parse.setLinePos(1,0); 
     getInputFromPrompt())

val _ = let val ht : (string,Time.time) HashTable.hash_table =
                          HashTable.mkTable(HashString.hashString, op = ) (128,Basic.Never)
        in HashTable.clear(ht) end

fun clearAll() = (Options.first_time := true;
                  MS.clearHTable(SortOrder.sort_table);
                  SortOrder.global_sort_matrix := SortOrder.makeSortMatrix(!SortOrder.domain_max);
                  SortOrder.order_sorted_array := Array.array((!SortOrder.domain_max)+1,false);
                  MS.clearHTable(Data.structure_table);
                  MS.clearHTable(Data.constructor_table);
                  MS.clearHTable(Data.fsym_table);
                  MS.clearHTable(Data.sort_abbreviations);
                  Data.structure_and_domain_arities := MS.empty_mapping)

fun getInputAndProcess() = 
    let val (double_quote_code) = (34,92)
        fun doIt() = 
              let val in_str = getDirectInput()
                  val in_str' = if String.sub(in_str,0) = #"\n" then
                                   String.substring(in_str,1,String.size(in_str)-1)
                                else in_str
                  val _ = Paths.current_file := N.top_level_name
              in
                 if in_str' = "quit\n" orelse in_str = "quit" then 
                               (clearAll(); ABase.top_assum_base := ABase.empty_ab; 
			        Data.clearSignature(); print("\nExiting Athena...\n\n");0)

                 else if in_str' = "" then (Util.killAthena();0)
                 else 
                  ((let val istream = TextIO.openString in_str'
                         val (user_inputs,ok_input,parse_error) = 
                                  ((Parse.parse_from_stream istream),true,"") 
                                      handle e => let val _ = Parse.setLinePos(1,0)
                                                  in
                                                    ([],false,Semantics.exceptionToString(e))
                                                  end
                     in
                       if ok_input then
                           (List.app (fn i => processInputWithTopValBackUpRefreshed(i, 
										    [], 
										    ref(SV.valEnv({val_map=SV.empty_val_map,mod_map=SV.empty_mod_map})), 
										    Semantics.top_val_env, 
										    N.top_level_name,
										    top_loaded_files_ht))
                                     user_inputs;
  	                    TextIO.closeIn istream;
                            ABase.adjustHashTable(!SM.top_assum_base);
			     1
                            )
                       else
                          (print(parse_error);1
 			   )
                     end) handle e => (handleException(e);1))
              end
    in
       doIt()
    end

fun escape(str) = 
  let val L = explode(str)
      val escape_char = #"\\"
      val quote_char = #"\""
      fun loop([],string_list) = String.concat(rev(string_list))
        | loop(c::more,string_list) = 
           if c = escape_char then 
              loop(more,(implode([c,c]))::string_list)
           else if c = quote_char then
                   loop(more,(implode([escape_char,c]))::string_list)
                else loop(more,implode([c])::string_list)
  in
     loop(L,[])
  end
       
(**** qqq PROCESSSTRING DEFINITION ****)
fun processString(cmd,mod_path,env,eval_env) =
    let val stream = TextIO.openString (cmd)
        val inputs  = Parse.parse_from_stream(stream)
        val responses = List.app (fn i => (processInput(i,mod_path,env, Semantics.top_val_env, N.top_level_name,top_loaded_files_ht))) inputs
    in 
      ()
    end

val _ = (Semantics.processString := processString)

fun processAlreadyParsedInputs(inputs,mod_path,env,eval_env) =
        let val _ = List.app (fn i => (processInput(i,mod_path,env, Semantics.top_val_env, N.top_level_name,top_loaded_files_ht))) inputs
    in () 
    end

val _ = (Semantics.processAlreadParsedInputsRef := processAlreadyParsedInputs)

fun makeLibFileName(home,fname) = List.foldl (fn (dir, path) => Paths.makePath(path, dir)) home ["lib", "basic", fname]

val (athena_home_option,athena_home) = (Paths.athena_home_option,Paths.athena_home)

fun auxLoadFiles(files, mod_path,env,eval_env,ht) = List.app (fn f => auxLoadFile(f, mod_path,env,eval_env,Position.dummy_pos,ht)) files

fun init(file_name_option) =   
     if not(!(Options.first_time)) then ()
     else 
     let val _ = print("\nLoading basic libraries...\n\n")
         val _ = StructureAnalysis.addFSym(Data.declared(StructureAnalysis.equality_symbol))
         val env = ref(SV.empty_val_env_functional)
         val eval_env = Semantics.top_val_env
         val mod_path = []
	 val _ = Options.silent_mode := true  
         val _ = processString("(datatype "^N.boolean_sort_name^
			       " "^N.true_logical_name^" "^
			       N.false_logical_name^")",mod_path,env,eval_env)
         val _ = processString("(domains Int Real Ide)",mod_path,env,eval_env)
         val _ = processString("(subsort Int Real)",mod_path,env,eval_env)
         val _ = processString("(declare app ((S T) -> ((Fun S T) S) T))",mod_path,env,eval_env)
         val _ = processString("(declare ("^
		 N.addition_name^" "^N.subtraction_name^" "^N.multiplication_name^" "^N.division_name^" "^N.modulo_name^") "^
		 "(-> (Real Real) Real))",mod_path,env,eval_env)
         val _ = processString("(declare ("^
			       N.formal_less_name^" "^N.formal_leq_name^" "^N.formal_greater_name^" "^N.formal_geq_name^") "^
			       "(-> (Real Real) Boolean))",mod_path,env,eval_env)
         val _ = processString("(declare "^N.ite_name^" ((T) -> (Boolean T T) T))",mod_path,env,eval_env)
         val _ = processString("(declare "^N.MOR_name^" ((S T) -> (S T) Boolean))",mod_path,env,eval_env)
         val prop_con_term_names = "(And Or If Iff)"
         val _ = processString("(declare "^prop_con_term_names^" (-> (Boolean Boolean) Boolean))",mod_path,env,eval_env)
         val _ = processString("(declare "^N.Not_name^" (-> (Boolean) Boolean))",mod_path,env,eval_env)
         val _ = processString("module Real { define [+ - * / % < <= > >=] := [+ - * / % < <= > >=] }",mod_path,env,eval_env)
         fun makeAHString(s) = (case (String.tokens (fn c => c = #"\\") s) of
                                   (ah as _::_::_) => (List.foldr (fn (s1,s2) => s1 ^ "\\\\" ^ s2) "" ah)
                                  | _ => s)
         val (lp,rp,quote) = (Basic.lparen,Basic.rparen,Basic.string_quote)
	 val _ = Paths.addPath (OS.FileSys.getDir())
	 val _ = Paths.createTempDir ()
	 val util_ath = makeLibFileName(athena_home,"util.ath")
	 val random_sentences_ath = makeLibFileName(athena_home,"make_random_problems.ath")
	 val rewriting_ath = makeLibFileName(athena_home,"rewriting.ath")
	 val pairs_ath = makeLibFileName(athena_home,"pairs.ath")
	 val options_ath = makeLibFileName(athena_home,"options.ath")
	 val property_management_ath = makeLibFileName(athena_home,"st.ath")
         val dt_model_check_ath = makeLibFileName(athena_home,"dt-model-checker.ath")
         val _ = SM.makePrivateLst(["force"])
         val top_files = [util_ath, rewriting_ath, pairs_ath, options_ath] (*** fun_def_ath,  ***)
         val _ = auxLoadFiles(top_files, [],Semantics.top_val_env,Semantics.top_val_env,top_loaded_files_ht)
             handle e => (print("\nEvaluation error encountered during the loading of the initial files:\n");
                          handleException(e))
         val _ = List.app (fn i => let val cmd = "(define-tuple-datatype " ^ i ^ ")"
                                   in
                                      processString(cmd,mod_path,env,eval_env)
                                   end)
                          ["2", "3", "4", "5"]
(** Making private the names of all Athena functions that are by default called by SML code: **)         
         val _ = SM.makePrivateLst(["diff*", "evaluate","compile-symbols", "compile-symbols-simple", "compile-symbols-simple-with-default",
	                            "auto-induction-definition",
	 	                    "dcompile-symbol", "string->symbol","get-defined-prop", "-->", N.mapApplyFun_name,
                                    N.empty_mapping_name, N.addMapFun_name, N.makeMapFun_name, N.addTableFun_name, N.makeTableFun_name, N.findTableFun_name])
         val top_files2 = [dt_model_check_ath ,property_management_ath, random_sentences_ath]
         val _ = auxLoadFiles(top_files2, [],Semantics.top_val_env,Semantics.top_val_env,top_loaded_files_ht)
             handle e => (print("\nEvaluation error encountered during the loading of the initial files:\n");
                          handleException(e))	     	          
         val _ = HashTable.clear(top_loaded_files_ht)
         val _ = List.app (fn sym => SM.setEvalProcBeingDefinedFlag(sym,false,NONE,NONE,NONE)) 
                          [N.maddition_symbol,N.msubtraction_symbol,N.mmultiplication_symbol,N.mdivision_symbol,
                           N.mequal_logical_symbol,N.mformal_less_symbol,N.mformal_leq_symbol,N.mite_symbol,
                           N.mformal_greater_symbol, N.mformal_geq_symbol]
         val ite_str = "(assert* ite-axioms := [((ite true ?x _) = ?x) ((ite false _ ?y) = ?y)])"
         val _ = processString(ite_str,mod_path,env,eval_env)

         val _ = map (fn struc => SM.addSelectorAxioms(struc,mod_path,env,eval_env)) (Data.getAllStructures());
     in
	 (Options.silent_mode := false;
          
          (case file_name_option of
              NONE => ()
            | SOME(fname) => ((let val _ = auxLoadFiles([fname], [],Semantics.top_val_env,Semantics.top_val_env,top_loaded_files_ht)
			       in () end)
                                   handle e => (print("\nEvaluation error encountered during\nthe loading of the given file: "^fname^".");
                                                handleException(e))));
         HashTable.clear(top_loaded_files_ht);
         Options.first_time := false)
     end

fun restartAthena() = 
      (SemanticValues.top_val_env := SemanticValues.valEnv({val_map=Semantics.empty_val_map,mod_map=Semantics.empty_mod_map});
       Semantics.updateTopValEnvLstOldAndFast(TopEnv.init_val_bindings);
       ABase.top_assum_base := ABase.empty_ab;
       Data.clearSignature();
       let
         val env = ref(SV.empty_val_env_functional)
         val eval_env = Semantics.top_val_env
         val mod_path = []
	 val _ = Options.silent_mode := true  
         val _ = processString("(datatype "^N.boolean_sort_name^
			       " "^N.true_logical_name^" "^
			       N.false_logical_name^")",mod_path,env,eval_env)
         val _ = processString("(domains Int Real Ide)",mod_path,env,eval_env)
         val _ = processString("(subsort Int Real)",mod_path,env,eval_env)
         val _ = processString("(declare ("^
		 N.addition_name^" "^N.subtraction_name^" "^N.multiplication_name^" "^N.division_name^" "^N.modulo_name^") "^
		 "(-> (Real Real) Real))",mod_path,env,eval_env)
         val _ = processString("(declare ("^
			       N.formal_less_name^" "^N.formal_leq_name^" "^N.formal_greater_name^" "^N.formal_geq_name^") "^
			       "(-> (Real Real) Boolean))",mod_path,env,eval_env)
         val _ = processString("(declare "^N.ite_name^" ((T) -> (Boolean T T) T))",mod_path,env,eval_env)

         val _ = processString("(declare "^N.MOR_name^" ((S T) -> (S T) Boolean))",mod_path,env,eval_env)
         val prop_con_term_names = "(And Or If Iff)"
         val _ = processString("(declare "^prop_con_term_names^" (-> (Boolean Boolean) Boolean))",mod_path,env,eval_env)
         val _ = processString("(declare "^N.Not_name^" (-> (Boolean) Boolean))",mod_path,env,eval_env)
         val _ = processString("module Real { define [+ - * / % < <= > >=] := [+ - * / % < <= > >=] }",mod_path,env,eval_env)
         val _ = StructureAnalysis.addFSym(Data.declared(StructureAnalysis.equality_symbol))
         val util_ath = makeLibFileName(athena_home,"util.ath")
    	 val pairs_ath = makeLibFileName(athena_home,"pairs.ath")	
	 val rewriting_ath = makeLibFileName(athena_home,"rewriting.ath")
	 val options_ath = makeLibFileName(athena_home,"options.ath")
	 val fun_def_ath = makeLibFileName(athena_home,"fundef.ath")
	 val property_management_ath = makeLibFileName(athena_home,"st.ath")
         val dt_model_check_ath = makeLibFileName(athena_home,"dt-model-checker.ath")
         val top_files = [util_ath, rewriting_ath, pairs_ath, options_ath] (*** fun_def_ath, ***) 
         val _ = auxLoadFiles(top_files, [],Semantics.top_val_env,Semantics.top_val_env,top_loaded_files_ht)
           handle e => (print("\nEvaluation error encountered during the loading of the initial files:\n");
                        handleException(e))			  
         val _ = SM.makePrivateLst(["diff*", "evaluate","compile-symbols", "compile-symbols-simple", "compile-symbols-simple-with-default", "dcompile-symbol", 
	                            "auto-induction-definition", "string->symbol","get-defined-prop", "-->", N.mapApplyFun_name, 
                                    N.empty_mapping_name,N.addMapFun_name, N.makeMapFun_name,N.addTableFun_name, N.makeTableFun_name, N.findTableFun_name])
         val top_files2 = [property_management_ath, dt_model_check_ath]	                    
         val _ = auxLoadFiles(top_files2, [],Semantics.top_val_env,Semantics.top_val_env,top_loaded_files_ht)
                  handle e => (print("\nEvaluation error encountered during the loading of the initial files:\n");
                               handleException(e))
         val _ = HashTable.clear(top_loaded_files_ht) 
         val _ = List.app (fn sym => SM.setEvalProcBeingDefinedFlag(sym,false,NONE,NONE,NONE)) 
                          [N.maddition_symbol,N.msubtraction_symbol,N.mmultiplication_symbol,N.mdivision_symbol,
                           N.mequal_logical_symbol,N.mformal_less_symbol,N.mformal_leq_symbol,N.mite_symbol,
                           N.mformal_greater_symbol, N.mformal_geq_symbol]
         val ite_str = "(assert* ite-axioms := (fun-def [(ite true ?x _) = ?x  | (ite false _ ?y) = ?y]))"
         val _ = processString(ite_str,mod_path,env,eval_env)
         val _ = map (fn struc => SM.addSelectorAxioms(struc,mod_path,env,eval_env)) (Data.getAllStructures())
	 val _ = Options.silent_mode := false
       in
          ()
       end)

val _ = (TopEnv.restartAthena_ref := restartAthena)
         
end (** Of structure Drive **)
