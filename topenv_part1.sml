(*======================================================================

Definitions of primitive procedures and methods (bound in Athena's top-level
environment), part 1 of 2. 

=======================================================================*)

structure TopEnv1 = 

struct

open Semantics

fun makeAthenaError(msg) = raise AthenaError(msg)

fun isNumeralValue(v) = 
   (case coerceValIntoTerm(v) of
       SOME(t) => (case (AthTerm.getNumVal(t)) of
                      SOME(_) => true
                    | _ => false)
     | _ => false)

fun getIntValue(v) = 
   (case coerceValIntoTerm(v) of
       SOME(t) => (case (AthTerm.getNumVal(t)) of
                      SOME(A.int_num(i,_),neg1) =>  SOME(getSignedInt(i,neg1))
                    | _ => NONE)
     | _ => NONE)


fun isProp(v) = (case coerceValIntoProp(v) of SOME(_) => true | _ => false)
  

fun readFile(fname) = 
      let val s = TextIO.openIn(fname)
          val res = TextIO.inputAll(s)
          val _ = (TextIO.closeIn(s)) handle _ => ()
      in
         res 
      end
         
fun readFileLines(fname) = 
   let val s = TextIO.openIn(fname)
       fun getLines(res) = 
                let val line = TextIO.inputLine(s) 
		in
		   if line = "" then rev(res) else getLines((MLStringToAthString line)::res)
		end
       val res = listVal(getLines([]))		
       val _ = (TextIO.closeIn(s)) handle _ => ()
   in
      res 
   end

fun readFileLinesPrimUFun(v,_,_) = 
       (case isStringValConstructive(v) of
           SOME(str) => ((readFileLines str) handle _ => primError("Unable to read file "^str))
         | _ => primError(wrongArgKind(N.readFileLines_name,1,stringLCType,v)))

fun readDirEntries(v,_,_) = 
       (case isStringValConstructive(v) of
           SOME(str) => ((let val athena_entry_names = map MLStringToAthString (Basic.readAllDirFiles(str))
                          in
                            listVal(athena_entry_names)
                          end)  handle _ => primError("Unable to read directory "^str))
         | _ => primError(wrongArgKind(N.listAllDirEntries_name,1,stringLCType,v)))

fun readDirEntriesRecursively(v,_,_) = 
       (case isStringValConstructive(v) of
           SOME(str) => ((let val athena_entry_names = map MLStringToAthString (Basic.listDirFilesRecursively(str))
                          in
                            listVal(athena_entry_names)
                          end)  handle _ => primError("Unable to read directory "^str))
         | _ => primError(wrongArgKind(N.listAllDirEntriesRecursively_name,1,stringLCType,v)))

fun mapKeyValuesPrimUFun(v,_,_) = 
     (case v of
         mapVal(m) => listVal(map (fn (x,y) => listVal([x,y])) (Maps.listKeyValuePairs m))
       | _ => primError(wrongArgKind(N.mapKeyValuesFun_name,1,mapLCType,v)))

fun sentSubtermsPrimUFun(v,_,_) = 
    (case coerceValIntoProp(v) of 
        SOME(P) => let val terms = P.subterms(P)
                   in
                     listVal(map termVal terms)
                   end
      | _ => (case coerceValIntoTerm(v) of 
                 SOME(t) => let val terms = AT.subtermsDefault(t)
                            in
			      listVal(map termVal terms)
                            end
               | _ => primError(wrongArgKind(N.sentSubtermsFun_name,1,termLCType,v))))

fun subtermsPrimUFun(v,_,_) = 
    (case coerceValIntoTerm(v) of 
                 SOME(t) => let val terms = AT.subtermsDefault(t)
                            in
			      listVal(map termVal terms)
                            end
               | _ => primError(wrongArgKind(N.subtermsFun_name,1,termLCType,v)))

fun hasMonoSortPrimUFun(v,_,_) = 
    (case coerceValIntoTerm(v) of 
        SOME(t) => let val flag = F.isGround(AT.getSort(t))
                   in
                     MLBoolToAth(flag)
                   end
      | _ => primError(wrongArgKind(N.hasMonoSortFun_name,1,termLCType,v)))


(*************************************************************************************************************)
(*                                         TOP-LEVEL FUNCTIONS                                               *)
(*************************************************************************************************************)

val pprint = fn (s,P) => (P.toPrettyString(s,P,F.makeVarSortPrinter()))

fun stringToSymbolAux(str) = 
  (case Data.isTermConstructorAsFSymOptionGeneral(A.makeMS(str,NONE)) of
      SOME(f) => SOME(termConVal(regFSym(f)))
    | _ => (case AbstractSyntax.getAthNumber(str) of
               SOME(anum) => SOME(termConVal(athNumFSym(anum)))
             | _ => NONE))

fun getHTSizeHint(val_arg) =
  (case val_arg of
      termVal(t) => (case AthTerm.getNumVal(t) of
                         SOME(A.int_num(i,_),neg1) => getSignedInt(i,neg1)
                       | _ => 197)
    | _ => primError(wrongArgKind(N.TermHT_lookup_name,1,termLCType,val_arg)))

val (max_int,max_int_str) = 
            (case Int.maxInt of
                  SOME(i) => (i,Int.toString(i))
                | _ => (1073741823,"1073741823"))


val max_int_val = termVal(AthTerm.makeNumTerm(A.int_num(max_int,ref max_int_str)))

open SMTOutput

fun yicesSolvePrimBFun(v,v',env,_) = 
  let val [yin0,yin1,yin2,yin3,yin4] = ["yin0.ys","yin1.ys","yin2.ys","yino.ys","yine.ys"]
      fun deleteFiles() = (List.app OS.FileSys.remove [yin0,yin1,yin2,yin3,yin4]) handle _ => ()
      val _ = deleteFiles()
      val (domain_stream,dec_stream,main_stream) = (TextIO.openOut(yin0),TextIO.openOut(yin1),TextIO.openOut(yin2))
      val var_table: ATV.ath_term_var ATV.htable = ATV.makeHTableWithVarEq(ATV.nameEq)
      val fsym_table:bool MS.htable = MS.makeHTableWithInitialSize(251)
      val poly_to_mono_sort_table:(string,(F.term list * F.term)) HashTable.hash_table = HashTable.mkTable(Basic.hashString, op=) (100,Basic.Never)

      val _ = (MS.insert(fsym_table,mfmap_empty_map_symbol,true);
               MS.insert(fsym_table,mfmap_update_symbol,true);
               MS.insert(fsym_table,mfmap_apply_symbol,true))

      val dom_table: bool MS.htable = MS.makeHTableWithInitialSize(97)

      val _ = (MS.insert(dom_table,Names.mboolean_sort_symbol,true);MS.insert(dom_table,Names.mint_sort_symbol,true);
               MS.insert(dom_table,Names.mreal_sort_symbol,true))
      val counter = ref 0 
      val t1 = Time.toReal(Time.now())
      val tables = {domain_stream=domain_stream,dec_stream=dec_stream,main_stream=main_stream,
      	            poly_to_mono_sort_table=poly_to_mono_sort_table,
                    var_table=var_table,fsym_table=fsym_table,domain_table=dom_table,sel_counter=counter}
      fun doPrelude() =  
                      (case isStringValConstructive(v') of 
                            SOME(file_name) => TextIO.output(main_stream,"(include \""^file_name^"\")\n")
                          | _ => (TextIO.output(dec_stream,"(include \"yin0.ys\")\n");
                                  TextIO.output(main_stream,"(include \"yin1.ys\")\n\n")))
  in
      (case coerceValIntoProp(v) of
          SOME(P) => let val _ = (doPrelude();
                                  TextIO.output(main_stream,"(assert ");
                                  ((Prop.writeSMT(P,tables)) handle Basic.Fail(msg) => primError(msg));
                                  TextIO.output(main_stream,")\n\n(check)\n"))
                         val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                         val t2 = Time.toReal(Time.now())
                         val command = "yices.exe  -e yin2.ys > yino.ys 2> yine.ys"
                         val _ = print("\nTranslation done in "^(Real.toString(Real.-(t2,t1)))^" seconds... About to call the SMT solver...\n")
                         val _ = OS.Process.system(command)
                         val smt_answer_stream = TextIO.openIn("yino.ys")
                         val res = SMTOutput.processYicesOutput(smt_answer_stream,Prop.getConjuncts P,false,var_table,fsym_table,poly_to_mono_sort_table,NONE)
                         val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                      in
                          res 
                      end
       | _ => (case v of 
                  listVal(vals) => 
                      let val props = Semantics.getProps(vals,"the argument list given to "^N.yicesSolveFun_name',env)
                          val _ = (doPrelude();
                                   ((Prop.writeSMTLst(props,[],tables)) handle Basic.Fail(msg) => primError(msg));
                                   TextIO.output(main_stream,"\n\n(check)\n"))                           
                          val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                          val t2 = Time.toReal(Time.now())
                          val command = "yices.exe -e yin2.ys > yino.ys 2> yine.ys"
                          val _ = print("\nTranslation done in "^(Real.toString(Real.-(t2,t1)))^" seconds... About to call the SMT solver...\n")
                          val _ = OS.Process.system(command)
                          val smt_answer_stream = TextIO.openIn("yino.ys")
                          val res = SMTOutput.processYicesOutput(smt_answer_stream,Prop.getConjunctsLst props,false,var_table,fsym_table,poly_to_mono_sort_table,NONE)
                          val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                       in
                          res 
                       end
               | _ => primError(wrongArgKind(N.yicesSolveFun_name',1,propLCType,v))))
  end

fun yicesSolvePrimUFun(v,env,_) = 
  let val [yin0,yin1,yin2,yin3,yin4] = ["yin0.ys","yin1.ys","yin2.ys","yino.ys","yine.ys"]
      fun deleteFiles() = (List.app OS.FileSys.remove [yin0,yin1,yin2,yin3,yin4]) handle _ => ()
      val _ = deleteFiles()
      val (domain_stream,dec_stream,main_stream) = (TextIO.openOut(yin0),TextIO.openOut(yin1),TextIO.openOut(yin2))
      val var_table: ATV.ath_term_var ATV.htable = ATV.makeHTableWithVarEq(ATV.nameEq)
      val fsym_table:bool MS.htable = MS.makeHTableWithInitialSize(251)
      val _ = (MS.insert(fsym_table,mfmap_empty_map_symbol,true);
               MS.insert(fsym_table,mfmap_update_symbol,true);
               MS.insert(fsym_table,mfmap_apply_symbol,true))
      val dom_table: bool MS.htable = MS.makeHTableWithInitialSize(97)
      val _ = (MS.insert(dom_table,Names.mboolean_sort_symbol,true);MS.insert(dom_table,Names.mint_sort_symbol,true);
               MS.insert(dom_table,Names.mreal_sort_symbol,true))
      val counter = ref 0 
      val poly_to_mono_sort_table:(string,(F.term list * F.term)) HashTable.hash_table = HashTable.mkTable(Basic.hashString, op=) (100,Basic.Never)
      val t1 = Time.toReal(Time.now())
      val tables = {domain_stream=domain_stream,dec_stream=dec_stream,main_stream=main_stream,
      	            poly_to_mono_sort_table=poly_to_mono_sort_table,
                    var_table=var_table,fsym_table=fsym_table,domain_table=dom_table,sel_counter=counter}
      fun doPrelude() =  
            (TextIO.output(dec_stream,"(include \"yin0.ys\")\n");
             TextIO.output(main_stream,"(include \"yin1.ys\")\n\n"))
      fun monomorphize(P) = if P.isPoly(P) then P.makeMonomorphicInstance(P) else P
  in
      (case coerceValIntoProp(v) of
          SOME(P) => let val P = monomorphize(P) 
                         val _ = (doPrelude();
                                  TextIO.output(main_stream,"(assert ");
                                  (Prop.writeSMT(P,tables) handle Basic.Fail(msg) => primError(msg));
                                  TextIO.output(main_stream,")\n\n(check)\n"))
                         val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                         val t2 = Time.toReal(Time.now())
                         val command = "yices.exe -e yin2.ys > yino.ys 2> yine.ys"
                         val _ = OS.Process.system(command)
                         val t3 = Time.toReal(Time.now())
                         val _ = print("\nYices finished in "^(Real.toString(Real.-(t3,t2)))^" seconds...\n")
                         val smt_answer_stream = TextIO.openIn("yino.ys")
                         val res = SMTOutput.processYicesOutput(smt_answer_stream,Prop.getConjuncts P,false,var_table,fsym_table,poly_to_mono_sort_table,NONE)
                         val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                      in
                          res 
                      end
       | _ => (case v of 
                  listVal(vals) => 
                      let val props = map monomorphize (Semantics.getProps(vals,"the argument list given to "^N.yicesSolveFun_name,env))
                          val _ = (doPrelude();
                                   (Prop.writeSMTLst(props,[],tables) handle Basic.Fail(msg) => primError(msg));
                                   TextIO.output(main_stream,"\n\n(check)\n"))                           
                          val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                          val t2 = Time.toReal(Time.now())
                          val command = "yices.exe  -e yin2.ys > yino.ys 2> yine.ys"
                          val _ = OS.Process.system(command)
                          val smt_answer_stream = TextIO.openIn("yino.ys")
                          val res = SMTOutput.processYicesOutput(smt_answer_stream,Prop.getConjunctsLst props,false,var_table,fsym_table,poly_to_mono_sort_table,NONE)
                          val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                       in
                          res 
                       end
               | _ => primError(wrongArgKind(N.yicesSolveFun_name,1,propLCType,v))))
  end

(** Main yices solving code (~ 2016): **)

(**
     Pass empty props and P_or_props = 1 for a single sentence to solve. 
     Pass non-empty props and P_or_props = 2 if this is a list-based instance 
     (i.e. if a whole list of sentences are given as constraints to solve.)

     For the list-based version, pass an empty list of weights if this is not 
     a Max-SAT problem, and a non-empty list of weights otherwise. 
**)

fun yicesSolve(P,props,weight_strings,time_limit_option,ht_option,stats_option) = 
  let val [yin0,yin1,yin2,yin3,yin4] = ["yin0.ys","yin1.ys","yin2.ys","yino.ys","yine.ys"]
      fun deleteFiles() = (List.app OS.FileSys.remove [yin0,yin1,yin2,yin3,yin4]) handle _ => ()
      val _ = deleteFiles()
      fun addBindings(m,bindings) = Maps.insertLst(m,bindings)
      val (domain_stream,dec_stream,main_stream) = (TextIO.openOut(yin0),TextIO.openOut(yin1),TextIO.openOut(yin2))
      val var_table: ATV.ath_term_var ATV.htable = ATV.makeHTableWithVarEq(ATV.nameEq)
      val fsym_table:bool MS.htable = MS.makeHTableWithInitialSize(251)
      val _ = (MS.insert(fsym_table,mfmap_empty_map_symbol,true);
               MS.insert(fsym_table,mfmap_update_symbol,true);
               MS.insert(fsym_table,mfmap_apply_symbol,true))
      val dom_table: bool MS.htable = MS.makeHTableWithInitialSize(97)
      val _ = (MS.insert(dom_table,Names.mboolean_sort_symbol,true);MS.insert(dom_table,Names.mint_sort_symbol,true);
               MS.insert(dom_table,Names.mreal_sort_symbol,true))
      val counter = ref 0 
      val t1 = Time.toReal(Time.now())
      val poly_to_mono_sort_table:(string,(F.term list * F.term)) HashTable.hash_table = HashTable.mkTable(Basic.hashString, op=) (100,Basic.Never)
      val tables = {domain_stream=domain_stream,dec_stream=dec_stream,main_stream=main_stream,
                    poly_to_mono_sort_table=poly_to_mono_sort_table,
                    var_table=var_table,fsym_table=fsym_table,domain_table=dom_table,sel_counter=counter}
      fun doPrelude() =  
            (TextIO.output(dec_stream,"(include \"yin0.ys\")\n");
             TextIO.output(main_stream,"(include \"yin1.ys\")\n\n"))
      fun monomorphize(P) = if P.isPoly(P) then P.makeMonomorphicInstance(P) else P
  in
                     let 
                         val P = monomorphize(P) 
			 val props = map monomorphize props 
                         val t1 = Time.toReal(Time.now())
                         val _ = if null(props) then 
                                  (doPrelude();
                                    TextIO.output(main_stream,"(assert ");
                                    (Prop.writeSMT(P,tables) handle Basic.Fail(msg) => primError(msg));
                                    TextIO.output(main_stream,")\n\n(check)\n"))
                                 else 
                                   (doPrelude();
                                     (Prop.writeSMTLst(props,weight_strings,tables) handle Basic.Fail(msg) => primError(msg));
                                     TextIO.output(main_stream,"\n\n(check)\n"))
                         val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                         val t2 = Time.toReal(Time.now())
			 val translation_time = Real.-(t2,t1)
                         val command = (case time_limit_option of
                                           SOME(str) => "yices.exe --timeout=" ^ str ^ " -e yin2.ys > yino.ys 2> yine.ys"
                                         | _ => "yices.exe -e yin2.ys > yino.ys 2> yine.ys")
                         val _ = OS.Process.system(command)
                         val t3 = Time.toReal(Time.now())
			 val solving_time = Real.-(t3,t2)
			 val constraint_size = Prop.size(P)
			 val _ = (case stats_option of 
                                     SOME(cv as (cellVal(c))) => let val binding1 = (termVal(AthTerm.makeIdeConstant("translation-time")),
				                                                     termVal(AthTerm.makeNumTerm(A.real_num(translation_time,ref ""))))
                                                                     val binding2 = (termVal(AthTerm.makeIdeConstant("solving-time")),
				                                                     termVal(AthTerm.makeNumTerm(A.real_num(solving_time,ref ""))))
                                                                     val binding3 = (termVal(AthTerm.makeIdeConstant("constraint_size")),
				                                                     termVal(AthTerm.makeNumTerm(A.int_num(constraint_size,ref ""))))
                                                                     val map_val = SV.mapVal(addBindings(Maps.makeMap(SV.compare),[binding1,binding2,binding3]))
                                                                 in
                                                                   (c := map_val)
                                                                 end
                                   | _ => ())
                         val smt_answer_stream = TextIO.openIn("yino.ys")
                         val res = SMTOutput.processYicesOutput(smt_answer_stream,Prop.getConjuncts P,false,var_table,fsym_table,poly_to_mono_sort_table,ht_option)
                         val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                      in
                          res 
                      end
  end

fun cvcSolvePrimUFun(v,env,_) = 
  let fun debugPrint(s) = print(s)
      val _ = print("\nSTARTING HERE --------------------------------------------------- \n")
      val [yin0,yin1,yin2,yin3,yin4] = ["cvc0.cvc","cvc1.cvc","cvc2.cvc","cvco.cvc","cvce.cvc"]
      fun deleteFiles() = (List.app OS.FileSys.remove [yin0,yin1,yin2,yin3,yin4]) handle _ => ()
      val _ = deleteFiles()
      val (domain_stream,dec_stream,main_stream) = (TextIO.openOut(yin0),TextIO.openOut(yin1),TextIO.openOut(yin2))
      val var_table: string ATV.htable = ATV.makeHTableWithVarEq(ATV.nameEq)
      val inverse_var_table: (string,ATV.ath_term_var) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (251,Basic.Never)
      val fsym_table:string MS.htable = MS.makeHTableWithInitialSize(251)
      val inverse_fsym_table: (string,MS.mod_symbol) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (251,Basic.Never)
      val _ = (MS.insert(fsym_table,mfmap_empty_map_symbol,fmap_empty_map_name);
               MS.insert(fsym_table,mfmap_update_symbol,fmap_update_name);
               MS.insert(fsym_table,N.mtrue_logical_symbol,"TRUE");
               MS.insert(fsym_table,N.mfalse_logical_symbol,"FALSE");
               MS.insert(fsym_table,mfmap_apply_symbol,fmap_apply_name))
      val _ = ((HashTable.insert inverse_fsym_table (fmap_empty_map_name,mfmap_empty_map_symbol));
               (HashTable.insert inverse_fsym_table (fmap_update_name,mfmap_update_symbol));
               (HashTable.insert inverse_fsym_table (fmap_apply_name,mfmap_apply_symbol));
               (HashTable.insert inverse_fsym_table ("TRUE",N.mtrue_logical_symbol));
               (HashTable.insert inverse_fsym_table ("FALSE",N.mfalse_logical_symbol)))
      val dom_table: (string,string) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (97,Basic.Never)
      val inverse_domain_table: (string,string) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (97,Basic.Never)
      val _ = ((HashTable.insert dom_table (Names.boolean_sort_name,"BOOLEAN"));(HashTable.insert dom_table (Names.int_sort_name,"INT"));
               (HashTable.insert dom_table (Names.real_sort_name,"REAL")))
      val _ = ((HashTable.insert inverse_domain_table ("INT",Names.int_sort_name));(HashTable.insert inverse_domain_table ("REAL",Names.real_sort_name));
               (HashTable.insert inverse_domain_table ("BOOLEAN",Names.boolean_sort_name)))
      val counter = ref 0 
      val fsym_counter = ref 0 
      val dom_counter = ref 0 
      val var_counter = ref 0 
      val t1 = Time.toReal(Time.now())
      val tables = {domain_stream=domain_stream,dec_stream=dec_stream,main_stream=main_stream,inverse_fsym_table=inverse_fsym_table,fsym_counter=fsym_counter,
                    dom_counter=dom_counter,var_counter=var_counter,
                    var_table=var_table,inverse_var_table=inverse_var_table,
                    fsym_table=fsym_table,domain_table=dom_table,inverse_domain_table=inverse_domain_table,sel_counter=counter}
      fun doPrelude() =  ()
      fun monomorphize(P) = if P.isPoly(P) then P.makeMonomorphicInstance(P) else P
  in
      (case coerceValIntoProp(v) of
          SOME(P) => let 
	                 val P = monomorphize(P) 
                         val _ = (doPrelude();
                                  TextIO.output(main_stream,"\nCHECKSAT ");
                                  (Prop.writeCVC(P,tables) handle Basic.Fail(msg) => primError(msg));
                                  TextIO.output(main_stream,";\n\nCOUNTERMODEL;\n"))
                         				  
                         val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                         val stream = TextIO.openAppend(yin0)
                         val _ = (TextIO.output(stream,readFile(yin1));TextIO.output(stream,"\n\n");TextIO.output(stream,readFile(yin2));TextIO.closeOut(stream))
                         val t2 = Time.toReal(Time.now())
                         val _ = debugPrint("\nTranslation to CVC done in "^(Real.toString(Real.-(t2,t1)))^" seconds... About to call CVC...\n")
                         val command = if Paths.is_unix then Names.cvc4_binary ^ " --produce-models cvc0.cvc > cvco.ys 2> cvce.ys"
                                       else "cvcopt.exe --produce-models cvc0.cvc > cvco.ys 2> cvce.ys"
                         val _ = OS.Process.system(command)
                         val t3 = Time.toReal(Time.now())
                         val _ = debugPrint("\nCVC finished in "^(Real.toString(Real.-(t3,t2)))^" seconds...\n")
                         val smt_answer_stream = TextIO.openIn("cvco.ys")
                         val res = SMTOutput.processCVCOutput(smt_answer_stream,[],false,tables,NONE)
                         val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                      in
                          res 
                      end)
  end

fun cvcSolveGeneric(P,timeout_option,ht_option) = 
  let fun debugPrint(s) = ()
      val [yin0,yin1,yin2,yin3,yin4] = ["cvc0.cvc","cvc1.cvc","cvc2.cvc","cvco.cvc","cvce.cvc"]
      fun deleteFiles() = (List.app OS.FileSys.remove [yin0,yin1,yin2,yin3,yin4]) handle _ => ()
      val _ = deleteFiles()
      val (domain_stream,dec_stream,main_stream) = (TextIO.openOut(yin0),TextIO.openOut(yin1),TextIO.openOut(yin2))
      val var_table: string ATV.htable = ATV.makeHTableWithVarEq(ATV.nameEq)
      val inverse_var_table: (string,ATV.ath_term_var) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (251,Basic.Never)
      val fsym_table:string MS.htable = MS.makeHTableWithInitialSize(251)
      val inverse_fsym_table: (string,MS.mod_symbol) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (251,Basic.Never)
      val _ = (MS.insert(fsym_table,mfmap_empty_map_symbol,fmap_empty_map_name);
               MS.insert(fsym_table,mfmap_update_symbol,fmap_update_name);
               MS.insert(fsym_table,N.mtrue_logical_symbol,"TRUE");
               MS.insert(fsym_table,N.mfalse_logical_symbol,"FALSE");
               MS.insert(fsym_table,mfmap_apply_symbol,fmap_apply_name))
      val _ = ((HashTable.insert inverse_fsym_table (fmap_empty_map_name,mfmap_empty_map_symbol));
               (HashTable.insert inverse_fsym_table (fmap_update_name,mfmap_update_symbol));
               (HashTable.insert inverse_fsym_table (fmap_apply_name,mfmap_apply_symbol));
               (HashTable.insert inverse_fsym_table ("TRUE",N.mtrue_logical_symbol));
               (HashTable.insert inverse_fsym_table ("FALSE",N.mfalse_logical_symbol)))
      val dom_table: (string,string) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (97,Basic.Never)
      val inverse_domain_table: (string,string) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (97,Basic.Never)
      val _ = ((HashTable.insert dom_table (Names.boolean_sort_name,"BOOLEAN"));(HashTable.insert dom_table (Names.int_sort_name,"INT"));
               (HashTable.insert dom_table (Names.real_sort_name,"REAL")))
      val _ = ((HashTable.insert inverse_domain_table ("INT",Names.int_sort_name));(HashTable.insert inverse_domain_table ("REAL",Names.real_sort_name));
               (HashTable.insert inverse_domain_table ("BOOLEAN",Names.boolean_sort_name)))
      val counter = ref 0 
      val fsym_counter = ref 0 
      val dom_counter = ref 0 
      val var_counter = ref 0 
      val t1 = Time.toReal(Time.now())
      val tables = {domain_stream=domain_stream,dec_stream=dec_stream,main_stream=main_stream,inverse_fsym_table=inverse_fsym_table,fsym_counter=fsym_counter,
                    dom_counter=dom_counter,var_counter=var_counter,
                    var_table=var_table,inverse_var_table=inverse_var_table,
                    fsym_table=fsym_table,domain_table=dom_table,inverse_domain_table=inverse_domain_table,sel_counter=counter}
      fun doPrelude() =  ()
      fun monomorphize(P) = if P.isPoly(P) then P.makeMonomorphicInstance(P) else P
  in
                     let 
		         val P = monomorphize(P)
                         val _ = (doPrelude();
                                  TextIO.output(main_stream,"\nCHECKSAT ");				  
                                  (Prop.writeCVC(P,tables) handle Basic.Fail(msg) => primError(msg));
                                  TextIO.output(main_stream,";\n\nCOUNTERMODEL;\n"))
                         val _ = (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
                         val stream = TextIO.openAppend(yin0)
                         val _ = (TextIO.output(stream,readFile(yin1));TextIO.output(stream,"\n\n");TextIO.output(stream,readFile(yin2));TextIO.closeOut(stream))
                         val t2 = Time.toReal(Time.now())
                         val cmd_predix = if Paths.is_unix then Names.cvc4_binary else "cvcopt.exe "
                         val command = (case timeout_option of
                                           SOME(str) => cmd_predix ^ "--tlimit= " ^ str  ^ " --produce-models cvc0.cvc > cvco.ys 2> cvce.ys"
                                         | _ => cmd_predix ^ " --produce-models cvc0.cvc > cvco.ys 2> cvce.ys")
                         val _ = OS.Process.system(command)
                         val t3 = Time.toReal(Time.now())
                         val _ = debugPrint("\nCVC finished in "^(Real.toString(Real.-(t3,t2)))^" seconds...\n")
                         val smt_answer_stream = TextIO.openIn("cvco.ys")
                         val res = SMTOutput.processCVCOutput(smt_answer_stream,Prop.getConjuncts P,false,tables,ht_option)
			 val fsym_table_str = MS.tableToString(fsym_table,fn x => x)
                         val _ = (TextIO.closeIn(smt_answer_stream)) handle _ => ()
                      in
                          res 
                      end
  end

fun isWeightPair(v) = 
  (case v of
     listVal([v1,v2]) => isProp(v1) andalso (isNumeralValue(v2) orelse isMetaId(v2))
   | _ => false)

fun unZipPropsAndWeights(vals) =
  let fun loop([],res) = res
        | loop(listVal([v1,v2])::more,res as (props,weights)) = 
              (case (coerceValIntoProp(v1),coerceValIntoTerm(v2)) of
                  (SOME(P),SOME(t)) => (case AthTerm.getNumVal(t) of 
                                           SOME(A.int_num(i,_),_) => loop(more,(P::props,(Int.toString(i))::weights))
                                         | _ => (case AthTerm.isIdeConstant(t) of 
                                                    SOME(s) => if (s = "inf") then loop(more,(P::props,(""::weights)))
                                                               else primError("Wrong kind of term given as a Max-SMT weight for a sentence: " ^ 
                                                                              (AT.toStringDefault(t)))))
                | (SOME(_),NONE) => primError("Wrong kind of value given as a Max-SMT weight for a sentence: " ^ (prettyValToString v2))
                | (NONE,_) => primError("Wrong type of input given as the first element of a (sentence,weight) Max-SMT pair;\nthe first element must " ^
                                        " be a sentence but here it was this: " ^ (prettyValToString v1)))
   in
     loop(vals,([],[]))
   end

(****************** General SMT solving code: *****************)

fun smtGeneralSolvePrimBFun(v1,v2,env,_) = 
   (case v2 of
       tableVal(table) => let val (P,props,weight_strings) =
                                 (case coerceValIntoProp(v1) of
                                     SOME(prop) => (prop,[],[])
                                   | _ => (case v1 of
                                            listVal(vals) => 
                                              if (not(null(vals)) andalso isWeightPair(hd(vals))) then
                                                 let val (props,weight_strings) = unZipPropsAndWeights(vals)
                                                 in
                                                    (P.true_prop,props,weight_strings)
                                                 end
                                              else 
                                              let val props = Semantics.getProps(vals,"the argument list given to "^N.smtSolveFun_name,env)
                                                              in
                                                                (P.makeConjunction(props),[],[])
                                                              end
                                          | _ => primError(wrongArgKind(N.smtSolveFun_name,1,propLCType,v1))))
                              val solver = (case (HashTable.find table (termVal(AthTerm.makeIdeConstant("solver")))) of
                                               SOME(termVal(st)) => (case AT.isIdeConstant(st) of
                                                                        SOME(str) => str
                                                                      | _ => primError("Incorrect use of " ^ N.smtSolveFun_name ^ ": The 'solver field must have " ^
                                                                                       "a meta-identifier value in the options table."))
                                             | _ =>  primError("Incorrect use of " ^ N.smtSolveFun_name ^ ": The 'solver field must have " ^
                                                                                       "a meta-identifier value in the options table."))
                              val stats_option = (case (HashTable.find table (termVal(AthTerm.makeIdeConstant("stats")))) of
                                                     SOME(cv as cellVal(_)) => SOME(cv)
                                                   | _ => NONE)
                              val result_table_option = (case (HashTable.find table (termVal(AthTerm.makeIdeConstant("results")))) of
                                                            NONE => NONE
                                                          | SOME(tableVal(T)) => (SOME(T)))
                              val timeout_option = (case (HashTable.find table (termVal(AthTerm.makeIdeConstant("timeout")))) of
                                                            NONE => NONE
                                                          | SOME(termVal(t)) => (case AthTerm.getNumVal(t) of
                                                                                    SOME(A.int_num(i,_),_) => SOME(Int.toString(i))
                                                                                  | _ => primError("Incorrect use of " ^ N.smtSolveFun_name ^ ": The 'timeout field must have " ^
                                                                                                   "a numeric value in the options table."))
                                                          | SOME(v) => (case isStringValConstructive(v) of
                                                                           SOME(str) => SOME(str)
                                                                         | _ => primError("Incorrect use of " ^ N.smtSolveFun_name ^ ": The 'timeout field must have " ^
                                                                                          "a numeric value in the options table.")))
                          in
                             (case solver of
                                 "yices" => yicesSolve(P,props,weight_strings,timeout_option,result_table_option,stats_option)
                               | "cvc" =>   cvcSolveGeneric(P,timeout_option,result_table_option)
                               | _ => primError("Incorrect use of " ^ N.smtSolveFun_name ^ ": Unrecognized solver: " ^ solver))
                          end
     | _ => primError(wrongArgKind(N.smtSolveFun_name,2,tableLCType,v2)))
     
fun strucValEqFun([v1,v2],env,{pos_ar,file}) = 
      MLBoolToAth(strucValEq(v1,v2))    
  | strucValEqFun(args,_,{pos_ar,file}) = evError(wrongArgNumber(N.struc_eq_name,length(args),2),getPosOpt(pos_ar,0))

fun valEqFun([v1,v2],_,{pos_ar,file}) = MLBoolToAth(valEq(v1,v2))
  | valEqFun(args,_,{pos_ar,file}) = evError(wrongArgNumber(N.eq_name,length(args),2),getPosOpt(pos_ar,0))

fun valEqPrimBFun(v1,v2,_,_) = MLBoolToAth(valEq(v1,v2))

fun strucValEqPrimBFun(v1,v2,env,_) = MLBoolToAth(strucValEq(v1,v2)) 

fun isPrintableFun([charVal(i)],_,_) = if (i > 32) andalso (i < 128) then true_val else false_val
  | isPrintableFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.isPrintableFun_name,1,charLCType,v),
                                                  getPosOpt(pos_ar,2))
  | isPrintableFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.isPrintableFun_name,length(vals),1),
                                                   getPosOpt(pos_ar,0))

fun isPrintablePrimUFun(charVal(i),_,_) = if (i > 32) andalso (i < 128) then true_val else false_val
  | isPrintablePrimUFun(v,_,_) = primError(wrongArgKind(N.isPrintableFun_name,1,charLCType,v))

fun translateOntologyPrimUFun(v,env,_) = 
      (case isStringValConstructive(v) of
          SOME(str) => let val cmd = "python owl2Athena.py " ^ str 
                           val _ = ((OS.Process.system cmd)
                                      handle _ => primError("\nTranslation failed. Make sure that Python (3.0 or later) is installed\n"^
                                                            "and that the file " ^ str ^ " contains a valid (OWL 2 or higher) ontology.\n"))
                           val _ = print("\nOutput written into " ^ str ^ ".ath\n")
                       in
                         unitVal
                       end
        | _ => primError(wrongArgKind(N.transOntologyFun_name,1,stringLCType,v)))

fun propFun([v:value],(env,ab),{pos_ar,file}) = 
      (case coerceValIntoProp(v) of
          SOME(P) => propVal(P)
        | _ => evError(wrongArgKind(N.propFun_name,1,termLCType^" or "^propLCType,v),getPosOpt(pos_ar,2)))
  | propFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.propFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun propPrimUFun(v,env,_) = 
      (case coerceValIntoProp(v) of
          SOME(P) => propVal(P)
        | _ => primError(wrongArgKind(N.propFun_name,1,termLCType^" or "^propLCType,v)))

fun sortOfFun([v],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => let val mgot = AT.getSort(t) 
                    in
                       MLStringToAthString(F.toStringDefault(mgot))
                    end
       | _ => evError(wrongArgKind(N.sort_of_name,1,termLCType,v),SOME(Array.sub(pos_ar,2))))
  | sortOfFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.sort_of_name,length(vals),1),
                                              SOME(Array.sub(pos_ar,0)))
					      
fun sortOfPrimUFun(v,env,ab) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => let val mgot = AT.getSort(t) 
                    in
                       MLStringToAthString(F.toStringDefault(mgot))
                    end
       | _ => primError(wrongArgKind(N.sort_of_name,1,termLCType,v)))

fun sortOfVarInTermFun([v1,v2],(env,ab),{pos_ar,file}) = 
     (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
         (SOME(t1),SOME(t2)) => 
            (case AT.isVarOpt(t1) of
                SOME(v) => let val obt = ATV.getSort(v) 
                           in
                              MLStringToAthString(F.toPrettyString(0,obt,F.makeVarSortPrinter()))
                           end
              | _ => evError(wrongArgKind(N.sort_of_var_in_term_name,1,varLCType,v1),SOME(Array.sub(pos_ar,2))))
        | (SOME(_),_) => evError(wrongArgKind(N.sort_of_var_in_term_name,2,termLCType,v2),SOME(Array.sub(pos_ar,3)))
        | (NONE,_) => evError(wrongArgKind(N.sort_of_var_in_term_name,1,varLCType,v1),SOME(Array.sub(pos_ar,2))))
  | sortOfVarInTermFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.sort_of_var_in_term_name,length(vals),2),
                                                 SOME(Array.sub(pos_ar,0)))

fun sortOfVarInTermPrimBFun(v1,v2,env,_) = 
     (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
         (SOME(t1),SOME(t2)) => 
            (case AT.isVarOpt(t1) of
                SOME(v) => let val obt = ATV.getSort(v) 
                           in
                              MLStringToAthString(F.toPrettyString(0,obt,F.makeVarSortPrinter()))
                           end
              | _ => primError(wrongArgKind(N.sort_of_var_in_term_name,1,varLCType,v1)))
        | (SOME(_),_) => primError(wrongArgKind(N.sort_of_var_in_term_name,2,termLCType,v2))
        | (NONE,_) => primError(wrongArgKind(N.sort_of_var_in_term_name,1,varLCType,v1)))

fun sortOfVarInPropFun([v1,v2],(env,ab),{pos_ar,file}) = 
     (case (coerceValIntoTerm(v1),coerceValIntoProp(v2)) of
         (SOME(t1),SOME(P)) => 
            (case AT.isVarOpt(t1) of
                SOME(v) => let val obt = ATV.getSort(v) 
                           in
                              MLStringToAthString(F.toPrettyString(0,obt,F.makeVarSortPrinter()))
                           end
              | _ => evError(wrongArgKind(N.sort_of_var_in_prop_name,1,varLCType,v1),
			     SOME(Array.sub(pos_ar,2))))
        | (SOME(_),_) => evError(wrongArgKind(N.sort_of_var_in_prop_name,2,termLCType,v2),SOME(Array.sub(pos_ar,3)))
        | (NONE,_) => evError(wrongArgKind(N.sort_of_var_in_prop_name,1,varLCType,v1),SOME(Array.sub(pos_ar,2))))
  | sortOfVarInPropFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.sort_of_var_in_prop_name,length(vals),2),
                                                 SOME(Array.sub(pos_ar,0)))


fun sortOfVarInPropPrimBFun(v1,v2,env,_) = 
     (case (coerceValIntoTerm(v1),coerceValIntoProp(v2)) of
         (SOME(t1),SOME(P)) => 
            (case AT.isVarOpt(t1) of
                SOME(v) => let val obt = ATV.getSort(v) 
                           in
                              MLStringToAthString(F.toPrettyString(0,obt,F.makeVarSortPrinter()))
                           end
              | _ => primError(wrongArgKind(N.sort_of_var_in_prop_name,1,varLCType,v1)))
        | (SOME(_),_) => primError(wrongArgKind(N.sort_of_var_in_prop_name,2,termLCType,v2))
        | (NONE,_) => primError(wrongArgKind(N.sort_of_var_in_prop_name,1,varLCType,v1)))

fun rootFun([v],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => (case isGeneralApp(t) of
                        SOME(fsym,_) => termConVal(fsym)
                      | _ => (case AT.isVarOpt(t) of 
                                 SOME(_) => termVal(t)
                               | _ => evError(wrongArgKind(N.root_name,1,termLCType^" or "^propLCType,v),
                                              SOME(Array.sub(pos_ar,2)))))
       | _ => (case coerceValIntoProp(v) of
		  SOME(P) => (case P.isAtom(P) of
				 SOME(t) => rootFun([termVal(t)],(env,ab),{pos_ar=pos_ar,file=file})
			       | _ => (case P.isCompound(P) of
					 SOME(prop_con,_) => propConVal(prop_con)
				       | _ => evError(wrongArgKind(N.root_name,1,termLCType^" or "^propLCType,v),
	                                              SOME(Array.sub(pos_ar,2)))))
               | _ => evError(wrongArgKind(N.root_name,1,termLCType^" or "^propLCType,v),
	                                              SOME(Array.sub(pos_ar,2)))))
  | rootFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.root_name,length(vals),1),
                                            SOME(Array.sub(pos_ar,0)))


fun getAlphaCertFun(v1,v2,env,ab) = 
  (case (v1,v2) of 
     (closMethodVal(A.methodExp({params=[],body,pos,name}),env_ref),
      closUFunVal(continuation_body,parameter,close_env,{name=cont_name,prec,...})) => 
         let val (method_res,ded_info as {proof,conc,fa,...}) = Alpha.evalDedAlpha(body,env_ref,ab)
             val _ = Basic.mark("3")
             val proof_str = Alpha.certToString(proof)
             val _ = Basic.mark("4")
             val proof_ath_str = MLStringToAthString(proof_str)
             val _ = Basic.mark("5")
             val res = evalClosure(v2,[proof_ath_str],ab,NONE)
         in
            res 
         end
   | (v1,closUFunVal(_)) => primError(wrongArgKind(N.getAlphaCertFun_name,1,closMethodLCType,v1))
   | (_,v2) => primError(wrongArgKind(N.getAlphaCertFun_name,2,closUFunType,v2)))

fun mergeSortPrimBFun(v1,v2,env,ab) =  
      (case v1 of 
          listVal(vals) =>
            (case v2 of
                primBFunVal(f,_) => let fun compare(x,y) = (case f(x,y,env,ab) of
                                                               termVal(t) => AT.isTrueTerm(t)
                                                             | _ => false)
                                    in
                                      listVal(Basic.mergeSortBuiltIn(vals,compare))
                                    end
              | closBFunVal(body,p1,p2,clos_env as ref(valEnv({val_map,mod_map,...})),_) => 
                       let fun compare(v1,v2) = 
                                 let val vm = Symbol.enter(Symbol.enter(val_map,p1,v1),p2,v2)
                                 in
                                    (case evalExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab) of
                                        termVal(t) => AT.isTrueTerm(t)
                                      | _ => primError("The comparison procedure given to " ^ N.built_in_merge_sort_name ^
                                                       "\nproduced a result of wrong type"))
                                 end
                        in
                           listVal(Basic.mergeSortBuiltIn(vals,compare))
                        end))
			
fun mergeSortPrimBFun'(v1,v2,env,ab) =  
      (case v1 of 
          listVal(vals) =>
            (case v2 of
                primBFunVal(f,_) => let fun compare(x,y) = (case f(x,y,env,ab) of
                                                               termVal(t) => AT.isFalseTerm(t)
                                                             | _ => true)
                                    in
                                      listVal(Basic.mergeSortBuiltIn(vals,compare))
                                    end
              | closBFunVal(body,p1,p2,clos_env as ref(valEnv({val_map,mod_map,...})),_) => 
                       let fun compare(v1,v2) = 
                                 let val vm = Symbol.enter(Symbol.enter(val_map,p1,v1),p2,v2)
                                 in
                                    (case evalExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab) of
                                        termVal(t) => AT.isFalseTerm(t)
                                      | _ => primError("The comparison procedure given to " ^ N.built_in_merge_sort_name ^
                                                       "\nproduced a result of wrong type"))
                                 end
                        in
                           listVal(Basic.mergeSortBuiltIn(vals,compare))
                        end))
 

fun unparseFun([closMethodVal(A.methodExp({params=[],body,pos,name}),env_ref)],env,ab) = 
      let val proof_str = A.unparseDed(body)
      in
         MLStringToAthString(proof_str)
      end
  | unparseFun([v],_,{pos_ar,file}) = primError(wrongArgKind(N.unparseFun_name,1,closMethodLCType,v))
  | unparseFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.unparseFun_name,length(vals),1),SOME(Array.sub(pos_ar,0)))
                                              

fun unparsePrimUFun(v,env,ab) = 
   (case v of
       closUFunVal(e,_,_,{name,...}) => 
              MLStringToAthString("Unary procedure: " ^ (!name) ^ (A.unparseExp(e)))
    | closBFunVal(e,_,_,_,{name,...}) => 
              MLStringToAthString("Binary procedure: " ^ (!name) ^ (A.unparseExp(e)))
    | closFunVal(e,_,{name,...}) => 
              MLStringToAthString("Procedure: " ^ (!name) ^ (A.unparseExp(e)))
    | closUMethodVal(d,_,_,name) => 
          let val conc = Simplify_New.proofConclusion(d,ab)
              val _ = print("\nCONCLUSION:\n" ^ (Prop.toPrettyStringDefault(0,conc)) ^ "\n")
          in
              MLStringToAthString("Unary method: " ^ (!name) ^ (A.unparseDed(d)))
          end
    | closBMethodVal(d,_,_,_,name) => 
              MLStringToAthString("Binary method: " ^ (!name) ^ (A.unparseDed(d)))
    | closMethodVal(e as A.methodExp({body,...}),_) => 
          let val conc = Simplify_New.proofConclusion(body,ab) 
              val _ = print("\nCONCLUSION:\n" ^ (Prop.toPrettyStringDefault(0,conc)) ^ "\n")
              val _ = print("\nABOUT TO COMPUTE FREE ASSUMPTIONS...\n")
              val fas = Simplify_New.FA(body,ab)
              val _ = print("\n[[[[[[[ FREE ASSUMPTIONS:\n\n" ^ (Basic.printListStr(fas,fn p => Prop.toPrettyStringDefault(0,p),"\n")) ^ "\n\n]]]]]]]\n")
          in
              MLStringToAthString("Method: " ^ (A.unparseExp(e)))
          end
    | _ =>  primError(wrongArgKind(N.unparseFun_name,1,functionLCType,v)))

fun unparsePlainPrimUFun(v,env,ab) = 
   (case v of
       closUFunVal(e,_,_,{name,...}) => 
              MLStringToAthString("Unary procedure: " ^ (!name) ^ (A.unparseExp(e)))
    | closBFunVal(e,_,_,_,{name,...}) => 
              MLStringToAthString("Binary procedure: " ^ (!name) ^ (A.unparseExp(e)))
    | closFunVal(e,_,{name,...}) => 
              MLStringToAthString("Procedure: " ^ (!name) ^ (A.unparseExp(e)))
    | closUMethodVal(d,_,_,name) => 
              MLStringToAthString("Unary method: " ^ (!name) ^ (A.unparseDed(d)))
    | closBMethodVal(d,_,_,_,name) => 
              MLStringToAthString("Binary method: " ^ (!name) ^ (A.unparseDed(d)))
    | closMethodVal(e as A.methodExp({body,...}),_) => 
              MLStringToAthString("Method: " ^ (A.unparseExp(e)))
    | _ =>  primError(wrongArgKind(N.unparseFun_name,1,functionLCType,v)))

fun rootPrimUFun(v,env,ab) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => (case isGeneralApp(t) of
                        SOME(fsym,_) => termConVal(fsym)
                      | _ => (case AT.isVarOpt(t) of 
                                 SOME(_) => termVal(t)
                               | _ => primError(wrongArgKind(N.root_name,1,termLCType^" or "^propLCType,v))))
       | _ => (case coerceValIntoProp(v) of
		  SOME(P) => (case P.isAtom(P) of
				 SOME(t) => rootPrimUFun(termVal(t),env,ab)
			       | _ => (case P.isCompound(P) of
					 SOME(prop_con,_) => propConVal(prop_con)
				       | _ => primError(wrongArgKind(N.root_name,1,termLCType^" or "^propLCType,v))))
               | _ => primError(wrongArgKind(N.root_name,1,termLCType^" or "^propLCType,v))))

fun isAtomFun([v],(env,ab),_) = 
      (case coerceValIntoProp(v) of
          SOME(P) => (case P.isAtom(P) of SOME(_) => true_val | _ => false_val)
        | _ => false_val)
  | isAtomFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.is_atom_name,length(vals),1),
                                              SOME(Array.sub(pos_ar,0)))

fun isAtomPrimUFun(v,env,ab) = 
      (case coerceValIntoProp(v) of
          SOME(P) => (case P.isAtom(P) of SOME(_) => true_val | _ => false_val)
        | _ => false_val)

fun isDirPrimUFun(v,env,ab) = 
      (case isStringValConstructive(v) of
          SOME(str) => MLBoolToAth(Basic.isDir(str))
        | _ => false_val)


fun isAssertionFun([v],(env,ab),_) = 
      (case coerceValIntoProp(v) of
          SOME(p) => MLBoolToAth(ABase.isAssertion(p,ab))
        | _ => false_val)
  | isAssertionFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.is_assertion_name,length(vals),1),
                                              SOME(Array.sub(pos_ar,0)))

fun isAssertionPrimUFun(v,env,ab) = 
      (case coerceValIntoProp(v) of
          SOME(p) => MLBoolToAth(ABase.isAssertion(p,ab))
        | _ => false_val)

fun isConstructorFun([v],(env,ab),_) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => MLBoolToAth(StructureAnalysis.isStructureConstructorBool(D.fsymName(some_fsym)))
          | _ => MLBoolToAth(false))
  | isConstructorFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.is_constructor_name,length(vals),1),
                                              SOME(Array.sub(pos_ar,0)))

fun isConstructorPrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => MLBoolToAth(Data.isStructureConstructorBool(D.fsymName(some_fsym)))
          | _ => MLBoolToAth(false))

fun isFreeConstructorPrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => MLBoolToAth(Data.isFreeStructureConstructor(D.fsymName(some_fsym)))
          | _ => MLBoolToAth(false))

fun symCodePrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val name = fsymName(some_fsym)
                                        in
                                           termVal(AthTerm.makeNumTerm(A.int_num(MS.code(name),ref "")))
                                        end
          | _ => primError(wrongArgKind(N.symCodeFun_name,1,termConLCType,v)))

fun tcFun([v],(env,ab),_) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)                      
                                            val tc_syms = MS.listModSymbols(Prop.tc'(fname))
                                            fun makeTCV(name) = (case Data.isTermConstructorAsFSymOption(name) of
                                                                    SOME(fsym) => termConVal(regFSym(fsym))
                                                                  | _ => raise Basic.Never)
                                        in 
                                          listVal(map makeTCV tc_syms)
                                        end)
					
fun tcPrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)                      
                                            val tc_syms = MS.listModSymbols(Prop.tc'(fname))
                                            fun makeTCV(name) = (case Data.isTermConstructorAsFSymOption(name) of
                                                                    SOME(fsym) => termConVal(regFSym(fsym))
                                                                  | _ => raise Basic.Never)
                                        in 
                                          listVal(map makeTCV tc_syms)
                                        end)

fun getEvalProcName(f,env) = 
  (case MS.find(Prop.fsym_def_table,f) of
      SOME({eval_proc_name,...}) => eval_proc_name 
    | _ => let val res = (MS.name f)^"'" 		    
               val res' = Semantics.nextAvailableEvalProcName(Symbol.name(MS.lastName f),env,NONE)
           in 
              res'
           end)

fun getReduceProcName(f,env) = 
  (case MS.find(Prop.fsym_def_table,f) of
      SOME({eval_proc_name,...}) => eval_proc_name^(Names.standardReduceProcNameTailString)
    | _ => let val res = (MS.name f)^"'" 
               val res' = Semantics.nextAvailableEvalProcName(Symbol.name(MS.lastName f),env,NONE)
           in 
              res'^(Names.standardReduceProcNameTailString)
           end)

fun getEvalProcName1(f,env) = 
  (case MS.find(Prop.fsym_def_table,f) of
      SOME({eval_proc_name_with_full_mod_path,...}) => eval_proc_name_with_full_mod_path
    | _ => let val res = (MS.name f)^"'"
               val res' = Semantics.nextAvailableEvalProcName(Symbol.name(MS.lastName f),env,NONE)
           in
              res'
           end)
	   
fun evalProcNameFun([v],(env,ab),{pos_ar,file}) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)
                                        in 
                                          MLStringToAthString(getEvalProcName(fname,env))
                                        end
          | _ => evError(wrongArgKind("get-eval-proc-name",1,termConLCType,v),SOME(Array.sub(pos_ar,2))))
  | evalProcNameFun(vals,(env,ab),{pos_ar,file}) = 
          evError(wrongArgNumber("get-eval-proc-name",length(vals),1),SOME(Array.sub(pos_ar,0)))

fun evalProcNamePrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)
                                        in 
                                          MLStringToAthString(getEvalProcName(fname,env))
                                        end
          | _ => primError(wrongArgKind("get-eval-proc-name",1,termConLCType,v)))

fun evalProcName1Fun([v],(env,ab),{pos_ar,file}) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)
                                        in 
                                          MLStringToAthString(getEvalProcName1(fname,env))
                                        end
          | _ => evError(wrongArgKind("get-eval-proc-name-1",1,termConLCType,v),SOME(Array.sub(pos_ar,2))))
  | evalProcName1Fun(vals,(env,ab),{pos_ar,file}) = 
          evError(wrongArgNumber("get-eval-proc-name-1",length(vals),1),SOME(Array.sub(pos_ar,0)))

fun evalProcName1PrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)
                                        in 
                                          MLStringToAthString(getEvalProcName1(fname,env))
                                        end
          | _ => primError(wrongArgKind("get-eval-proc-name-1",1,termConLCType,v)))
                            
fun defEqnsPrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)
                                        in 
                                           (case MS.find(Prop.fsym_def_table,fname) of
                                               SOME({defining_equations=eqns,...}) => 
					         let 
                                                 in
                                                    listVal(map propVal eqns)
                                                 end
                                             | _ => (let in listVal([]) end))
                                        end
          | _ => primError(wrongArgKind(N.defEqnsFun_name,1,termConLCType,v)))
            
fun getFunDefInfoPrimUFun(v,env,ab) = 
        (case coerceValIntoTermCon(v) of 
            SOME(regFSym(some_fsym)) => let val fname = Data.fsymName(some_fsym)
                                        in
                                          (case MS.find(Prop.fsym_def_table,fname) of
                                             SOME({eval_proc_name,guard_syms,occurring_syms,defining_equations,obsolete_axioms,needed_by,code,red_code,dcode,bicond_sources,...}) => 
                                                               let val tc_sym_names  = (map MS.name occurring_syms)
								   fun idVal(str) = termVal(AT.makeIdeConstant(str))
							           val pair_1 = (idVal("eval-proc-name"),MLStringToAthString(eval_proc_name))
                                                                   val pair_2 = (idVal("guard-syms"),listVal(map MLStringToAthString (map MS.name guard_syms)))
                                                                   val pair_3 = (idVal("occurring-syms"),listVal(map MLStringToAthString (map MS.name occurring_syms)))
								   val pair_4 = (idVal("defining-equations"),listVal(map propVal defining_equations))
								   val pair_5 = (idVal("code"),MLStringToAthString(!code))
								   val pair_7 = (idVal("deduction-code"),MLStringToAthString(!dcode))
								   val pair_8 = (idVal("red-code"),MLStringToAthString(!red_code))
								   val pair_9 = (idVal("needed-by-syms"),listVal(map MLStringToAthString (map MS.name needed_by)))
								   val pair_10 = (idVal("obsolete-axioms"),listVal(map propVal obsolete_axioms))
								   val pair_12 = (idVal("bicond-axiom-sources"),listVal(map (fn (p1,p2) => listVal([propVal(p1),propVal(p2)])) 
								                                                            bicond_sources))
                                                               in
                                                                 SV.makeValMapping([pair_1,pair_2,pair_3,pair_4,pair_5,pair_7,pair_8,pair_9,pair_10,pair_12])
                                                               end
                                           | _ =>  unitVal)
                                        end
         | _ => let val _ = print("\nNot a reg fsym...\n") in unitVal end)

fun isCanonicalFun([termVal(t)],(env,ab),_) =  MLBoolToAth(AT.isCanonical(t))

fun isCanonicalPrimUFun(termVal(t),env,ab) =  MLBoolToAth(AT.isCanonical(t))

fun childrenFun([v],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => (case isGeneralApp(t) of
                        SOME(fsym,args) => listVal(map termVal args)
                      | _ => (case AT.isVarOpt(t) of 
                                 SOME(var) => listVal([])
                               | _ => evError(wrongArgKind(N.children_name,1,termLCType^" or "^propLCType,v),
                                              SOME(Array.sub(pos_ar,2)))))
       | _ => (case coerceValIntoProp(v) of
                 SOME(P) => (case P.isAtom(P) of
			        SOME(t) => childrenFun([termVal(t)],(env,ab),{pos_ar=pos_ar,file=file})
 		              | _ => (case P.isQuant(P) of 
				         SOME(_,v,Q) => listVal([termVal(AthTerm.makeVar(v)),propVal(Q)])
				       | _ => (case P.isCompound(P) of
				 	          SOME(_,props) => listVal(List.map propVal props)
                                                | _ => raise Basic.Never)))
               | _ => evError(wrongArgKind(N.children_name,1,termLCType^" or "^propLCType,v),
                                           SOME(Array.sub(pos_ar,2)))))
  | childrenFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.children_name,length(vals),1),
                                                SOME(Array.sub(pos_ar,0)))

fun childrenPrimUFun(v,env,ab) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => (case isGeneralApp(t) of
                        SOME(fsym,args) => listVal(map termVal args)
                      | _ => (case AT.isVarOpt(t) of 
                                 SOME(var) => listVal([])
                               | _ => primError(wrongArgKind(N.children_name,1,termLCType^" or "^propLCType,v))))
       | _ => (case coerceValIntoProp(v) of
                 SOME(P) => (case P.isAtom(P) of
			        SOME(t) => childrenPrimUFun(termVal(t),env,ab)
 		              | _ => (case P.isQuant(P) of 
				         SOME(_,v,Q) => listVal([termVal(AthTerm.makeVar(v)),propVal(Q)])
				       | _ => (case P.isCompound(P) of
				 	          SOME(_,props) => listVal(List.map propVal props)
                                                | _ => raise Basic.Never)))
               | _ => primError(wrongArgKind(N.children_name,1,termLCType^" or "^propLCType,v))))

exception TermHashTable

fun makeTermHTPrimUFun(val_arg,env,ab) = 
  let val sizeHint = getHTSizeHint(val_arg)
      val ht: (AT.term,Semantics.value) HashTable.hash_table = HashTable.mkTable(AT.hashTerm, AT.termEq) (sizeHint,TermHashTable)
      fun dispatch(v,env,ab) =
            (case isStringValConstructive(v) of
                SOME("look-up") => 
                   let fun lookUp(v,env,ab) = 
                            (case coerceValIntoTerm(v) of 
                                SOME(t) => (case (HashTable.find ht t) of 
                                                 SOME(v) => v
                                               | _ => unitVal)
                              | _ => primError(wrongArgKind(N.TermHT_lookup_name,1,termLCType,v)))
                   in
                     primUFunVal(lookUp,default_ufv_pa N.TermHT_lookup_name)
                   end
             | SOME("enter") => 
                   let fun enter(v,key_val,env,ab) = 
                            (case coerceValIntoTerm(v) of  
                                SOME(t) => (HashTable.insert ht (t,key_val);key_val)
                              | _ => primError(wrongArgKind(N.TermHT_enter_name,2,termLCType,v)))
                   in 
                     primBFunVal(enter,default_bfv_pa N.TermHT_enter_name)
                   end
             | SOME("remove") => 
                   let fun remove(v,env,ab) = 
                            (case coerceValIntoTerm(v) of  
                                SOME(t) => ((HashTable.remove ht t) handle _ => unitVal;unitVal)
                              | _ => primError(wrongArgKind(N.TermHT_remove_name,2,termLCType,v)))
                   in 
                      primUFunVal(remove,default_ufv_pa N.TermHT_remove_name)
                   end
             | SOME("clear") => 
                   let fun clear([],env,ab) = (HashTable.clear(ht);unitVal)
                         | clear(vals,_,_) = primError(wrongArgNumber(N.TermHT_clear_name,length(vals),0))
                   in 
                      funVal(clear,N.TermHT_clear_name,default_fv_pa 1)
                   end
             | SOME("size") => 
                   let fun size([],env,ab) = 
                            let val i = HashTable.numItems(ht)
                                val str = Int.toString i
                                 in termVal(AthTerm.makeNumTerm(A.int_num(i,ref "")))
                                 end
                         | size(vals,_,_) = primError(wrongArgNumber(N.TermHT_size_name,length(vals),1))
                   in 
                      funVal(size,N.TermHT_size_name,default_fv_pa 0)
                   end
             | SOME("show") => 
                   let fun show([],env,ab) = 
                          let val list_of_pairs = HashTable.listItemsi(ht)
                              val list_of_lists = map (fn (t:AT.term,b:value) => 
                                                            listVal([(termVal t),b]))
                                                      list_of_pairs
                          in
                             listVal(list_of_lists)
                          end
                         | show(vals,_,_) = primError(wrongArgNumber(N.TermHT_show_name,length(vals),1))
                   in 
                      funVal(show,N.TermHT_show_name,default_fv_pa 0)
                   end)
  in
     primUFunVal(dispatch,default_ufv_pa N.makeTermHTFun_name)
  end

fun makeHTPrimUFun(val_arg,env,ab) = 
  let val size_hint = getHTSizeHint(val_arg)
      val ht = Symbol.makeHTableWithInitialSize(size_hint)
      fun dispatch(v,env,ab) = 
            (case isStringValConstructive(v) of
                SOME("look-up") => 
                   let fun lookUp(v,env,ab) = 
                            (case isStringValConstructive(v) of  
                                SOME(str) => (case Symbol.find(ht,Symbol.symbol(str)) of 
                                                 SOME(v) => v
                                               | _ => unitVal)
                              | _ => primError(wrongArgKind(N.HT_lookup_name,1,stringLCType,v)))
                   in
                     primUFunVal(lookUp,default_ufv_pa N.HT_lookup_name)
                   end
             | SOME("remove") => 
                   let fun remove(v,env,ab) = 
                            (case isStringValConstructive(v) of 
                                SOME(str) => let val sym = Symbol.symbol(str)
                                                 val res = (Symbol.removeHT(ht,sym)) handle _ => unitVal
                                             in 
                                                unitVal
                                             end
                              | _ => primError(wrongArgKind(N.HT_remove_name,2,stringLCType,v)))
                   in 
                      primUFunVal(remove,default_ufv_pa N.HT_remove_name)
                   end
             | SOME("clear") => 
                   let fun clear([],env,ab) = (Symbol.clearHTable(ht);unitVal)
                         | clear(vals,_,_) = primError(wrongArgNumber(N.HT_clear_name,length(vals),0))
                   in 
                      funVal(clear,N.HT_clear_name,default_fv_pa 1)
                   end
             | SOME("enter") => 
                   let fun enter(v_str,key_val,env,ab) = 
                            (case isStringValConstructive(v_str) of  
                                SOME(str) => (Symbol.insert(ht,Symbol.symbol(str),key_val);key_val)
                              | _ => primError(wrongArgKind(N.HT_enter_name,2,stringLCType,v_str)))
                   in 
                      primBFunVal(enter,default_bfv_pa N.HT_enter_name)
                   end
             | SOME("size") => 
                   let fun size([],env,ab) = 
                           let val i = Symbol.numItems(ht) 
                               val str = Int.toString(i)
                           in termVal(AthTerm.makeNumTerm(A.int_num(i,ref "")))
                           end
                         | size(vals,_,_) = primError(wrongArgNumber(N.HT_size_name,length(vals),1))
                   in 
                      funVal(size,N.HT_size_name,default_fv_pa 0)
                   end
             | SOME("show") => 
                   let fun show([],env,ab) = 
                          let val list_of_pairs = Symbol.listItemsi(ht)
                              val list_of_lists = map (fn (a:Symbol.symbol,b:value) => 
                                                            listVal([MLStringToAthString(Symbol.name(a)),b]))
                                                      list_of_pairs
                          in
                             listVal(list_of_lists)
                          end
                         | show(vals,_,_) = primError(wrongArgNumber(N.HT_show_name,length(vals),1))
                   in 
                      funVal(show,N.HT_show_name,default_fv_pa 0)
                   end)
  in
     primUFunVal(dispatch,default_ufv_pa N.HT_dispatch_name)
  end

fun arityOfFun([v],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) =>
                  let val arity = D.fsymArity(some_fsym)
                  in termVal(AthTerm.makeNumTerm(A.int_num(arity,ref "")))
                  end
          | SOME(_) => termVal(AthTerm.makeNumTerm(A.int_num(0,ref "")))
          | _ => (case v of  
                     closFunVal(A.functionExp({params,...}),_,_) => 
                       let val arity = length(params)
                       in
                          termVal(AthTerm.makeNumTerm(A.int_num(arity,ref "")))
                       end
                   | closUFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(1,ref "")))
                   | closBFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(2,ref "")))
                   | primUFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(1,ref "")))
                   | primBFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(2,ref "")))
                   | funVal(_,_,{arity,...}) => termVal(AthTerm.makeNumTerm(A.int_num(arity,ref "")))
                   | _ =>  evError(wrongArgKind(N.arityOf_name,1,termConLCType,v),getPosOpt(pos_ar,2))))
  | arityOfFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.arityOf_name,length(vals),1),
                                               SOME(Array.sub(pos_ar,0)))

fun arityOfPrimUFun(v,env,ab) = 
     (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) =>
                  let val arity = D.fsymArity(some_fsym)
                  in termVal(AthTerm.makeNumTerm(A.int_num(arity,ref "")))
                  end
          | SOME(_) => termVal(AthTerm.makeNumTerm(A.int_num(0,ref "")))
          | _ => (case v of  
                     closFunVal(A.functionExp({params,...}),_,_) => 
                       let val arity = length(params)
                       in
                          termVal(AthTerm.makeNumTerm(A.int_num(arity,ref "")))
                       end
                   | closUFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(1,ref "")))
                   | closBFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(2,ref "")))
                   | primUFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(1,ref "")))
                   | primBFunVal(_) => termVal(AthTerm.makeNumTerm(A.int_num(2,ref "")))
                   | funVal(_,_,{arity,...}) => termVal(AthTerm.makeNumTerm(A.int_num(arity,ref "")))
                   | _ =>  primError(wrongArgKind(N.arityOf_name,1,termConLCType,v))))

fun precedenceOfFun([v],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) => 
                  let val prec = (!(D.fsymPrec(some_fsym)))
                  in
                     termVal(AthTerm.makeNumTerm(A.int_num(prec,ref "")))
                  end
          | _ => (case v of  
                     primUFunVal(_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | primBFunVal(_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | closUFunVal(_,_,_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | closBFunVal(_,_,_,_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | closFunVal(A.functionExp({params,...}),_,{prec,assoc,...}) => 
                       termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | funVal(_,_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | propConVal(A.notCon) => let val p = !(#prec(A.not_con_passoc))
                                             in termVal(AthTerm.makeNumTerm(A.int_num(p, ref "")))
                                             end 
                   | propConVal(A.andCon) => let val p = !(#prec(A.and_con_passoc))
                                             in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                             end 
                   | propConVal(A.orCon) => let val p = !(#prec(A.or_con_passoc))
                                            in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                            end 
                   | propConVal(A.ifCon) => let val p = !(#prec(A.if_con_passoc))
                                            in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                            end 
                   | propConVal(A.iffCon) => let val p = !(#prec(A.iff_con_passoc))
                                             in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                             end 
                   | _ => evError(wrongArgKind(N.getPrecedence_name,1,termConLCType,v),getPosOpt(pos_ar,2))))
  | precedenceOfFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.getPrecedence_name,length(vals),1),
                                               SOME(Array.sub(pos_ar,0)))

fun precedenceOfPrimUFun(v,env,ab) = 
     (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) => 
                  let val prec = (!(D.fsymPrec(some_fsym)))
                  in
                     termVal(AthTerm.makeNumTerm(A.int_num(prec,ref "")))
                  end
          | _ => (case v of  
                     primUFunVal(_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | primBFunVal(_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | closUFunVal(_,_,_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | closBFunVal(_,_,_,_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | closFunVal(A.functionExp({params,...}),_,{prec,assoc,...}) => 
                       termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))
                   | funVal(_,_,{prec,...}) => termVal(AthTerm.makeNumTerm(A.int_num(!prec,ref "")))

                   | propConVal(A.notCon) => let val p = !(#prec(A.not_con_passoc))
                                             in termVal(AthTerm.makeNumTerm(A.int_num(p, ref "")))
                                             end 
                   | propConVal(A.andCon) => let val p = !(#prec(A.and_con_passoc))
                                             in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                             end 
                   | propConVal(A.orCon) => let val p = !(#prec(A.or_con_passoc))
                                            in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                            end 
                   | propConVal(A.ifCon) => let val p = !(#prec(A.if_con_passoc))
                                            in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                            end 
                   | propConVal(A.iffCon) => let val p = !(#prec(A.iff_con_passoc))
                                             in termVal(AthTerm.makeNumTerm(A.int_num(p,ref "")))
                                             end 
                   | _ => primError(wrongArgKind(N.getPrecedence_name,1,termConLCType,v))))

fun assocOfFun([v],(env,ab),{pos_ar,file}) = 
  let fun assocString(arity,str) = if not(arity = 2) then 
                                      evError("Non-binary procedures and function symbols have no associativity",
                                               SOME(Array.sub(pos_ar,2)))
                                   else MLStringToAthString(str)
  in
     (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) => (case D.fsymAssoc(some_fsym) of 
                                            ref(SOME(true)) => assocString(D.fsymArity(some_fsym),"left")
                                          | _ => assocString(D.fsymArity(some_fsym),"default (right)"))
          | _ => (case v of  
                     closFunVal(A.functionExp({params,...}),_,{prec,assoc=ref(SOME(true)),...}) => assocString(length params,"left")
                   | closFunVal(A.functionExp({params,...}),_,{prec,assoc=ref(_),...}) => assocString(length params,"default (right)")
                   | funVal(_,_,{arity,assoc=ref(SOME(true)),...}) => assocString(arity,"left")
                   | funVal(_,_,{arity,assoc=ref(_),...}) => assocString(arity,"default (right)")
                   | v => evError(wrongArgKind(N.getAssoc_name,1,termConLCType,v),getPosOpt(pos_ar,2))))
  end
  | assocOfFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.getAssoc_name,length(vals),1),
                                               SOME(Array.sub(pos_ar,0)))

fun assocOfPrimUFun(v,env,ab) = 
  let fun assocString(arity,str) = if not(arity = 2) then 
                                      primError("Non-binary procedures and function symbols have no associativity")
                                   else MLStringToAthString(str)
  in
     (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) => (case D.fsymAssoc(some_fsym) of 
                                            ref(SOME(true)) => assocString(D.fsymArity(some_fsym),"left")
                                          | _ => assocString(D.fsymArity(some_fsym),"default (right)"))
          | _ => (case v of  
                     closFunVal(A.functionExp({params,...}),_,{prec,assoc=ref(SOME(true)),...}) => assocString(length params,"left")
                   | closFunVal(A.functionExp({params,...}),_,{prec,assoc=ref(_),...}) => assocString(length params,"default (right)")
                   | closUFunVal(_) => assocString(1,"")
                   | closBFunVal(_,_,_,_,{assoc=ref(SOME(true)),...}) => assocString(2,"left")
                   | closBFunVal(_,_,_,_,{assoc=ref(_),...}) => assocString(2,"default (right)")
                   | funVal(_,_,{arity,assoc=ref(SOME(true)),...}) => assocString(arity,"left")
                   | funVal(_,_,{arity,assoc=ref(_),...}) => assocString(arity,"default (right)")
                   | primUFunVal(_) => assocString(1,"")
                   | primBFunVal(_,{assoc=ref(SOME(true)),...}) => assocString(2,"left")
                   | primBFunVal(_,{assoc=ref(_),...}) => assocString(2,"default (right)")
                   | v => primError(wrongArgKind(N.getAssoc_name,1,termConLCType,v))))
  end

fun moduleToStringPrimUFun(v,env,ab) = 
    (case isStringValConstructive(v) of
          SOME(str) => 
           let val msym = A.makeMS(str,NONE)
           in
            (case lookUpModule(!env,msym) of
               SOME(module:SV.module as {env as SV.valEnv({val_map=imported_val_map,mod_map=imported_mod_map}),...}) => 
                  let val e = SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.enter(Symbol.empty_mapping,Symbol.symbol str,module)})
                  in
                    MLStringToAthString(SV.envToString(e))
                  end
              | _ => if str = Names.top_module_name then 
                        let val (tv_map,tm_map) = getValAndModMaps(!top_val_env)
                            val tenv: SV.value_environment = !top_val_env
                            val tmod_name = ModSymbol.makeModSymbol([],Names.top_module_symbol,Names.top_module_symbol)
                            val tmod:SV.module = {env=tenv,mod_name=tmod_name,open_mod_directives=[]}
                            val e = SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.enter(Symbol.empty_mapping,Names.top_module_symbol,tmod)})
                        in
                           MLStringToAthString(SV.envToString(e))
                        end
                     else primError("Incorrect use of "^(N.moduleToStringFun_name)^": no module by the name of "^str^" is visible here"))
           end
        | _ => primError(wrongArgKind(N.moduleToStringFun_name,1,stringLCType,v)))

fun moduleToHTPrimUFun(v,_,ab) = 
  let val env = top_val_env_backup
  in
    (case isStringValConstructive(v) of
          SOME(str) => 
           let val msym = A.makeMS(str,NONE)
           in
            (case lookUpModule(!env,msym) of
               SOME(module:SV.module as {env as SV.valEnv({val_map=imported_val_map,mod_map=imported_mod_map}),...}) => 
                  let val e = SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.enter(Symbol.empty_mapping,Symbol.symbol str,module)})
		      val res = (case env2HTVal(e) of
                                   listVal([_,tableVal(ht)]) => ht)
                  in
                           (case (HashTable.listItems res) of 
                              [v] => v)
                  end
              | _ => if str = Names.top_module_name then 
                        let val (tv_map,tm_map) = getValAndModMaps(!top_val_env)
                            val tenv: SV.value_environment = !top_val_env
                            val tmod_name = ModSymbol.makeModSymbol([],Names.top_module_symbol,Names.top_module_symbol)
                            val tmod:SV.module = {env=tenv,mod_name=tmod_name,open_mod_directives=[]}
                            val e = SV.valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.enter(Symbol.empty_mapping,Names.top_module_symbol,tmod)})			    
  	   	            val res = (case env2HTVal(e) of
                                          listVal([_,tableVal(ht)]) => ht)
                        in
                           (case (HashTable.listItems res) of 
                              [v] => v)
                        end
                     else primError("Incorrect use of "^(N.moduleToStringFun_name)^": no module by the name of "^str^" is visible here"))
           end
        | _ => primError(wrongArgKind(N.moduleToStringFun_name,1,stringLCType,v)))
  end

fun moduleSizePrimUFun(v,env,ab) = 
    let val env = top_val_env_backup
    in
      (case isStringValConstructive(v) of
          SOME(str:string) => 
                       let val msym = A.makeMS(str,NONE)
                       in
                         (case lookUpModule(!env,msym) of
  			     SOME(m:module as {env=mod_env,...}) => let val (tv_map,tm_map) = getValAndModMaps(mod_env)
                                                                        val count = Symbol.domainSize(tv_map) + Symbol.domainSize(tm_map)
                                                                    in
                                                                      termVal(AT.makeNumTerm(A.int_num(count,ref "")))
                                                                    end
                           | _ => if str = Names.top_module_name then 
                                     let val (tv_map,tm_map) = getValAndModMaps(!top_val_env)
                                         val count = Symbol.domainSize(tv_map) + Symbol.domainSize(tm_map)
                                     in
                                        termVal(AT.makeNumTerm(A.int_num(count,ref "")))
                                     end
                                     else primError("Incorrect use of "^(N.moduleSizeFun_name)^": no module by the name of "^
                                                    str^" is visible here"))
                       end
        | _ => primError(wrongArgKind(N.moduleSizeFun_name,1,stringLCType,v)))
    end

fun moduleSize1PrimUFun(v,env,ab) = 
    let val env = top_val_env_backup
    in
      (case isStringValConstructive(v) of
          SOME(str:string) => 
                       let val msym = A.makeMS(str,NONE)
                       in
                         (case lookUpModule(!env,msym) of
  			     SOME(m:module as {env=mod_env,...}) => let 
                                                                        val (tv_map,tm_map) = getValAndModMaps(mod_env)
                                                                        val count = Symbol.domainSize(tv_map) + Symbol.domainSize(tm_map)
                                                                    in
                                                                      termVal(AT.makeNumTerm(A.int_num(count,ref "")))
                                                                    end
                           | _ => if str = Names.top_module_name then 
                                     let val (tv_map,tm_map) = getValAndModMaps(!top_val_env)
                                         val count = Symbol.domainSize(tv_map) + Symbol.domainSize(tm_map)
                                     in
                                        termVal(AT.makeNumTerm(A.int_num(count,ref "")))
                                     end
                                     else primError("Incorrect use of "^(N.moduleSizeFun1_name)^": no module by the name of "^
                                                    str^" is visible here"))
                       end
        | _ => primError(wrongArgKind(N.moduleSizeFun1_name,1,stringLCType,v)))
    end

fun submodulesPrimUFun(v,env,ab) = 
    let val env = top_val_env_backup
    in
      (case isStringValConstructive(v) of
          SOME(str:string) => 
                       let val msym = A.makeMS(str,NONE)
                       in
                         (case lookUpModule(!env,msym) of
                             SOME(m:module as {env=mod_env,...}) => let val (tv_map,tm_map) = getValAndModMaps(mod_env)
			                                                val syms = (Symbol.listSymbolsInDomain tm_map)
                                                                        val names = map (fn sym => MLStringToAthString(Symbol.name(sym))) syms
                                                                    in
                                                                      listVal(names)
                                                                    end
                           | _ => if str = Names.top_module_name then 
                                     let val (_,tm_map) = getValAndModMaps(!env)
                                         val syms = (Symbol.listSymbolsInDomain tm_map)
                                         val names = map (fn sym => MLStringToAthString(Symbol.name(sym))) syms
                                     in
                                        listVal(names)
                                     end
                                     else primError("Incorrect use of "^(N.moduleSizeFun_name)^": no module by the name of "^
                                                    str^" is visible here"))
                       end
        | _ => primError(wrongArgKind(N.moduleSizeFun_name,1,stringLCType,v)))
   end

fun moduleAbPrimUFun(v,_,_) = 
             (case isStringValConstructive(v) of
                   SOME(str:string) => (case (HashTable.find P.module_ab_table str) of 
                                          SOME(ht) => listVal(map (fn (p,string_opt) => propVal(p))
                                                                 (HashTable.listItemsi ht))
                                       | _ => listVal([]))
                | _ => primError(wrongArgKind(N.moduleSizeFun_name,1,stringLCType,v)))

fun moduleDomPrimUFun(v,env,ab) = 
     (case isStringValConstructive(v) of
          SOME(str:string) => 
                       let val msym = A.makeMS(str,NONE)
                       in
                         (case lookUpModule(!env,msym) of
                             SOME(m:module as {env=mod_env,...}) => let val (tv_map,tm_map) = getValAndModMaps(mod_env)
                                                                        val syms = (Symbol.listSymbolsInDomain tm_map)@(Symbol.listSymbolsInDomain tv_map)
                                                                        val names = map (fn sym => MLStringToAthString(Symbol.name(sym))) syms
                                                                    in
                                                                      listVal names
                                                                    end
                           | _ => if str = Names.top_module_name then 
                                     let val (tv_map,tm_map) = getValAndModMaps(!top_val_env)
                                         val syms = (Symbol.listSymbolsInDomain tm_map)@(Symbol.listSymbolsInDomain tv_map)
                                         val names = map (fn sym => MLStringToAthString(Symbol.name(sym))) syms
                                     in
                                        listVal names
                                     end
                                     else primError("Incorrect use of "^(N.moduleDomFun_name)^": no module by the name of "^
                                                   str^" is visible here"))
                       end
        | _ => primError(wrongArgKind(N.moduleDomFun_name,1,stringLCType,v)))

fun moduleAppPrimBFun(v1,v2,env,ab) = 
  let 
  in
   (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
          (SOME(str1),SOME(str2)) => 
                       let val msym = A.makeMS(str1,NONE)
                       in
                         (case lookUpModule(!env,msym) of
                             SOME(m:module as {env=mod_env,...}) => let val (tv_map,tm_map) = getValAndModMaps(mod_env)
                                                                        val sym = Symbol.symbol str2
                                                                    in
                                                                      (case Symbol.lookUp(tv_map,sym) of 
                                                                          SOME(v) => v
                                                                        | _ => primError("Incorrect use of "^(N.moduleAppFun_name)^": "^
                                                                                       "Unbound identifier: "^str2))
                                                                    end
                           | _ => if str1 = Names.top_module_name then 
                                     let val (tv_map,tm_map) = getValAndModMaps(!top_val_env)
                                         val sym = Symbol.symbol str2
                                     in
                                       (case Symbol.lookUp(tv_map,sym) of 
                                          SOME(v) => v
                                        | _ => primError("Incorrect use of "^(N.moduleAppFun_name)^": "^
                                                       "Unbound identifier: "^str2))
                                     end
                                     else primError("Incorrect use of "^(N.moduleAppFun_name)^": no module by the name of "^
                                                     str1^" is visible here"))
                       end
        | (SOME(_),_) => primError(wrongArgKind(N.moduleAppFun_name,1,stringLCType,v2))
        | _ => primError(wrongArgKind(N.moduleAppFun_name,1,stringLCType,v1)))
  end

fun printFun(vals,_,_) = 
     let fun getString(v) = (case isStringValConstructive(v) of
                                SOME(str) => str 
                              | _ => (prettyValToStringNoTypes v))
         fun getStrings([]) = "" 
           | getStrings([v]) = getString v 
           | getStrings(v::(more as _::_)) = (getString v)^" "^(getStrings more)
         val string = getStrings(vals)
     in 
        (print(string);unitVal)
     end 

fun makeAthenaListFun(vals,_,_) = listVal(vals)

fun writePrimUFun(v,_,_) =
  let val _ = (case isStringValConstructive(v) of
                  SOME(str) => print(str)
		| _ => printVal(v))
  in
    unitVal
  end

fun valToStringFun([v],_,_) = MLStringToAthString(prettyValToString(v))
  |  valToStringFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.valToString_name,length(vals),1),
                          		            SOME(Array.sub(pos_ar,0)))

fun valToStringPrimUFun(v,_,_) = MLStringToAthString(prettyValToString(v))
fun valToStringUnlimPrimUFun(v,_,_) = MLStringToAthString(prettyValToStringUnlimited(v))
fun valToStringPrimUFun'(v,_,_) = MLStringToAthString(prettyValToString'(v))

fun writeValFun([v],_,_) = (printValNoType(v);unitVal)
  | writeValFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.writeVal_name,length(vals),1),
                                             SOME(Array.sub(pos_ar,0)))

fun writeValPrimUFun(v,_,_) = (printValNoType(v);unitVal)

fun indentPrintFun([termVal(tv),v],_,{pos_ar,file}) = 
    let val _ = ()
    in (case AthTerm.getNumVal(tv) of
          SOME(A.int_num(i,_),neg1) =>
           let val i' = getSignedInt(i,neg1)
           in 
              (case v of 
                  termVal(t) => (print("  "^AthTerm.toPrettyString(i,t,F.makeVarSortPrinter()));unitVal)
                | propVal(p) => (print("  "^pprint(i+2,p));unitVal)
                | _ => evError(wrongArgKind(N.indentPrintFun_name,2,termLCType^" or "^propLCType,v),
                               SOME(Array.sub(pos_ar,2))))
           end
        | _ => evError(wrongArgKind(N.indentPrintFun_name,1,numTermLCType,termVal(tv)),
                     SOME(Array.sub(pos_ar,0))))
    end
  | indentPrintFun([v1,v2],_,{pos_ar,file}) = evError(wrongArgKind(N.indentPrintFun_name,1,numTermLCType,v1),
                                                      SOME(Array.sub(pos_ar,0)))
  | indentPrintFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.indentPrintFun_name,length(vals),2),
                                                   SOME(Array.sub(pos_ar,0)))

fun indentPrintPrimBFun(termVal(tv),v,_,_) = 
    let val _ = ()
    in (case AthTerm.getNumVal(tv) of
          SOME(A.int_num(i,_),neg1) =>
           let val i' = getSignedInt(i,neg1)
           in 
              (case v of 
                  termVal(t) => (print("  "^AthTerm.toPrettyString(i,t,F.makeVarSortPrinter()));unitVal)
                | propVal(p) => (print("  "^pprint(i+2,p));unitVal)
                | _ => primError(wrongArgKind(N.indentPrintFun_name,2,termLCType^" or "^propLCType,v)))
           end
        | _ => primError(wrongArgKind(N.indentPrintFun_name,1,numTermLCType,termVal(tv))))
    end
  | indentPrintPrimBFun(v1,v2,_,_) = primError(wrongArgKind(N.indentPrintFun_name,1,numTermLCType,v1))

fun makeTermFun([v,listVal(arg_vals)],_,{pos_ar,file}) = 
      let val term_args = getTerms(arg_vals,"the list argument of "^N.makeTermFun_name,Array.sub(pos_ar,2))
          fun wrongArgNumber(name,giv,req) = "Wrong number of arguments ("^Int.toString(giv)^") given to "^
                                             name^" via the "^N.makeTermFun_name^" procedure---exactly "^
                                             argNumToString(req)^" required";
      in 
        (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) => termVal(applyTermConstructor(D.fsymName(some_fsym),D.fsymArity(some_fsym),term_args,
                                                   Array.sub(pos_ar,0)))
          | SOME(fs as athNumFSym(anum)) => if length(arg_vals) = 0 then termVal(AthTerm.makeNumTerm(anum)) else
                                               evError(wrongArgNumber(valToString(termConVal(fs)),
                                                                      length(arg_vals),0),
                                                       SOME(Array.sub(pos_ar,2)))
           | SOME(fs as metaIdFSym(str)) => if length(arg_vals) = 0 then termVal(AthTerm.makeIdeConstant(str)) 
                                            else evError(wrongArgNumber(valToString(termConVal(fs)),
                                                                      length(arg_vals),0),
                                                       SOME(Array.sub(pos_ar,2)))
           | _ => evError(wrongArgKind(N.makeTermFun_name,1,termConLCType,v),
                                       SOME(Array.sub(pos_ar,2))))
      end
  | makeTermFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.makeTermFun_name,length(vals),2),
                                             SOME(Array.sub(pos_ar,0)))

fun makeTermPrimBFun(v,listVal(arg_vals),_,_) = 
      let val term_args = getTermsNoPos(arg_vals,"the list argument of "^N.makeTermFun_name,NONE)
          fun wrongArgNumber(name,giv,req) = "Wrong number of arguments ("^Int.toString(giv)^") given to "^
                                             name^" via the "^N.makeTermFun_name^" procedure---exactly "^
                                             argNumToString(req)^" required";
      in 
        (case coerceValIntoTermCon(v) of
            SOME(regFSym(some_fsym)) => termVal(applyTermConstructorNoPos(D.fsymName(some_fsym),term_args))
          | SOME(fs as athNumFSym(anum)) => if length(arg_vals) = 0 then termVal(AthTerm.makeNumTerm(anum)) else
                                               primError(wrongArgNumber(valToString(termConVal(fs)),
                                                                      length(arg_vals),0))
           | SOME(fs as metaIdFSym(str)) => if length(arg_vals) = 0 then termVal(AthTerm.makeIdeConstant(str)) 
                                            else primError(wrongArgNumber(valToString(termConVal(fs)),
                                                                      length(arg_vals),0))
           | _ => primError(wrongArgKind(N.makeTermFun_name,1,termConLCType,v)))
      end
  | makeTermPrimBFun(_,v2,_,_) = primError(wrongArgKind(N.makeTermFun_name,1,listLCType,v2))

fun  transformOutputFun(vals as [v1,v2],(env,ab),{pos_ar,file}) = 
 let fun getConverters(listVal(vals),name,arity) = 
         let val given = List.length(vals)
             val counter = ref 0 
         in 
               (List.map (fn v => (Basic.inc(counter);
                                   (case v of 
                                      closUFunVal(body,_,_,_) => (fn arg_val => evalClosure(v,[arg_val],ab,SOME(Array.sub(pos_ar,0))))
                                    | primUFunVal(f,_) => (fn arg_val => f(arg_val,env,ab))
                                    | _ => evError("Output transformation error: the "^(ordinal(!counter))^" element of the\ngiven list of converters"^
                                                      " must be a unary procedure; instead, it was this: "^(valLCTypeAndString(v)),
                                                      SOME(Array.sub(pos_ar,2))))))
                          vals)
         end
       | getConverters(v,name,arity) = evError("Output transformation error: a list of converters was expected here.\n"^
                                                   "Instead, this was found: "^(valLCTypeAndString(v)),
                                                   SOME(Array.sub(pos_ar,2)))
     fun loop([],res) = res
       | loop(f::more,res) = loop(more,f res)
 in
   (case coerceValIntoTermCon(v1) of
      SOME(regFSym(f)) => 
        let val (arity,name,prec,assoc) = (Data.fsymArity(f),Data.fsymName(f),Data.fsymPrec(f),Data.fsymAssoc(f))
            val name_string = MS.name name 
            val converters = getConverters(v2,name_string,arity)
            fun makeNew(arity,name_string,converters) = 
             (fn (arg_vals,env',ab') => 
                   let val arg_num = length(arg_vals)
                       val _ = if not(arg_num = arity) then 
                                  primError(wrongArgNumber(name_string,arg_num,arity))
                               else ()                                            
                       val arg_terms = getTermsNoPos(arg_vals,name_string,NONE)
                       val res = termVal(applyTermConstructorNoPos(name,arg_terms))
                   in
                      loop(converters,res)
                   end) 
        in 
           (name,funVal(makeNew(arity,name_string,converters),name_string,{arity=arity,prec=prec,assoc=assoc}))
        end
     | _ => (case v1 of 
                funVal(f,fun_name,{arity,prec,assoc,...}) =>              
                 let val converters = getConverters(v2,fun_name,arity)
                     val proc = (fn (arg_vals,env',ab') => 
                                   let val arg_num = length(arg_vals)                  
                                       val _ = if not(arg_num = arity) then 
                                                  primError(wrongArgNumber(fun_name,arg_num,arity))
                                               else ()                                        
                                       val res = f(arg_vals,env',ab')
                                   in
                                      loop(converters,res)                                      
                                   end)
                  in
                    (A.makeMS(fun_name,NONE),funVal(proc,fun_name,{arity=arity,prec=prec,assoc=assoc}))
                  end
              | closUFunVal(body,parameter,clos_env,{name,prec,...}) => 
                 let val closure_name = name 
                     val arity = 1
                     val converters = getConverters(v2,closure_name,arity)
                     val proc = (fn (arg_vals,env',ab') => 
                                   let val res = evalClosure(v1,arg_vals,ab',NONE)
                                   in
                                     loop(converters,res)
                                   end)
                     val name' = !name
                 in
                  (A.makeMS(name',NONE),funVal(proc,name',{arity=arity,prec=prec,assoc=ref(NONE)}))
                 end 
              | closBFunVal(body,parameter1,parameter2,clos_env,{name,prec,assoc,...}) => 
                 let val closure_name = !name 
                     val arity = 2
                     val converters = getConverters(v2,closure_name,arity)
                     val proc = (fn (arg_vals,env',ab') => 
                                   let val res = evalClosure(v1,arg_vals,ab',NONE)
                                   in
                                     loop(converters,res)
                                   end)
                     val name' = !name
                 in
                  (A.makeMS(name',NONE),funVal(proc,name',{arity=arity,prec=prec,assoc=assoc}))
                 end 
              | closFunVal(e,env,{prec,assoc,name}) => 
                 let val closure_name = !name 
                     val arity = getClosureArity(v1)
                     val converters = getConverters(v2,closure_name,arity)
                     val proc = (fn (arg_vals,env',ab') => 
                       let val arg_num = length(arg_vals)                  
                           val _ = if not(arg_num = arity) then 
                                      primError(wrongArgNumber(closure_name,arg_num,arity))
                                   else ()                                          
                           val res = evalClosure(v1,arg_vals,ab',NONE)
                        in
                          loop(converters,res)
                       end)
                    val name' = !name
                 in
                  (A.makeMS(name',NONE),funVal(proc,name',{arity=arity,prec=prec,assoc=assoc}))
                 end
              | primUFunVal(f,{name,prec,...}) =>      
                 let val converters = getConverters(v2,name,1)
                     val proc = (fn (arg_val,env',ab') => 
                                   let val res = f(arg_val,env',ab')
                                   in
                                      loop(converters,res)                                      
                                   end)
                  in
                    (A.makeMS(name,NONE),primUFunVal(proc,{prec=prec,name=name}))
                  end        
              | primBFunVal(f,{name,prec,assoc,...}) =>      
                 let val converters = getConverters(v2,name,2)
                     val proc = (fn (arg_val1,arg_val2,env',ab') => 
                                   let val res = f(arg_val1,arg_val2,env',ab')
                                   in
                                      loop(converters,res)                                      
                                   end)
                  in
                    (A.makeMS(name,NONE),primBFunVal(proc,{prec=prec,name=name,assoc=assoc}))
                  end        
              | _ => evError(wrongArgKind("transform-output",1,functionLCType,v1),SOME(Array.sub(pos_ar,1)))))
  end

fun expandInputFun(vals as [v1,v2],(env,ab),{pos_ar,file}) = 
 let fun getConverters(listVal(vals),name,arity) = 
         let val given = List.length(vals)
             val counter = ref 0 
         in 
           if not(arity =  given) then 
              evError("Input expansion error: wrong number\n"^"of converters ("^(Int.toString(given))^") given for "^name^"; "^
                      "exactly "^(Int.toString(arity))^" are required",SOME(Array.sub(pos_ar,0)))
           else
               (List.map (fn v => (Basic.inc(counter);
                                   (case v of 
                                      closUFunVal(body,_,_,_) => (fn arg_val => evalClosure(v,[arg_val],ab,SOME(Array.sub(pos_ar,0))))
                                    | primUFunVal(f,_) => (fn arg_val => f(arg_val,env,ab))
                                    | _ => evError("Input expansion error: the "^(ordinal(!counter))^" element of the\ngiven list of converters"^
                                                   " must be a unary procedure; instead, it was this: "^(valLCTypeAndString(v)),
                                                   SOME(Array.sub(pos_ar,2))))))
                          vals)
         end
       | getConverters(v,name,arity) = evError("Input expansion error: a list of converters was expected here.\n"^
                                                   "Instead, this was found: "^(valLCTypeAndString(v)),
                                                   SOME(Array.sub(pos_ar,2)))
 in
   (case coerceValIntoTermCon(v1) of
      SOME(regFSym(f)) => 
        let val (arity,name,prec,assoc) = (Data.fsymArity(f),Data.fsymName(f),Data.fsymPrec(f),Data.fsymAssoc(f))
            val name_string = MS.name name 
            val (expected_arg_sorts,result_sort,is_poly,_) = Data.getSignature(name)
            val converters = getConverters(v2,name_string,arity)
            fun makeNew(arity,name_string,converters) = 
             (fn (arg_vals,env',ab') => 
                   let val arg_num = length(arg_vals)
                       val _ = if not(arg_num = arity) then 
                                  primError(wrongArgNumber(name_string,arg_num,arity))
                               else ()                                            
                       val args_and_converters = Basic.zip(arg_vals,converters)
                       val arg_term_vals = List.map (fn (arg_val,converter) => converter(arg_val))
                                                  args_and_converters
                       val arg_terms = getTermsNoPos(arg_term_vals,name_string,SOME(expected_arg_sorts,result_sort,is_poly))
                   in
                      termVal(applyTermConstructorNoPos(name,arg_terms))
                   end)
        in 
           (name,funVal(makeNew(arity,name_string,converters),name_string,{arity=arity,prec=prec,assoc=assoc}))
        end
     | _ => (case v1 of 
               closUFunVal(body,parameter,clos_env,{name,prec,...}) => 
                 let val closure_name = !name 
                     val arity = 1
                     val converters = getConverters(v2,closure_name,arity)
                     val proc = (fn (arg_val,env',ab') => 
                                   let val converter = hd converters
                                       val arg_val' = converter(arg_val)
                                   in
                                     evalClosure(v1,[arg_val'],ab',NONE)
                                   end)
                 in
                  (A.makeMS(closure_name,NONE),primUFunVal(proc,{name=closure_name,prec=prec}))
                 end 
              | closBFunVal(body,parameter1,parameter2,clos_env,{name,assoc,prec,...}) => 
                 let val closure_name = !name 
                     val arity = 2
                     val converters = getConverters(v2,closure_name,arity)
                     val proc = (fn (arg_val1,arg_val2,env',ab') => 
                                   let val converter1 = hd converters
                                       val converter2 = hd(tl(converters))
                                       val arg_val1' = converter1(arg_val1)
                                       val arg_val2' = converter2(arg_val2)
                                   in
                                     evalClosure(v1,[arg_val1',arg_val2'],ab',NONE)
                                   end)
                 in
                  (A.makeMS(closure_name,NONE),primBFunVal(proc,{name=closure_name,prec=prec,assoc=assoc}))
                 end 
              | funVal(f,fun_name,{arity,prec,assoc,...}) =>              
                 let val converters = getConverters(v2,fun_name,arity)
                     val proc = (fn (arg_vals,env',ab') => 
                     let val arg_num = length(arg_vals)                  
                         val _ = if not(arg_num = arity) then 
                                    primError(wrongArgNumber(fun_name,arg_num,arity))
                                 else ()                                        
                         val args_and_converters = Basic.zip(arg_vals,converters)
                         val arg_vals = List.map (fn (arg_val,converter) => converter(arg_val))
                                                  args_and_converters
                      in
                        f(arg_vals,env',ab')
                     end)
                  in
                    (A.makeMS(fun_name,NONE),funVal(proc,fun_name,{arity=arity,prec=prec,assoc=assoc}))
                  end
              | primUFunVal(f,{name,prec,...}) =>              
                 let val converters = getConverters(v2,name,1)
                     val converter = hd converters
                     val proc = (fn (arg_val,env',ab') => 
                                   let val arg_val' = converter(arg_val)
                                   in
                                     f(arg_val',env',ab')
                                   end)
                  in
                    (A.makeMS(name,NONE),primUFunVal(proc,{prec=prec,name=name}))
                  end
              | primBFunVal(f,{name,assoc,prec,...}) =>              
                 let val converters = getConverters(v2,name,1)
                     val converter1 = hd converters
                     val converter2 = hd(tl(converters))
                     val proc = (fn (arg_val1,arg_val2,env',ab') => 
                                   let val arg_val1' = converter1(arg_val1)
                                       val arg_val2' = converter2(arg_val2)
                                   in
                                     f(arg_val1',arg_val2',env',ab')
                                   end)
                  in
                    (A.makeMS(name,NONE),primBFunVal(proc,{prec=prec,assoc=assoc,name=name}))
                  end
              | closFunVal(e,env,{prec,assoc,name}) => 
                 let val arity = getClosureArity(v1)
                     val closure_name = !name
                     val converters = getConverters(v2,closure_name,arity)
                     val proc = (fn (arg_vals,env',ab') => 
                       let val arg_num = length(arg_vals)                  
                           val _ = if not(arg_num = arity) then 
                                      primError(wrongArgNumber(closure_name,arg_num,arity))
                                   else ()                                          
                           val args_and_converters = Basic.zip(arg_vals,converters)
                           val arg_vals = List.map (fn (arg_val,converter) => converter(arg_val))
                                                    args_and_converters
                        in
                          evalClosure(v1,arg_vals,ab',NONE)
                       end)
                 in
                  (A.makeMS(closure_name,NONE),funVal(proc,closure_name,{arity=arity,prec=prec,assoc=assoc}))
                 end
              | _ => evError(wrongArgKind("expand-input",1,functionLCType,v1),SOME(Array.sub(pos_ar,1)))))
  end

fun doAppArgs([],[],tab,arg_vals',_) = (tab,arg_vals')
 |  doAppArgs(pwp::more_params,arg_val::more_arg_vals,tab,arg_vals',i) =  
      (case pwp of
          A.someParam({name,pos as param_pos,sort_as_fterm as SOME(fsort),...}) =>
                                           ((case (coerceValIntoTerm arg_val) of 
                                                 SOME(t) => let val term_sort = AT.getSort(t)
                                                            in
                                                               (case unifySorts(term_sort,fsort) of
                                                                   SOME(sort_sub) =>  
                                                                       let val t' = AT.applySortSub(sort_sub,t)
                                                                           val arg_val' = termVal t'
                                                                       in         
                                                                         doAppArgs(more_params,more_arg_vals,Symbol.enter(tab,name,arg_val'),
                                                                           arg_val'::arg_vals',i+1)
                                                                       end
                                                                 | _ => primError("the "^(ordinal i)^" argument in this procedure call violated the\n"^
                                                                                "sort constraint of the corresponding parameter. The relevant sort \n"^
                                                                                "annotation ("^(A.posToString param_pos)^
                                                                                 ") dictates a term of sort "^
                                                                                (F.toStringDefault(fsort))))
                                                            end))
         				       | A.someParam({name,sort_as_fterm as NONE,...}) =>
                	                             (doAppArgs(more_params,more_arg_vals,Symbol.enter(tab,name,arg_val),arg_val::arg_vals',i+1))
 				               | A.wildCard(_) => 
				  	          doAppArgs(more_params,more_arg_vals,tab,arg_val::arg_vals',i+1))


fun overloadFun(vals as [v1,v2],(env,ab),pos_ar_and_file as {pos_ar,file},overloaded_name,inverted) = 
 let val overload_pos = getPosOpt(pos_ar,0) 
     val (applyOld,arity_old,name_old_sym) = 
            (case coerceValIntoTermCon(v2) of
               SOME(regFSym(old_fsym)) => let val old_sym = Data.fsymName(old_fsym)
                                              val old_sym_str = MS.name(old_sym)
					      val (expected_arg_sorts,result_sort,is_poly,_) = Data.getSignature(old_sym)
                                              fun appOld(name,arity,arg_vals,ab) =                                                 
                                                    termVal(applyTermConstructorNoPos(name,getTermsNoPos(arg_vals,old_sym_str,SOME(expected_arg_sorts,result_sort,is_poly))))
                                          in
                                            (appOld,Data.fsymArity(old_fsym),old_sym)
                                          end
             | _ => (case v2 of
                      closUFunVal(body,parameter,clos_env,{name=clos_name,prec,...}) => 
                         let fun appOld(name,arity,arg_vals,ab) = 
                              (case arg_vals of
                                  [av] =>
                                    let val (vmap,mmap) = getValAndModMaps(!clos_env)
                                        val vmap' = Symbol.enter(vmap,parameter,av)
                                        val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
                                    in
                                       Semantics.evalExp(body,new_env,ab)
                                    end
                                 | _ => evError("Wrong number of arguments given to unary procedure "^(!clos_name),overload_pos))
                         in
                           (appOld,1,A.makeMS(!clos_name,NONE))
                         end
                    | closBFunVal(body,p1,p2,clos_env,{name=clos_name,prec,...}) => 
                         let fun appOld(name,arity,arg_vals,ab) = 
                                (case arg_vals of
                                   [av1,av2] => 
                                     let val (vmap,mmap) = getValAndModMaps(!clos_env)
                                         val vmap' = Symbol.enter(vmap,p1,av1)
                                         val vmap'' = Symbol.enter(vmap',p2,av2)
                                         val new_env = ref(valEnv({val_map=vmap'',mod_map=mmap}))
                                     in
                                        Semantics.evalExp(body,new_env,ab)
                                     end
                                | _ => evError("Wrong number of arguments given to binary procedure "^(!clos_name),overload_pos))
                         in
                           (appOld,2,A.makeMS(!clos_name,NONE))
                         end
                    | closFunVal(A.functionExp({params,body,...}),clos_env,_) => 
                         let fun appOld(name,arity,arg_vals,ab) = 
                                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                                       val (vmap',vals') = doAppArgs(params,arg_vals,vmap,[],1)
                                       val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
                                   in
                                      Semantics.evalExp(body,new_env,ab)
                                   end
                         in
                           (appOld,length(params),A.makeMS("",NONE))
                         end
                     | primUFunVal(f,{name=prim_name,prec,...}) =>
                         let fun appOld(name,arity,arg_vals,ab) = 
                                   (case arg_vals of
                                      [av] => f(av,env,ab)
                                    | _ => evError("Wrong number of arguments given to unary procedure "^prim_name,overload_pos))
                         in
                           (appOld,1,A.makeMS(prim_name,NONE))
                         end                            
                     | primBFunVal(f,{name=prim_name,prec,...}) =>
                         let fun appOld(name,arity,arg_vals,ab) = 
                                   (case arg_vals of
                                      [av1,av2] => f(av1,av2,env,ab)
                                    | _ => evError("Wrong number of arguments given to unary procedure "^prim_name,overload_pos))
                         in
                           (appOld,2,A.makeMS(prim_name,NONE))
                         end                            
                     | funVal(f,name,{arity,prec,assoc}) => 
                         let fun appOld(name,arity,arg_vals,ab) = f(arg_vals,env,ab)
                         in
                           (appOld,arity,A.makeMS(name,NONE))
                         end
                     | _ => evError("Overloading error: a function symbol was expected here",SOME(Array.sub(pos_ar,3)))))
     val name_old = MS.name(name_old_sym)
     val signature_opt = ref(NONE: (FTerm.term list * FTerm.term * bool) option)
     val (applyNew,name_new:string,arity_new,prec_new,assoc_new) = 
            (case coerceValIntoTermCon(v1) of
                SOME(regFSym(new_fsym)) => 
                  let val (arity_new,name_new_sym,prec_new_1,assoc_new_1) = 
                                  (Data.fsymArity(new_fsym),Data.fsymName(new_fsym),
                                   Data.fsymPrec(new_fsym),Data.fsymAssoc(new_fsym))
                      val new_name:string = MS.name name_new_sym
                      val (expected_arg_sorts,result_sort,is_poly,_) = Data.getSignature(name_new_sym)
                      val _ = let 
                              in
                                 (signature_opt := SOME(expected_arg_sorts,result_sort,is_poly))
                              end
                  in
                     ((fn (arity_new,val_args,term_args_thunk) => 
                          termVal(applyTermConstructorNoPos(name_new_sym,term_args_thunk()))),
                      new_name,arity_new,prec_new_1,assoc_new_1)
                  end
               | _ => (case v1 of 
                         funVal(f,new_name,{arity,prec,assoc,...}) => 
                              ((fn (arity_new,val_args,term_args_thunk) => 
                                    f(val_args,env,ab)),new_name,arity,prec,assoc)

                       | primUFunVal(f,{name=prim_name,prec,...}) => 
                              ((fn (arity_new,val_args,term_args_thunk) => 
                                  (case val_args of
                                      [av] => f(av,env,ab)
                                    | _ => evError("Incorrect number of arguments given to unary procedure "^(prim_name),overload_pos))),
                                prim_name,1,prec,ref(NONE))
                       | primBFunVal(f,{name=prim_name,prec,assoc,...}) => 
                              ((fn (arity_new,val_args,term_args_thunk) => 
                                  (case val_args of
                                      [av1,av2] => f(av1,av2,env,ab)
                                    | _ => evError("Incorrect number of arguments given to binary procedure "^(prim_name),overload_pos))),
                                prim_name,2,prec,assoc)
                       | closUFunVal(body,parameter,ref clos_env,{name=clos_name,prec,...}) => 
                              ((fn (arity_new,[av],term_args_thunk) =>
                                   let val (vmap,mmap) = getValAndModMaps(clos_env)
                                       val vmap' = Symbol.enter(vmap,parameter,av)
                                       val new_env = valEnv({val_map=vmap',mod_map=mmap})
                                   in
                                      Semantics.evalExp(body,ref new_env,ab)
                                   end),!clos_name,1,prec,ref(NONE))
                       | closBFunVal(body,p1,p2,ref clos_env,{name=clos_name,prec,assoc,...}) => 
                              ((fn (arity_new,[av1,av2],term_args_thunk) =>
                                   let val (vmap,mmap) = getValAndModMaps(clos_env)
                                       val vmap' = Symbol.enter(vmap,p1,av1)
                                       val vmap'' = Symbol.enter(vmap',p2,av2)
                                       val new_env = valEnv({val_map=vmap'',mod_map=mmap})
                                   in
                                      Semantics.evalExp(body,ref new_env,ab)
                                   end),!clos_name,2,prec,assoc)
                       | closFunVal(A.functionExp({params,body,pos=fexp_pos,...}),ref clos_env,{name,prec,assoc,...}) => 
                              ((fn (arity_new,val_args,term_args_thunk) =>
                                   let fun getBindings([],[],res) = rev res
                                         | getBindings((A.someParam({name,...}))::more_params,v::more_vals,res) =  
                                                getBindings(more_params,more_vals,(name,v)::res)
                                         | getBindings(_::more_params,_::more_vals,res) =  getBindings(more_params,more_vals,res)
                                       val bindings = getBindings(params,val_args,[])
                                       val (vmap,mmap) = getValAndModMaps(clos_env)
                                       val new_env = valEnv({val_map=S.enterLst(vmap,bindings),mod_map=mmap})
                                   in
                                      Semantics.evalExp(body,ref new_env,ab)
                                   end),!name,length params,prec,assoc)
                       | _ => evError("Overloading error: a function symbol or procedure was expected here",
                                      SOME(Array.sub(pos_ar,2)))))
     val new_name_sym = A.makeMS(name_new,NONE)
     fun newFun(vals,env',ab') = 
          let val term_args_thunk = fn () => getTermsNoPos(vals,name_new,!signature_opt)
              val msg = ref ""
           in
             if inverted then 
             ((applyNew(arity_new,vals,term_args_thunk)) 
                 handle _ => applyOld(name_old_sym,arity_old,vals,ab'))
             else 
             ((applyOld(name_old_sym,arity_old,vals,ab')) 
                 handle _ => applyNew(arity_new,vals,term_args_thunk))
           end
 in 
   (new_name_sym,funVal(newFun,overloaded_name,{arity=arity_new,prec=prec_new,assoc=assoc_new}))
 end
| overloadFun(vals,(env,ab),{pos_ar,file},_,_) = 
    evError("Overloading error: two arguments were expected here, "^(Int.toString(length(vals)))^" found",
            SOME(Array.sub(pos_ar,0)))

fun variantsFun([v1,v2],(env,_),{pos_ar,file}) = 
       (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
           (SOME(str1),SOME(str2))  => 
		let fun isLegalVar(str) = hd(explode(str)) = Names.sort_variable_prefix_as_char
        	in
		  (case (Terms.parseSymTerm(str1,isLegalVar),Terms.parseSymTerm(str2,isLegalVar)) of
	 	     (SOME(t1),SOME(t2)) => let val _ = if Terms.isSymTermLegalSort(t1) andalso
							   Terms.isSymTermLegalSort(t2)
							then () else
						        evError("\nInvalid sort",
							      SOME(Array.sub(pos_ar,2)))
					         val (sort1,sort2) = (FTerm.translateFromSymTerm(t1),
						   		      FTerm.translateFromSymTerm(t2))
					    in
						MLBoolToAthBoolVal(F.variants1(sort1,sort2))
					    end
		  | _ => evError("\nInvalid sort",SOME(Array.sub(pos_ar,2))))
	        end
        | _ => evError(wrongArgKind(N.fresh_var_name,1,stringLCType,v1),SOME(Array.sub(pos_ar,2))))
  | variantsFun(vals,_,{pos_ar,file}) = evError(wrongArgNumberFlex("variants?",length(vals),[0,1]),
                                                getPosOpt(pos_ar,0))   

fun variantsPrimBFun(v1,v2,env,_) = 
       (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
           (SOME(str1),SOME(str2))  => 
		let fun isLegalVar(str) = hd(explode(str)) = Names.sort_variable_prefix_as_char
        	in
		  (case (Terms.parseSymTerm(str1,isLegalVar),Terms.parseSymTerm(str2,isLegalVar)) of
	 	     (SOME(t1),SOME(t2)) => let val _ = if Terms.isSymTermLegalSort(t1) andalso
							   Terms.isSymTermLegalSort(t2)
							then () else
						        primError("\nInvalid sort")
					         val (sort1,sort2) = (FTerm.translateFromSymTerm(t1),
						   		      FTerm.translateFromSymTerm(t2))
					    in
						MLBoolToAthBoolVal(F.variants1(sort1,sort2))
					    end
		  | _ => primError("\nInvalid sort"))
	        end
        | _ => primError(wrongArgKind(N.fresh_var_name,1,stringLCType,v1)))
					
fun showTCCsFun([],_,_) = 
      let val tccs = !(AT.global_tccs)
          val tcc_str = AT.tccsToString(tccs)
      in
        (print("\nTCCs:[[[[[[[[[[[[[[[[[\n"^tcc_str^"\n]]]]]]]]]]]]]]]]]\n");unitVal)
      end

fun clearTCCsFun([],_,_) = 
      let val _ = AT.global_tccs := []
      in
        unitVal
      end

fun stringToSort(str) = 
  let fun isLegalVar(str) = hd(explode(str)) = Names.sort_variable_prefix_as_char
  in
    (case Terms.parseSymTerm(str,isLegalVar) of
        SOME(t) => let val t = Terms.putBogusTags(t,A.dum_pos)
                       val t' = SV.qualifySort(t)
                       val t'' = SymTerm.stripTags(t')
                       val _ = if Terms.isSymTermLegalSort(t'') then () else
				  primError("\nInvalid sort: "^SymTerm.toPrettyString(14,t'',Symbol.name))
  	               val sort = FTerm.translateFromSymTerm(t'')
                 in
                   sort
                 end)
  end

fun freshVarFun([],_,_) = termVal(AthTerm.makeVar(AthTermVar.fresh()))
  | freshVarFun(vals,_,_) =  
     let val v = hd vals
     in
       (case isStringValConstructive(v) of
           SOME(str) => let val sort = stringToSort(str)
                            val fv = (case (tl vals) of 
                                         [v'] => (case coerceValIntoTerm(v') of
                                                     SOME(t) => (case AthTerm.isIdeConstant(t) of
                                                                    SOME(p) => AthTermVar.freshWithSortAndPrefix(p,sort))
                                                                  | _ => primError(wrongArgKind(N.fresh_var_name,2,"identifier",v')))
                                                   | [] => AthTermVar.freshWithSort(sort)
                                      | _ => primError(wrongArgNumberFlex(N.fresh_var_name,length(vals),[0,1,2])))
		        in
		           termVal(AthTerm.makeVar(fv))
  	   	        end
         | _ => primError(wrongArgKind(N.fresh_var_name,1,stringLCType,v)))
     end

fun makeFreshSymbol(sort_name:string) = 
      let val sort = stringToSort(sort_name)
          val clist = String.explode sort_name
          val clist' = Basic.mapSelect((fn c => if c = #" " then #"_" else c),clist,fn x => not(Basic.isMember(x,[#")",#"("])))
          val sort_name' = (implode clist') ^ "_";
	  val fresh_sym = Symbol.freshSymbol(SOME sort_name')
          val msym = A.msym(fresh_sym)
          val tagged_absyn_sort = Terms.putBogusTags(SymTerm.makeVar(fresh_sym),A.dum_pos)
          val new_fsym = declared({name=msym,obtype_params=[],bits=makeWord({poly=false,pred_based_sig=false}),
                                   argument_types=[],range_type=sort,prec=ref(0),assoc=ref(NONE),absyn_argument_types=[],arity=0,absyn_range_type=tagged_absyn_sort})
          val _ = Data.addFSym(new_fsym)
	  val sym_val = termConVal(regFSym(new_fsym))
	  val msym_list = (case (HashTable.find Data.domains_as_datatypes_table sort_name) of
                            SOME(L) => L
                         | _ => [])
          val _ = HashTable.insert Data.domains_as_datatypes_table (sort_name,new_fsym::msym_list)
     in
        sym_val
     end

fun makeFreshSymbolsPrimBFun(v1,v2,env,_) = 
       (case isStringValConstructive(v1) of
           SOME(sort_name) => 
             (case (HashTable.find Data.domains_as_datatypes_table sort_name) of
                 SOME(L) => (case isStringValConstructive(v2) of
                                SOME(count_str) => (case Int.fromString(count_str) of
                                                       SOME(count) => let val len = length(L)
                                                                      in
                                                                         if len >= count then 
                                                                            listVal(List.take(rev(map (fn fsym => termConVal(regFSym(fsym))) L),count))
                                                                         else let val range = Basic.fromI2N(len+1,count)
                                                                                  val _ = map (fn _ => makeFreshSymbol(sort_name)) range
                                                                              in
                                                                                 (case (HashTable.find Data.domains_as_datatypes_table sort_name) of   
                                                                                     SOME(L) => listVal(List.take(rev(map (fn fsym => termConVal(regFSym(fsym))) L),count)))
                                                                              end
                                                                      end
                                                    | _ => primError("A positive integer numeral was expected as the second argument of " ^ N.freshSymbolFun_name))
                              | _ => primError(wrongArgKind(N.freshSymbolFun_name,2,stringLCType,v2)))
               | _ => (case isStringValConstructive(v2) of
                          SOME(count_str) => (case Int.fromString(count_str) of
                                                 SOME(count) => let val range = Basic.fromI2N(1,count)
                                                                    val syms = map (fn _ => makeFreshSymbol(sort_name)) range
                                                                in
                                                                  listVal(syms)
                                                                end
                                             | _ => primError("A positive integer numeral was expected as the second argument of " ^ N.freshSymbolFun_name))
                         | _ => primError(wrongArgKind(N.freshSymbolFun_name,2,stringLCType,v2))))
         | _ => primError(wrongArgKind(N.freshSymbolFun_name,1,stringLCType,v1)))
 
fun freshVarPrimUFun(v,env,_) = 
       (case isStringValConstructive(v) of
           SOME(str) => let fun isLegalVar(str) = hd(explode(str)) = Names.sort_variable_prefix_as_char
			in
			   (case Terms.parseSymTerm(str,isLegalVar) of
			       SOME(t) => let val _ = if Terms.isSymTermLegalSort(t) then () else
						      primError("\nInvalid sort: "^SymTerm.toPrettyString(14,t,Symbol.name))
					      val sort = FTerm.translateFromSymTerm(t)
                                              val fv = AthTermVar.freshWithSort(sort)
					  in
					     termVal(AthTerm.makeVar(fv))
					  end
			    | _ => primError("\nInvalid sort: "^str))
                        end
        | _ => primError(wrongArgKind(N.fresh_var_name,1,stringLCType,v)))

fun freshVarWithPrefixPrimBFun(v1,v2,env,_) = 
       (case isStringValConstructive(v1) of
           SOME(str) => let fun isLegalVar(str) = hd(explode(str)) = Names.sort_variable_prefix_as_char
			in
			   (case Terms.parseSymTerm(str,isLegalVar) of
			       SOME(t) => let val _ = if Terms.isSymTermLegalSort(t) then () else
						      primError("\nInvalid sort: "^SymTerm.toPrettyString(14,t,Symbol.name))
					      val sort = FTerm.translateFromSymTerm(t)
                                              val fv = (case coerceValIntoTerm(v2) of
                                                          SOME(t) => (case AthTerm.isIdeConstant(t) of
                                                                         SOME(p) => AthTermVar.freshWithSortAndPrefix(p,sort))
                                                                      | _ => primError(wrongArgKind(N.fresh_var_with_prefix_name,2,"identifier",v2)))
					  in
					     termVal(AthTerm.makeVar(fv))
					  end
			    | _ => primError("\nInvalid sort: "^str))
                        end
        | _ => primError(wrongArgKind(N.fresh_var_with_prefix_name,1,stringLCType,v1)))

fun writeFile(fname,str:string) = let val stream = TextIO.openAppend(fname) handle _ => TextIO.openOut(fname)
                                  in
                                     (TextIO.output(stream,str);TextIO.closeOut(stream))
                                  end
 
fun readFilePrimUFun(v,_,_) = 
       (case isStringValConstructive(v) of
           SOME(str) => (MLStringToAthString(readFile(str)) 
                            handle _ => primError("Unable to read file "^str))
         | _ => primError(wrongArgKind(N.readFile_name,1,stringLCType,v)))

fun lineCountPrimUFun(v,_,_) = 
       (case isStringValConstructive(v) of
           SOME(path) => ((termVal(AthTerm.makeNumTerm(A.int_num(Basic.countLines(path),ref ""))))
                            handle _ => primError("Unable to read file "^path))
         | _ => primError(wrongArgKind(N.lineCount_name,1,stringLCType,v)))

                                   
fun writeFileFun([v1,v2],_,{pos_ar,file}) = 
                             (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
                                 (SOME(str1),SOME(str2)) => ((writeFile(str1,str2);unitVal)
                                                             handle _ => evError("Unable to write file "^str1,
                                                                                  SOME(Array.sub(pos_ar,1))))
                               | (NONE,_) => evError(wrongArgKind(N.writeFile_name,1,stringLCType,v1),
                                                     SOME(Array.sub(pos_ar,2)))
                               | (SOME(fname),NONE) => 
                                   (case v2 of
                                      vectorVal(A) =>  
                                        let val stream = TextIO.openAppend(fname) handle _ => TextIO.openOut(fname)
                                            fun f(i) = (case Array.sub(A,i) of
                                                          charVal(c) => (TextIO.output(stream,Char.toString(Char.chr(c)));
                                                                         f(i+1))
                                                        | _ => unitVal)
                                            val res = f(0)
                                            val _ = TextIO.closeOut(stream)
                                        in res end
                                    | _ => evError(wrongArgKind(N.writeFile_name,2,stringLCType,v2),
                                                     SOME(Array.sub(pos_ar,3)))))
  | writeFileFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.writeFile_name,length(vals),2),
                                                 SOME(Array.sub(pos_ar,0)))

fun writeFilePrimBFun(v1,v2,_,_) = 
                             (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
                                 (SOME(str1),SOME(str2)) => ((writeFile(str1,str2);unitVal)
                                                             handle _ => primError("Unable to write file "^str1))
                               | (NONE,_) => primError(wrongArgKind(N.writeFile_name,1,stringLCType,v1))
                               | (SOME(fname),NONE) => 
                                   (case v2 of
                                      vectorVal(A) =>  
                                        let val stream = TextIO.openAppend(fname) handle _ => TextIO.openOut(fname)
                                            fun f(i) = (case Array.sub(A,i) of
                                                          charVal(c) => (TextIO.output(stream,Char.toString(Char.chr(c)));
                                                                         f(i+1))
                                                        | _ => unitVal)
                                            val res = f(0)
                                            val _ = TextIO.closeOut(stream)
                                        in res end
                                    | _ => primError(wrongArgKind(N.writeFile_name,2,stringLCType,v2))))
      
fun readOneChar() = Char.ord(hd(explode(TextIO.inputN(TextIO.stdIn,1))))

fun readOneCharFun([],_,_) = charVal(readOneChar())
  | readOneCharFun(vals,_,_) = primError(wrongArgNumber(N.readOneChar_name,length(vals),0))

fun replaceVarFun([v1,v2,v3],env,_) = 
  let fun error1(v,t,t') = "\nAttempt to replace the variable "^(ATV.toPrettyString(0,v,F.varToString))^
		        "\ninside the term:\n"^AT.toPrettyString(0,t,F.varToString)^
			"\nby a term of incompatible sort:\n"^(AT.toPrettyString(0,t',F.varToString))
      fun error2(v,P,t) = "\nAttempt to replace the variable "^(ATV.toPrettyString(0,v,F.varToString))^
		        "\ninside the sentence:\n"^P.toPrettyString(0,P,F.varToString)^
			"\nby a term of incompatible sort:"^(AT.toPrettyString(0,t,F.varToString))
      fun checkSorts1(v,t1,t2) = 
	 let val (v_sort,t1_sort) = (ATV.getSort(v),AT.getSort(t1))
	 in
	    (case F.isSubSort(t1_sort,v_sort) of
	       SOME(_) => ()
	    |  _ => primError(error1(v,t2,t1)))
	 end
      fun checkSorts2(v,t,P) = 
	 let val (v_sort,t_sort) = (ATV.getSort(v),AT.getSort(t))
	 in
	    (case F.isSubSort(t_sort,v_sort) of
	       SOME(_) => ()
	    |  _ => primError(error2(v,P,t)))
	 end
  in
     (case coerceValIntoTerm(v1) of
        SOME(t1) => 
          (case AT.isVarOpt(t1) of
             SOME(v) => 
               (case coerceValIntoTerm(v2) of
                  SOME(t2) => 
                    (case coerceValIntoTerm(v3) of
                        SOME(t3) => (checkSorts1(v,t2,t3);termVal(AT.replace(v,t2,t3)))
                      | _ => (case coerceValIntoProp(v3) of
                                 SOME(P) => (checkSorts2(v,t2,P);propVal(P.replace(v,t2,P)))
                               | _ => primError(wrongArgKind(N.replaceVar_name,3,termLCType^" or "^propLCType,v3))))
                | _ => primError(wrongArgKind(N.replaceVar_name,2,termLCType,v2)))
           | _ => primError(wrongArgKind(N.replaceVar_name,1,varLCType,v1)))
      | _ => primError(wrongArgKind(N.replaceVar_name,1,varLCType,v1)))
  end
  | replaceVarFun(vals,_,_) = primError(wrongArgNumber(N.replaceVar_name,length(vals),3))

fun sizeFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoProp(v) of 
          SOME(P) => termVal(AthTerm.makeNumTerm(A.int_num(P.size(P),ref "")))
        | _ => (case coerceValIntoTerm(v) of
                  SOME(t) => termVal(AthTerm.makeNumTerm(A.int_num(AT.size(t),ref "")))
                | _ => evError(wrongArgKind(N.sizeFun_name,1,propLCType,v),getPosOpt(pos_ar,2))))
  | sizeFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.sizeFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun sizePrimUFun(v,env,_) = 
      (case coerceValIntoProp(v) of 
          SOME(P) => termVal(AthTerm.makeNumTerm(A.int_num(P.size(P),ref "")))
        | _ => (case coerceValIntoTerm(v) of
                  SOME(t) => termVal(AthTerm.makeNumTerm(A.int_num(AT.size(t),ref "")))
                | _ => primError(wrongArgKind(N.sizeFun_name,1,propLCType,v))))

fun renameFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoProp(v) of
          SOME(P) => propVal(Prop.alphaRename(P))
        | _ => evError(wrongArgKind(N.renameFun_name,1,propLCType,v),getPosOpt(pos_ar,2)))
  | renameFun([v1,v2],(env,_),{pos_ar,file}) = 
      let fun msg(i,v) = "Wrong kind of value found in the "^ordinal(i)^" position of the list argument"^
                         " of "^N.renameFun_name^"---a "^termLCType^" or "^propLCType^" was expected, "^
                         "but the given value was a "^valLCTypeAndString(v)
      in
        (case coerceValIntoProp(v1) of
            SOME(P) => propVal(Prop.alphaRename(P))
          | _ => evError(wrongArgKind(N.renameFun_name,1,propLCType,v1),getPosOpt(pos_ar,2)))
      end
  | renameFun(vals,_,{pos_ar,file}) = evError(wrongArgNumberFlex(N.renameFun_name,length(vals),[1,2]),
                                                  getPosOpt(pos_ar,0))
						  
fun renamePrimUFun(v,env,_) = 
      (case coerceValIntoProp(v) of
          SOME(P) => propVal(Prop.alphaRename(P))
        | _ => primError(wrongArgKind(N.renameFun_name,1,propLCType,v)))

fun makeVarList(vars) = map (fn v => termVal(AthTerm.makeVar(v))) vars

fun displayFun([v],(env,_),{pos_ar,file}) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => (AT.display(t);unitVal)
       | _ => (case coerceValIntoProp(v) of 
                  SOME(P) => (Prop.display(P);unitVal)
		| _ => evError(wrongArgKind("display",1,propLCType,v),getPosOpt(pos_ar,2))))
  | displayFun(vals,_,{pos_ar,file}) = evError(wrongArgNumberFlex("display",length(vals),[1,2]),
                                                  getPosOpt(pos_ar,0))

fun displayPrimUFun(v,env,_) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => (AT.display(t);unitVal)
       | _ => (case coerceValIntoProp(v) of 
                  SOME(P) => (Prop.display(P);unitVal)
		| _ => primError(wrongArgKind("display",1,propLCType,v))))

fun varsFun([v],(env,_),{pos_ar,file}) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => listVal(makeVarList(AthTerm.getVars(t)))
       | _ => (case coerceValIntoProp(v) of 
                  SOME(P) => listVal(makeVarList(Prop.freeVars(P)))
                | _ => evError(wrongArgKind(N.varsFun_name,1,termLCType^" or "^propLCType,v),
                               getPosOpt(pos_ar,2))))
  | varsFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.varsFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun varsPrimUFun(v,env,_) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => listVal(makeVarList(AthTerm.getVars(t)))
       | _ => (case coerceValIntoProp(v) of 
                  SOME(P) => listVal(makeVarList(Prop.freeVars(P)))
                | _ => primError(wrongArgKind(N.varsFun_name,1,termLCType^" or "^propLCType,v))))

fun varsInOrderPrimUFun(v,env,_) = 
     (case coerceValIntoTerm(v) of
         SOME(t) => listVal(makeVarList(AthTerm.getVarsInOrder(t)))
       | _ => (case coerceValIntoProp(v) of 
                  SOME(P) => listVal(makeVarList(Prop.freeVars(P)))
                | _ => primError(wrongArgKind("varsio",1,termLCType^" or "^propLCType,v))))

fun repeat(f,x,n) = let val i = ref(n)
                        val _ = while (!i > 0) do
                                   (f(x);i := !i - 1)
                    in
                       f(x)
                    end
		    
fun repeatPrimBFun(cv as closFunVal(A.functionExp({params,body,pos,...}),clos_env,{prec,assoc,...}),v_num,env,ab) = 
     (case v_num of 
         termVal(t) => (case AthTerm.getNumVal(t) of
                           SOME(A.int_num(i,_),neg1) =>
                             let val n = getSignedInt(i,neg1)
                                 val (vmap,mmap) = getValAndModMaps(!clos_env)
                                 val new_env = ref(valEnv({val_map=enterParamValLst(vmap,params,[]),mod_map=mmap}))
                                 fun loop(i) = if i < 1 then () else (evalExp(body,new_env,ab);loop(i-1))
                             in
                               (loop(n);unitVal)
                             end))

fun freeVarsFun([listVal pvals],(env,_),{pos_ar,file}) = 
     let val props = Semantics.getProps(pvals,"the argument list given to "^N.freeVarsFun_name,env)
     in 
        listVal(makeVarList(Basic.removeDuplicatesEq(Prop.freeVarsLst(props),ATV.athTermVarEq)))
     end
   | freeVarsFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoProp(v) of
          SOME(P) => listVal(makeVarList(Prop.freeVars(P)))
        | _ => evError(wrongArgKind(N.freeVarsFun_name,1,propLCType,v),getPosOpt(pos_ar,2)))
  | freeVarsFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.freeVarsFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun freeVarsPrimUFun(listVal(pvals),env,_) = 
     let val props = Semantics.getProps(pvals,"the argument list given to "^N.freeVarsFun_name,env)
     in 
        listVal(makeVarList(Basic.removeDuplicatesEq(Prop.freeVarsLst(props),ATV.athTermVarEq)))
     end
   | freeVarsPrimUFun(v,env,_) = 
      (case coerceValIntoProp(v) of
          SOME(P) => listVal(makeVarList(Prop.freeVars(P)))
        | _ => primError(wrongArgKind(N.freeVarsFun_name,1,propLCType,v)))                               

fun satSolve([listVal pvals],env,_) = 
      let val props = Semantics.getProps(pvals,"the argument list given to "^"ssat",env)
      in 
        MLBoolToAth(Prop.satSolveTableauNew(props))
      end
  | satSolve(_) = primError("Incorrect invocation of ssat")


fun satSolve0([listVal pvals],env,_) = 
      let val props = Semantics.getProps(pvals,"the argument list given to "^"ssat",env)
      in 
        case Prop.satSolvableTableau(props) of
           SOME(b) => MLBoolToAth(b)
         | _ => MLBoolToAth(false)
      end
  | satSolve0(_) = primError("Incorrect invocation of ssat")

fun alphaEquivFun([v1,v2],(env,_),{pos_ar,file}) = 
     (case coerceValIntoProp(v1) of
         SOME(P1) => (case coerceValIntoProp(v2) of
                         SOME(P2) => MLBoolToAth(Prop.alEq(P1,P2))
                       | _ => evError(wrongArgKind(N.alEqFun_name,2,propLCType,v2),getPosOpt(pos_ar,3)))
       | _ => evError(wrongArgKind(N.alEqFun_name,1,propLCType,v2),getPosOpt(pos_ar,2)))
  | alphaEquivFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.alEqFun_name,length(vals),2),getPosOpt(pos_ar,0))

fun alphaEquivPrimBFun(v1,v2,env,_) = 
     (case coerceValIntoProp(v1) of
         SOME(P1) => (case coerceValIntoProp(v2) of
                         SOME(P2) => MLBoolToAth(Prop.alEq(P1,P2))
                       | _ => primError(wrongArgKind(N.alEqFun_name,2,propLCType,v2)))
       | _ => primError(wrongArgKind(N.alEqFun_name,1,propLCType,v2)))

fun isSubFun([subVal(_)],_,_) = true_val
  | isSubFun([_],_,_) = false_val
  | isSubFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.isSubFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun makeTableFun([],_,_) = tableVal(HashTable.mkTable(SemanticValues.hashVal, valEq) (!(Options.default_table_size),Data.GenEx("Failed table creation")))
  | makeTableFun([v],_,_) = 
     (case v of
         listVal(pairs) =>
            let val t = HashTable.mkTable(SemanticValues.hashVal, valEq) (!(Options.default_table_size),Data.GenEx("Failed table creation"))
                val _ = List.app (fn listVal([v1,v2]) => HashTable.insert t (v1,v2)
                                   | listVal([v1,_,v2]) => HashTable.insert t (v1,v2)
                                   | listVal([]) => ()
                                   | _ => primError("Invalid list argument given to "^N.makeTableFun_name^
                                                    "\nA list of pairs (two-element lists) was expected."))
                                 pairs
            in
              tableVal(t)
            end
       | termVal(t) => (case AthTerm.getNumVal(t) of
                           SOME(A.int_num(n,_),_) => 
                             tableVal(HashTable.mkTable(SemanticValues.hashVal, valEq) (n,Data.GenEx("Failed table creation")))
                         | _ => primError("Wrong type of argument given to "^N.makeTableFun_name^".\nA positive integer or a list of pairs was expected,\n"^
                                          "but the given term was: "^(AT.toStringDefault(t))))
       | _ => primError("Wrong type of argument given to "^N.makeTableFun_name^".\nA positive integer or a list of pairs was expected,\n"^
                        "but the given argument was: "^(valLCTypeAndString v)))
  | makeTableFun(vals,_,_) = primError(wrongArgNumber(N.makeTableFun_name,length(vals),1))

fun isListVal(listVal(_)) = true
  | isListVal(_) = false

fun addTablePrimBFun(v1,v2,_,_) = 
     (case v1 of
         tableVal(ht) => 
            let fun addBinding(listVal([first,second]),_) = HashTable.insert ht (first,second)
                  | addBinding(listVal([first,_,second]),_) = HashTable.insert ht (first,second)
                  | addBinding(_,i) = primError("Invalid type of binding given in the second argument to "^N.addTableFun_name)
                fun addBindings(bindings) = Basic.appWithIndex(addBinding,bindings)
            in
               (case v2 of
                   listVal(L as [v1,v2,v3]) => if isListVal(v1) andalso isListVal(v2) andalso isListVal(v3) then addBindings(L) else addBinding(listVal(L),1)
                 | listVal(L as [v1,v2]) => if isListVal(v1) andalso isListVal(v2) andalso not(isStringVal(v1)) then addBindings(L) else addBinding(listVal(L),1)
                 | listVal(vals) => addBindings(vals)
                 | _ => primError(wrongArgKind(N.addTableFun_name,2,listLCType,v2)));
                unitVal
            end
      | _ => primError(wrongArgKind(N.addTableFun_name,1,tableLCType,v1)))

fun isMetaIdentifier(v,T,F) = if isMetaId(v) then T else F

fun removeMapPrimBFun(v1,v2,_,_) = 
     (case v1 of
         mapVal(m) => 
           (case (SOME(Maps.remove(m,v2)) handle _ => NONE) of
               SOME(m',_) => mapVal(m')
             | _ => v1)
       | _ => primError(wrongArgKind(N.removeMapFun_name,1,mapLCType,v1)))

fun applySubToVal(sub,v) = 
     (case coerceValIntoTerm(v) of 
          SOME(t) =>  termVal(AT.applySub(sub,t))
        | _ => (case coerceValIntoProp(v) of
                   SOME(p) => propVal(P.applySub(sub,p))
                 | _ => (case v of 
                            listVal(vals) => applySubToValLstNoPos(sub,vals)
                          | _ => evError("Substitution applied to an argument of the wrong type; " ^ (expect(termLCType,v)), NONE))))

fun mapToValuesPrimBFun(v1,v2,env,ab) = 
        (case v1 of
            mapVal(m) => 
              (case v2 of
                    primUFunVal(f,{name,...}) => let val m' = Maps.mapToValues(fn x => f(x,env,ab),m)
                                                 in
                                                   mapVal(m')
                                                 end
                  | funVal(f,string,_) => let val m' = Maps.mapToValues(fn x => f([x],env,ab),m)
                                          in
                                            mapVal(m')
                                          end
                  | termConVal(regFSym(some_fsym)) => let fun f(v) = (case coerceValIntoTerm(v) of
                                                                         SOME(t) => termVal(applyTermConstructorNoPos(D.fsymName(some_fsym),[t]))
                                                                       | _ => primError("Incorrect application of " ^ N.mapToValuesFun_name ^ ": " ^
                                                                                        "term constructor " ^ (MS.name(D.fsymName(some_fsym))) ^ 
                                                                                        " applied to the non-term value: " ^ (prettyValToString v)))

                                                          val m' = Maps.mapToValues(f,m)
                                                      in
                                                        mapVal(m')
                                                      end
                  | mapVal(M) => let fun f(v) = (case Maps.find(M,v) of
                                                     SOME(res) => res
                                                   | _ => primError("Incorrect application of " ^  N.mapToValuesFun_name ^ ": failed map application: no such key in the map: " ^ 
                                                                   (valLCTypeAndString v)))
                                     val m' = Maps.mapToValues(f,m)
                                 in
                                     mapVal(m')
                                 end
                  | subVal(sub) => let fun f(v) = applySubToVal(sub,v)
                                       val m' = Maps.mapToValues(f,m)
                                   in
                                      mapVal(m')
                                   end
                  | _ => let val m' = Maps.mapToValues(fn x => evalClosure(v2,[x],ab,NONE),m)
                         in
                           mapVal(m')
                         end)
       | _ => primError(wrongArgKind(N.mapToValuesFun_name,1,mapLCType,v1)))

fun mapToKeyValuesPrimBFun(v1,v2,env,ab) = 
        (case v1 of
            mapVal(m) => 
              (case v2 of
                    primUFunVal(f,{name,...}) => let val m' = Maps.mapToKeyValuePairs(fn (x,y) => f(listVal([x,y]),env,ab),m)
                                                 in
                                                   mapVal(m')
                                                 end
                  | funVal(f,string,_) => let val m' = Maps.mapToKeyValuePairs(fn (x,y) => f([listVal([x,y])],env,ab),m)
                                          in
                                            mapVal(m')
                                          end
                  | mapVal(M) => let fun f(v as (x,y)) = 
                                              (case Maps.find(M,listVal([x,y])) of
                                                     SOME(res) => res
                                                   | _ => primError("Incorrect application of " ^  N.mapToKeyValuesFun_name ^ ": failed map application: no such key in the map: " ^ 
                                                                   (valLCTypeAndString (listVal([x,y])))))
                                     val m' = Maps.mapToKeyValuePairs(f,m)
                                 in
                                     mapVal(m')
                                 end
                  | _ => let val m' = Maps.mapToKeyValuePairs(fn (x,y) => evalClosure(v2,[listVal([x,y])],ab,NONE),m)
                         in
                           mapVal(m')
                         end)
       | _ => primError(wrongArgKind(N.mapToKeyValuesFun_name,1,mapLCType,v1)))

fun applyToKeyValuesPrimBFun(v1,v2,env,ab) = 
        (case v1 of
            mapVal(m) => 
              (case v2 of
                    primUFunVal(f,{name,...}) => let fun g(x,y) = let val _ = f(listVal([x,y]),env,ab)
                                                                   in () end
                                                     val _ = Maps.applyToKeyValuePairs(g,m)
                                                 in
                                                   unitVal
                                                 end
                  | funVal(f,string,_) => let val _ = Maps.applyToKeyValuePairs(fn (x,y) => (f([listVal([x,y])],env,ab);()),m)
                                          in
                                            unitVal
                                          end
                  | mapVal(M) => let fun f(v as (x,y)) = 
                                              (case Maps.find(M,listVal([x,y])) of
                                                     SOME(res) => ()
                                                   | _ => primError("Incorrect application of " ^  N.applyToKeyValuesFun_name ^ ": failed map application: no such key in the map: " ^ 
                                                                   (valLCTypeAndString (listVal([x,y])))))
                                     val m' = Maps.applyToKeyValuePairs(f,m)
                                 in
                                    unitVal
                                 end
                  | _ => let val m' = Maps.applyToKeyValuePairs(fn (x,y) => (evalClosure(v2,[listVal([x,y])],ab,NONE);()),m)
                         in
                           unitVal
                         end)
       | _ => primError(wrongArgKind(N.applyToKeyValuesFun_name,1,mapLCType,v1)))

fun mapFoldlFun(vals as [v1,v2,v3],env,ab) = 
        (case v2 of
            mapVal(m) => 
              (case v1 of
                    funVal(f,string,_) => let val res = Maps.foldl(fn (k,v,x) => f([listVal([k,v,x])],env,ab),v3,m)
                                          in
                                            res
                                          end
                 | _ => Maps.foldl(fn (k,v,x) => evalClosure(v1,[k,v,x],ab,NONE),v3,m))
          | _ => primError(wrongArgKind(N.mapFoldlFun_name,2,mapLCType,v1)))

fun mapSizePrimUFun(v,_,_) = 
     (case v of
         mapVal(m) => termVal(AthTerm.makeNumTerm(A.int_num(Maps.size(m),ref "")))
       | _ => primError(wrongArgKind(N.mapSizeFun_name,1,mapLCType,v)))

fun mapKeysPrimUFun(v,_,_) = 
     (case v of
         mapVal(m) => listVal(Maps.listKeys(m))
       | _ => primError(wrongArgKind(N.mapKeysFun_name,1,mapLCType,v)))

fun mapValuesPrimUFun(v,_,_) = 
     (case v of
         mapVal(m) => listVal(Maps.listValues(m))
       | _ => primError(wrongArgKind(N.mapValuesFun_name,1,mapLCType,v)))

fun mapKeyValuesPrimUFun(v,_,_) = 
     (case v of
         mapVal(m) => listVal(map (fn (x,y) => listVal([x,y])) (Maps.listKeyValuePairs m))
       | _ => primError(wrongArgKind(N.mapKeyValuesFun_name,1,mapLCType,v)))

fun mapApplyPrimBFun(v1,v2,_,_) = 
     (case v1 of
         mapVal(m) => 
             (case Maps.find(m,v2) of
                SOME(res) => res
              | _ => primError("Failed use of " ^ (N.mapApplyFun_name)   ^ ": no such key in the map: " ^ (valLCTypeAndString v2)))
       | _ => primError(wrongArgKind(N.mapApplyFun_name,1,mapLCType,v1)))

fun addMapPrimBFun(v1,v2,_,_) = 
     (case v1 of
         mapVal(m) => 
            let fun getBinding(listVal([first,second])) = (first,second)
                  | getBinding(listVal([first,_,second])) = (first,second)
                  | getBinding(_) = primError("Invalid type of binding given in the second argument to "^N.addMapFun_name)
		fun getBindings([],res) = rev(res)
                  | getBindings(b::more,res) = getBindings(more,(getBinding b)::res)
                fun addBindings(bindings) = let val bindings = getBindings(bindings,[])
                                            in
                                               Maps.insertLst(m,bindings)
                                            end
            in
               (case v2 of
                   mapVal(m') => SV.mapVal(Maps.foldl((fn (k,v,m) => Maps.insert(m,k,v)),m,m'))
                 | listVal(key_value_pairs) => let val new_map = addBindings(key_value_pairs)
                                               in
                                                  SV.mapVal(new_map)
                                               end
                 | _ => primError(wrongArgKind(N.addMapFun_name,2,listLCType,v2)))
            end
      | _ => primError(wrongArgKind(N.addTableFun_name,1,mapLCType,v1)))

fun makeMapFromListPrimUFun(v,_,_) = 
            let fun getBinding(listVal([first,second])) = (first,second)
                  | getBinding(listVal([first,_,second])) = (first,second)
                  | getBinding(_) = primError("Invalid type of binding given in the second argument to "^N.makeMapFromListFun_name)
		fun getBindings([],res) = rev(res)
                  | getBindings(b::more,res) = getBindings(more,(getBinding b)::res)
                fun addBindings(m,bindings) = Maps.insertLst(m,getBindings(bindings,[]))
            in
               (case v of
                   listVal(key_value_pairs) => SV.mapVal(addBindings(Maps.makeMap(SV.compare),key_value_pairs))
                 | _ => primError(wrongArgKind(N.makeMapFromListFun_name,2,listLCType,v)))
            end

fun removeTablePrimBFun(v1,v2,_,_) = 
     (case v1 of
         tableVal(ht) => ((HashTable.remove ht v2) handle _ => primError("Failed application of "^N.removeTableFun_name^
                                                                         ".\nThere is no such key in the table: " ^ (valLCTypeAndString v2)))
      | _ => primError(wrongArgKind(N.addTableFun_name,1,tableLCType,v1)))

fun findTablePrimBFun(v1,v2,_,_) = 
     (case v1 of
         tableVal(ht) => (case (HashTable.find ht v2) of
                             SOME(res) => res
                           | _ => primError("Failed table look-up:\nno such key in the table: " ^ (valLCTypeAndString v2)))
      | _ => primError(wrongArgKind(N.findTableFun_name,1,tableLCType,v1)))

fun findMapPrimBFun(v1,v2,_,_) = 
     (case v1 of
         mapVal(m) => (case Maps.find(m,v2) of
                             SOME(res) => res
                           | _ => primError("Failed map look-up:\nno such key in the map: " ^ (valLCTypeAndString v2)))
      | _ => primError(wrongArgKind(N.findMapFun_name,1,mapLCType,v1)))

fun tableSizePrimUFun(v,_,_) =
     (case v of
          tableVal(ht) => termVal(AthTerm.makeNumTerm(A.int_num(HashTable.numItems(ht),ref "")))
        | _ => primError(wrongArgKind(N.tableSizeFun_name,1,tableLCType,v)))

fun tableClearPrimUFun(v,_,_) =
     (case v of
          tableVal(ht) => (HashTable.clear(ht);unitVal)
        | _ => primError(wrongArgKind(N.tableClearFun_name,1,tableLCType,v)))

fun tableToStringPrimUFun(v,_,_) =
     (case v of
          tableVal(ht) => MLStringToAthString(tableToString(ht))
        | _ => primError(wrongArgKind(N.tableToStringFun_name,1,tableLCType,v)))

fun tableToListPrimUFun(v,_,_) =
     (case v of
          tableVal(ht) => let val list_of_pairs = HashTable.listItemsi(ht)
                              val list_of_lists = map (fn (v1,v2) => listVal([v1,v2])) list_of_pairs
                          in
                            listVal(list_of_lists)
                          end
        | _ => primError(wrongArgKind(N.tableToListFun_name,1,tableLCType,v)))

fun isSubPrimUFun(subVal(_),_,_) = true_val
  | isSubPrimUFun(_,_,_) = false_val

fun isTermFun([v],(env,_),_) = 
        (case coerceValIntoTerm(v) of SOME(_) => true_val | _ => false_val)
  | isTermFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.isTermFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isTermPrimUFun(v,env,_) = 
        (case coerceValIntoTerm(v) of SOME(_) => true_val | _ => false_val)
 
fun isMetaIdFun([v],(env,_),_) = isMetaIdentifier(v,true_val,false_val)
  | isMetaIdFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.isMetaIdFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isMetaIdPrimUFun(v,env,_) = 
      (case coerceValIntoTerm(v) of 
          SOME(t) => (case AthTerm.isIdeConstant(t) of NONE => false_val | _ => true_val)
        | _ => false_val)

fun isCharFun([charVal(_)],_,_) = true_val 
  | isCharFun([_],_,_) = false_val
  | isCharFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.isCharFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isCharPrimUFun(charVal(_),_,_) = true_val 
  | isCharPrimUFun(_) = false_val

fun isListFun([v],_,_) = MLBoolToAth(isListVal(v))
  | isListFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.isListFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isListPrimUFun(listVal(_),_,_) = true_val 
  | isListPrimUFun(_) = false_val

fun charOrdFun([charVal(c)],_,_) = termVal(AthTerm.makeNumTerm(A.int_num(c,ref "")))
  | charOrdFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.charOrdFun_name,1,charLCType,v),getPosOpt(pos_ar,2))
  | charOrdFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.charOrdFun_name,length(vals),1), getPosOpt(pos_ar,0))

fun charOrdPrimUFun(charVal(c),_,_) = termVal(AthTerm.makeNumTerm(A.int_num(c,ref "")))
  | charOrdPrimUFun(v,_,_) = primError(wrongArgKind(N.charOrdFun_name,1,charLCType,v))

fun makeCharFun([termVal(t)],_,{pos_ar,file}) =
      (case AthTerm.getNumVal(t) of
          SOME(A.int_num(i,_),false) => if i >= 0 andalso i <= 127 then charVal(i)
                                              else evError("Illegal character code",getPosOpt(pos_ar,2))
        | _ => evError("Illegal character code",getPosOpt(pos_ar,2)))
  | makeCharFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.makeCharFun_name,1,termLCType,v),getPosOpt(pos_ar,2))
  | makeCharFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.makeCharFun_name,length(vals),1), getPosOpt(pos_ar,0))

fun makeCharPrimUFun(termVal(t),_,_) = 
      (case AthTerm.getNumVal(t) of
          SOME(A.int_num(i,_),false) => if i >= 0 andalso i <= 127 then charVal(i)
                                              else primError("Illegal character code")
        | _ => primError("Illegal character code"))
  | makeCharPrimUFun(v,_,_) = primError(wrongArgKind(N.makeCharFun_name,1,termLCType,v))

fun compareCharsFun([charVal(c1),charVal(c2)],_,_) = 
     if c1 = c2 then termVal(AthTerm.makeIdeConstant("equal"))
      else if c1 < c2 then termVal(AthTerm.makeIdeConstant("less"))
           else termVal(AthTerm.makeIdeConstant("greater"))
  | compareCharsFun([charVal(_),v],_,{pos_ar,file}) = 
      evError(wrongArgKind(N.compareCharsFun_name,2,charLCType,v),getPosOpt(pos_ar,3))
  | compareCharsFun([v,_],_,{pos_ar,file}) = 
      evError(wrongArgKind(N.compareCharsFun_name,1,charLCType,v),getPosOpt(pos_ar,2))
  | compareCharsFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.compareCharsFun_name,length(vals),2), getPosOpt(pos_ar,0))

fun compareCharsPrimBFun(charVal(c1),charVal(c2),_,_) = 
     if c1 = c2 then termVal(AthTerm.makeIdeConstant("equal"))
      else if c1 < c2 then termVal(AthTerm.makeIdeConstant("less"))
           else termVal(AthTerm.makeIdeConstant("greater"))
  | compareCharsPrimBFun(charVal(_),v,_,_) = 
      primError(wrongArgKind(N.compareCharsFun_name,2,charLCType,v))
  | compareCharsPrimBFun(v,_,_,_) = primError(wrongArgKind(N.compareCharsFun_name,1,charLCType,v))
      
fun orderToString(LESS) = "less"
  | orderToString(GREATER) = "greater"
  | orderToString(_) = "equal"

fun compareStringsPrimBFun(v1,v2,_,_) = 
  (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
      (SOME(str1),SOME(str2)) => termVal(AthTerm.makeIdeConstant(orderToString(String.compare(str1,str2))))
    | (_,SOME(_)) => primError(wrongArgKind(N.compareStringsFun_name,1,stringLCType,v1))
    | (SOME(_),_) => primError(wrongArgKind(N.compareStringsFun_name,2,stringLCType,v2))
    | _ => primError(wrongArgKind(N.compareStringsFun_name,1,stringLCType,v1)))

fun varToStringFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoTerm(v) of 
         SOME(t) => (case AT.isVarOpt(t) of
                        NONE => evError(wrongArgKind(N.varToStringFun_name,1,varLCType,v),getPosOpt(pos_ar,2))
                      | SOME(var) => MLStringToAthString(AthTermVar.name(var)))
       | _ => evError(wrongArgKind(N.varToStringFun_name,1,varLCType,v),getPosOpt(pos_ar,2)))
  | varToStringFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.varToStringFun_name,length(vals),1),getPosOpt(pos_ar,0))
                                                   
fun varToStringPrimUFun(v,env,_) = 
      (case coerceValIntoTerm(v) of 
         SOME(t) => (case AT.isVarOpt(t) of
                        NONE => primError(wrongArgKind(N.varToStringFun_name,1,varLCType,v))
                      | SOME(var) => MLStringToAthString(AthTermVar.name(var)))
       | _ => primError(wrongArgKind(N.varToStringFun_name,1,varLCType,v)))

fun stringToVarFun(vals,_,_) = 
     let fun error(str) = primError("Invalid argument given to "^N.stringToVarFun_name^"---the\nname '"^
                                  str^"' cannot be used as a variable.")
         fun error2(str1,str2) = primError("Invalid arguments given to "^N.stringToVarFun_name^"---the\nname '"^
                                            str1^":"^str2^"' cannot be used as a variable.")
     in
       (case vals of 
           [v] => (case isStringValConstructive(v) of
                     SOME(str) => let val atv_opt: ATV.ath_term_var option = Terms.stringsToAthVar([str])
                                  in
                                    (case atv_opt of
                                        SOME(av) => termVal(AthTerm.makeVar(av))
                                      | _ => error(str))
                                  end
                   | _ => primError(wrongArgKind(N.stringToVarFun_name,1,stringLCType,v)))
        | [v1,v2] => (case (isStringValConstructive(v1),isStringValConstructive(v2)) of 
                         (SOME(str1),SOME(str2)) => (case Terms.stringsToAthVar([str1,str2]) of
                                                          SOME(av) => termVal(AthTerm.makeVar(av))
                                                        | _ => error2(str1,str2))
                        | (SOME(_),_) => primError(wrongArgKind(N.stringToVarFun_name,1,stringLCType,v1))
                        | (_,SOME(_)) => primError(wrongArgKind(N.stringToVarFun_name,1,stringLCType,v1))
                        | _ => primError(wrongArgKind(N.stringToVarFun_name,1,stringLCType,v1)))
        | _ => primError(wrongArgNumber(N.stringToVarFun_name,length(vals),1)))
     end

fun stringToVarPrimUFun(v,_,_) = 
     let fun error(str) = primError("Invalid argument given to "^N.stringToVarFun_name^"---the\nname '"^
                                    str^"' cannot be used as a variable.")
         fun error2(str1,str2) = primError("Invalid arguments given to "^N.stringToVarFun_name^"---the\nname '"^
                                            str1^":"^str2^"' cannot be used as a variable.")
     in
        (case isStringValConstructive(v) of
                     SOME(str) => let val atv_opt: ATV.ath_term_var option = Terms.stringsToAthVar([str])
                                  in
                                    (case atv_opt of
                                        SOME(av) => termVal(AthTerm.makeVar(av))
                                      | _ => error(str))
                                  end
                   | _ => primError(wrongArgKind(N.stringToVarFun_name,1,stringLCType,v)))
     end

exception NonNumericOperand of AT.term * int

fun getSignedInt(i,neg) = if neg then Int.~(i) else i
fun getSignedReal(r,neg) = if neg then Real.~(r) else r

fun doNumOpEqualityComparison(t1,t2) = 
 let val _ = () 
 in
 (case (AthTerm.getNumVal(t1),AthTerm.getNumVal(t2)) of
        (SOME(A.int_num(a1,_),neg1),SOME(A.int_num(a2,_),neg2)) =>
           let val (a1',a2') = (getSignedInt(a1,neg1),getSignedInt(a2,neg2))
	       val res = a1' = a2' 
           in
               MLBoolToAth(res)
           end
      | (SOME(A.int_num(a1,_),neg1),SOME(A.real_num(a2,_),neg2)) =>
         let val (a1',a2':Real.real) = (getSignedInt(a1,neg1),getSignedReal(a2,neg2))
             val a1'':Real.real = Real.fromInt(a1')
	     val res:bool = Real.==(a1'',a2')
         in
            MLBoolToAth(res)
         end
      | (SOME(A.real_num(a1,_),neg1),SOME(A.int_num(a2,_),neg2)) =>
         let val (a1',a2') = (getSignedReal(a1,neg1),getSignedInt(a2,neg2))
	     val res = Real.==(a1',Real.fromInt(a2'))
         in
            MLBoolToAth(res)
         end
      | (SOME(A.real_num(a1,_),neg1),SOME(A.real_num(a2,_),neg2)) =>
         let val (a1',a2') = (getSignedReal(a1,neg1),getSignedReal(a2,neg2))
	     val res = Real.==(a1',a2')
         in
            MLBoolToAth(res)
         end
      | (NONE,_) => raise NonNumericOperand(t1,1)
      | (_,NONE) => raise NonNumericOperand(t2,2))
 end

fun doNumOpOnSignedComparison(t1,t2,fInt,fReal) = 
 let fun getSignedInt(i,neg) = if neg then Int.~(i) else i
     fun getSignedReal(r,neg) = if neg then Real.~(r) else r
 in
 (case (AthTerm.getNumVal(t1),AthTerm.getNumVal(t2)) of
        (SOME(A.int_num(a1,_),neg1),SOME(A.int_num(a2,_),neg2)) =>
           let val (a1',a2') = (getSignedInt(a1,neg1),getSignedInt(a2,neg2))
	       val res = fInt(a1',a2') 
           in
               MLBoolToAth(res)
           end
      | (SOME(A.int_num(a1,_),neg1),SOME(A.real_num(a2,_),neg2)) =>
         let val (a1',a2':Real.real) = (getSignedInt(a1,neg1),getSignedReal(a2,neg2))
             val a1'':Real.real = Real.fromInt(a1')
	     val res:bool = fReal(a1'',a2')
         in
            MLBoolToAth(res)
         end
      | (SOME(A.real_num(a1,_),neg1),SOME(A.int_num(a2,_),neg2)) =>
         let val (a1',a2') = (getSignedReal(a1,neg1),getSignedInt(a2,neg2))
	     val res = fReal(a1',Real.fromInt(a2'))
         in
            MLBoolToAth(res)
         end
      | (SOME(A.real_num(a1,_),neg1),SOME(A.real_num(a2,_),neg2)) =>
         let val (a1',a2') = (getSignedReal(a1,neg1),getSignedReal(a2,neg2))
	     val res = fReal(a1',a2') 
         in
            MLBoolToAth(res)
         end
      | (NONE,_) => raise NonNumericOperand(t1,1)
      | (_,NONE) => raise NonNumericOperand(t2,2))
 end

fun doNumOpOnSignedANums(t1,t2,fInt,fReal) = 
 let fun getSignedInt(i,neg) = if neg then Int.~(i) else i
     fun getSignedReal(r,neg) = if neg then Real.~(r) else r
 in
 (case (AthTerm.getNumVal(t1),AthTerm.getNumVal(t2)) of
        (SOME(A.int_num(a1,_),neg1),SOME(A.int_num(a2,_),neg2)) =>
           let val (a1',a2') = (getSignedInt(a1,neg1),getSignedInt(a2,neg2))
	       val res = fInt(a1',a2') 
	       val t = if res < 0 then AthTerm.makeNumTerm(A.int_num(~res,ref ""))
	               else AthTerm.makeNumTerm(A.int_num(res,ref ""))
           in
	      if (res < 0) then
                 termVal(AthTerm.doUnaryMinusOnLiteral(t,true))
              else termVal(t)
	      
           end
      | (SOME(A.int_num(a1,_),neg1),SOME(A.real_num(a2,_),neg2)) =>
         let val (a1',a2':Real.real) = (getSignedInt(a1,neg1),getSignedReal(a2,neg2))
             val a1'':Real.real = Real.fromInt(a1')
	     val res:Real.real = fReal(a1'',a2')
	     val t = if res < 0.0 then AthTerm.makeNumTerm(A.real_num(~res,ref "")) else AthTerm.makeNumTerm(A.real_num(res,ref ""))
         in
	   if (res < 0.0) then
              termVal(AthTerm.doUnaryMinusOnLiteral(t,false))
           else termVal(t)
         end
      | (SOME(A.real_num(a1,_),neg1),SOME(A.int_num(a2,_),neg2)) =>
         let val (a1',a2') = (getSignedReal(a1,neg1),getSignedInt(a2,neg2))
	     val res = fReal(a1',Real.fromInt(a2'))
	     val t = if res < 0.0 then AthTerm.makeNumTerm(A.real_num(~res,ref "")) else AthTerm.makeNumTerm(A.real_num(res,ref ""))
         in
	   if (res < 0.0) then
              termVal(AthTerm.doUnaryMinusOnLiteral(t,false))
           else
            termVal(t)
         end
      | (SOME(A.real_num(a1,_),neg1),SOME(A.real_num(a2,_),neg2)) =>
         let val (a1',a2') = (getSignedReal(a1,neg1),getSignedReal(a2,neg2))
	     val res = fReal(a1',a2') 
	     val t = if res < 0.0 then AthTerm.makeNumTerm(A.real_num(~res,ref "")) else AthTerm.makeNumTerm(A.real_num(res,ref ""))
         in
	   if (res < 0.0) then
                 termVal(AthTerm.doUnaryMinusOnLiteral(t,false))
           else
            termVal(t)
         end
      | (NONE,_) => raise NonNumericOperand(t1,1)
      | (_,NONE) => raise NonNumericOperand(t2,2))
 end

fun PrimPlusFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.+,Real.+))
				handle NonNumericOperand(t,i) =>
				 evError("Wrong app of prim-plus",NONE)))

fun PrimMinusFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.-,Real.-))
				handle NonNumericOperand(t,i) =>
				 evError("Wrong app of prim-plus",NONE)))

fun PrimGreaterFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedComparison(t1,t2,Int.>,Real.>))
				handle NonNumericOperand(t,i) =>
				 primError("Incorrect application of "^N.greaterFun_name)))

fun plusFun([v1,v2],(env,_),{pos_ar,file}) = 
 let val msg = "Could not successfully apply "^N.plusFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.+,Real.+))
				handle NonNumericOperand(t,i) =>
				 evError(wrongTermKind(N.plusFun_name,i,"numeric term",t),
					 getPosOpt(pos_ar,1+i))
			      | _ => evError(msg,getPosOpt(pos_ar,0)))
  | (SOME(_),_) => evError(wrongArgKind(N.plusFun_name,2,termLCType,v2),
                                        getPosOpt(pos_ar,3))
  | (_,_) => evError(wrongArgKind(N.plusFun_name,1,termLCType,v1),
                                        getPosOpt(pos_ar,2)))
 end
  | plusFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.plusFun_name,length(vals),2),
						  getPosOpt(pos_ar,0))

fun plusPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.+,Real.+))
				handle NonNumericOperand(t,i) =>
				 primError("Incorrect application of plus"))
  | _ => primError(wrongArgKind(N.plusFun_name,1,termLCType,v1)))

fun plusPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.+,Real.+))
				handle NonNumericOperand(t,i) =>
				 primError("Incorrect application of plus"))
  | p => (case p of
           (SOME(_),_) => primError(wrongArgKind(N.plusFun_name,2,termLCType,v2))
          | _ => primError(wrongArgKind(N.plusFun_name,1,termLCType,v1))))

fun sqrtPrimUFun(v,env,_) = 
 (case coerceValIntoTerm(v) of
    SOME(t) => (case AthTerm.getNumVal(t) of 
                   SOME(A.real_num(a,_),neg) => let val r = getSignedReal(a,neg)
                                                    val res = Real.Math.sqrt(r)
                                                in
						   termVal(AthTerm.makeNumTerm(A.real_num(res,ref "")))
                                                end
                | SOME(A.int_num(a,_),neg) => let val i = getSignedInt(a,neg)
                                                  val r = Real.fromInt(i)
                                                  val res = Real.Math.sqrt(r)
                                              in
                                                termVal(AthTerm.makeNumTerm(A.real_num(res,ref "")))
                                              end)
  | _ => primError(wrongArgKind(N.sqrtFun_name,1,termLCType,v)))

fun log10PrimUFun(v,env,_) = 
 (case coerceValIntoTerm(v) of
    SOME(t) => (case AthTerm.getNumVal(t) of 
                   SOME(A.real_num(a,_),neg) => let val r = getSignedReal(a,neg)
                                                    val res = Real.Math.log10(r)
                                                in
						   termVal(AthTerm.makeNumTerm(A.real_num(res,ref "")))
                                                end
                | SOME(A.int_num(a,_),neg) => let val i = getSignedInt(a,neg)
                                                  val r = Real.fromInt(i)
                                                  val res = Real.Math.log10(r)
                                              in
                                                termVal(AthTerm.makeNumTerm(A.real_num(res,ref "")))
                                              end) 
  | _ => primError(wrongArgKind(N.log10Fun_name,1,termLCType,v)))

fun floorPrimUFun(v,env,_) = 
 (case coerceValIntoTerm(v) of
    SOME(t) => (case AthTerm.getNumVal(t) of 
                   SOME(A.real_num(a,_),neg) => let val r = getSignedReal(a,neg)
                                                    val res = floor(r)
                                                in
						   termVal(AthTerm.makeNumTerm(A.int_num(res,ref "")))
                                                end
                | SOME(A.int_num(a,_),neg) => let val i = getSignedInt(a,neg)
                                              in
                                                termVal(AthTerm.makeNumTerm(A.int_num(i,ref "")))
                                              end)
  | _ => primError(wrongArgKind(N.floorFun_name,1,termLCType,v)))

fun ceilPrimUFun(v,env,_) = 
 (case coerceValIntoTerm(v) of
    SOME(t) => (case AthTerm.getNumVal(t) of 
                   SOME(A.real_num(a,_),neg) => let val r = getSignedReal(a,neg)
                                                    val res = ceil(r)
                                                in
						   termVal(AthTerm.makeNumTerm(A.int_num(res,ref "")))
                                                end
                | SOME(A.int_num(a,_),neg) => let val i = getSignedInt(a,neg)
                                              in
                                                termVal(AthTerm.makeNumTerm(A.int_num(i,ref "")))
                                              end)
  | _ => primError(wrongArgKind(N.ceilFun_name,1,termLCType,v)))


fun lnPrimUFun(v,env,_) = 
 (case coerceValIntoTerm(v) of
    SOME(t) => (case AthTerm.getNumVal(t) of 
                   SOME(A.real_num(a,_),neg) => let val r = getSignedReal(a,neg)
                                                    val res = Real.Math.ln(r)
                                                in
						   termVal(AthTerm.makeNumTerm(A.real_num(res,ref "")))
                                                end
                | SOME(A.int_num(a,_),neg) => let val i = getSignedInt(a,neg)
                                                  val r = Real.fromInt(i)
                                                  val res = Real.Math.ln(r)
                                              in
                                                termVal(AthTerm.makeNumTerm(A.real_num(res,ref "")))
                                              end) 
  | _ => primError(wrongArgKind(N.lnFun_name,1,termLCType,v)))

fun minusFun(vals,_,_) = 
 (case vals of 
 [v1,v2] =>
 let val msg = "Could not successfully apply "^N.minusFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
     val real_minus = Real.-
     val int_minus = Int.-
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,int_minus,real_minus))
			      handle NonNumericOperand(t,i) =>
				 primError(wrongArgKind(N.minusFun_name,i,"numeric term",termVal(t)))
			      | _ => primError("Subtraction error"))
  | (SOME(_),_) => primError(wrongArgKind(N.minusFun_name,2,"numeric term",v2))
  | (_,_) => primError(wrongArgKind(N.minusFun_name,1,"numeric term",v1)))
 end
| [v] =>  (case coerceValIntoTerm(v) of 
              SOME(t) => (case AthTerm.getNumVal(t) of
                             SOME(A.int_num(a,_),is_neg) => 
                                 if is_neg then 
                                    termVal(AthTerm.makeNumTerm(A.int_num(a,ref "")))
                                 else 
                                    termVal(AthTerm.makeNumTerm(A.int_num(~a,ref "")))
                           | SOME(A.real_num(a,_),is_neg) => 
                                 if is_neg then 
                                   termVal(AthTerm.makeNumTerm(A.real_num(a,ref "")))
                                 else termVal(AthTerm.makeNumTerm(A.real_num(~a,ref ""))))
            | _ => primError(wrongArgKind(N.minusFun_name,1,termLCType,v)))

  | _ => primError(wrongArgNumber(N.minusFun_name,length(vals),2)))

fun minusPrimBFun(v1,v2,env,_) = 
 let val msg = "Could not successfully apply "^N.minusFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
     val real_minus = Real.-
     val int_minus = Int.-
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,int_minus,real_minus))
			      handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.plusFun_name,i,"numeric term",t))
			      | _ => primError(msg))
  | (SOME(_),_) => primError(wrongArgKind(N.minusFun_name,2,termLCType,v2))
  | (_,_) => primError(wrongArgKind(N.minusFun_name,1,termLCType,v1)))
 end

fun minusPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.-,Real.-))
				handle NonNumericOperand(t,i) =>
				 primError("Incorrect application of "^N.minusFun_name))
  | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.minusFun_name,2,termLCType,v2))
           | _ => primError(wrongArgKind(N.minusFun_name,1,termLCType,v1))))          

fun timesFun([v1,v2],(env,_),{pos_ar,file}) = 
 let val msg = "Could not successfully apply "^N.timesFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
     val real_times = Real.*
     val int_times = Int.*
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,int_times,real_times))
				handle NonNumericOperand(t,i) =>
				 evError(wrongTermKind(N.plusFun_name,i,"numeric term",t),
					 getPosOpt(pos_ar,1+i))
			      | _ => evError(msg,getPosOpt(pos_ar,0)))
  | (SOME(_),_) => evError(wrongArgKind(N.timesFun_name,2,termLCType,v2),
                                        getPosOpt(pos_ar,3))
  | (_,_) => evError(wrongArgKind(N.timesFun_name,1,termLCType,v1),
                                        getPosOpt(pos_ar,2)))
 end
  | timesFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.timesFun_name,length(vals),2),
						  getPosOpt(pos_ar,0))

fun timesPrimBFun(v1,v2,env,_) = 
 let val msg = "Could not successfully apply "^N.timesFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
     val real_times = Real.*
     val int_times = Int.*
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,int_times,real_times))
				handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.plusFun_name,i,"numeric term",t))
			      | _ => primError(msg))
  | (SOME(_),_) => primError(wrongArgKind(N.timesFun_name,2,termLCType,v2))
  | (_,_) => primError(wrongArgKind(N.timesFun_name,1,termLCType,v1)))
 end

fun timesPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedANums(t1,t2,Int.*,Real.* ))
				handle NonNumericOperand(t,i) =>
				 primError("Incorrect application of "^N.timesFun_name))
   | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.timesFun_name,2,termLCType,v2))
           | _ => primError(wrongArgKind(N.timesFun_name,1,termLCType,v1))))

fun divFun([v1,v2],(env,_),{pos_ar,file}) = 
 let val msg = "Could not successfully apply "^N.divFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
     val dbz = "Division by zero"
     val real_div = Real./
     val int_div = Int.div
     fun decide(i,t1,t2) = if Real.==(Real.fromInt(i),0.0) then evError(dbz,getPosOpt(pos_ar,0)) else
					  ((doNumOpOnSignedANums(t1,t2,int_div,real_div))
				  	   handle _ => evError(msg,getPosOpt(pos_ar,0)))
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => (case AthTerm.getNumVal(t2) of 
			       SOME(A.int_num(i,_),_) => decide(i,t1,t2)
                             | SOME(A.real_num(r,_),_) => decide(ceil r,t1,t2)
                             | _ => ((doNumOpOnSignedANums(t1,t2,int_div,real_div))
					handle NonNumericOperand(t,i) =>
					 evError(wrongTermKind(N.plusFun_name,i,"numeric term",t),
						 getPosOpt(pos_ar,1+i))
				      | _ => evError(msg,getPosOpt(pos_ar,0))))
  | (SOME(_),_) => evError(wrongArgKind(N.divFun_name,2,termLCType,v2),
                                        getPosOpt(pos_ar,3))
  | (_,_) => evError(wrongArgKind(N.divFun_name,1,termLCType,v1),
                                        getPosOpt(pos_ar,2)))
 end
  | divFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.divFun_name,length(vals),2),
						  getPosOpt(pos_ar,0))
						  
fun divPrimBFun(v1,v2,env,_) = 
 let val real_div = Real./
     val int_div = Int.div
     fun decide(i,t1,t2) = if Real.==(i,0.0) then primError("Division by zero") else
					  ((doNumOpOnSignedANums(t1,t2,int_div,real_div))
				  	   handle _ => primError("Failed application of "^N.divFun_name))
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => (case AthTerm.getNumVal(t2) of 
			       SOME(A.int_num(i,_),_) => decide(Real.fromInt(i),t1,t2)
                             | SOME(A.real_num(r,_),_) => decide(r,t1,t2)
                             | _ => ((doNumOpOnSignedANums(t1,t2,int_div,real_div))
					handle NonNumericOperand(t,i) =>
					 primError(wrongTermKind(N.plusFun_name,i,"numeric term",t))
				      | _ => primError("Failed application of "^N.divFun_name)))
  | p => (case p of
           (SOME(_),_) => primError(wrongArgKind(N.divFun_name,2,termLCType,v2))
         | (_,_) => primError(wrongArgKind(N.divFun_name,1,termLCType,v1))))
 end

fun modFun([v1,v2],(env,_),{pos_ar,file}) = 
 let val msg = "Could not successfully apply "^N.modFun_name^
	       " to the given arguments;\nmost likely there was an overflow."
     val dbz = "Division by zero"
     val real_mod = Real.rem
     val int_mod = Int.mod
     fun decide(i,t1,t2) = if Real.==(i,0.0) then evError(dbz,getPosOpt(pos_ar,0)) else
					  ((doNumOpOnSignedANums(t1,t2,int_mod,real_mod))
				  	   handle _ => evError(msg,getPosOpt(pos_ar,0)))
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => (case AthTerm.getNumVal(t2) of 
			       SOME(A.int_num(i,_),_) => decide(Real.fromInt(i),t1,t2)
                             | SOME(A.real_num(r,_),_) => decide(r,t1,t2)
                             | _ => ((doNumOpOnSignedANums(t1,t2,int_mod,real_mod))
			  		   handle _ => evError(msg,getPosOpt(pos_ar,0))))
  | (SOME(_),_) => evError(wrongArgKind(N.modFun_name,2,termLCType,v2),
                                        getPosOpt(pos_ar,3))
  | (_,_) => evError(wrongArgKind(N.modFun_name,1,termLCType,v1),
                                        getPosOpt(pos_ar,2)))
 end
  | modFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.modFun_name,length(vals),2),
						  getPosOpt(pos_ar,0))

fun modPrimBFun(v1,v2,env,_) = 
 let val real_mod = Real.rem
     val int_mod = Int.mod
     fun decide(i,t1,t2) = if Real.==(i,0.0) then primError("Division by zero") else
					  ((doNumOpOnSignedANums(t1,t2,int_mod,real_mod))
				  	   handle _ => primError("Failed application of "^N.modFun_name))
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => (case AthTerm.getNumVal(t2) of 
			       SOME(A.int_num(i,_),_) => decide(Real.fromInt(i),t1,t2)
                             | SOME(A.real_num(r,_),_) => decide(r,t1,t2)
                             | _ => ((doNumOpOnSignedANums(t1,t2,int_mod,real_mod))
			  		   handle _ => primError("Failed application of "^N.modFun_name)))
  | p => (case p of
           (SOME(_),_) => primError(wrongArgKind(N.modFun_name,2,termLCType,v2))
         | (_,_) => primError(wrongArgKind(N.modFun_name,1,termLCType,v1))))
 end

fun lessFun([v1,v2],(env,_),{pos_ar,file}) = 
 let val msg = "Could not successfully apply "^N.lessFun_name^
	       " to the given arguments;\nmost likely there was an overflow"
 in
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedComparison(t1,t2,Int.<,Real.<))
				handle NonNumericOperand(t,i) =>
				 evError(wrongTermKind(N.lessFun_name,i,"numeric term",t),
					 getPosOpt(pos_ar,1+i))
			      | _ => evError(msg,getPosOpt(pos_ar,0)))
  | (SOME(_),_) => evError(wrongArgKind(N.lessFun_name,2,termLCType,v2),
                                        getPosOpt(pos_ar,3))
  | (_,_) => evError(wrongArgKind(N.lessFun_name,1,termLCType,v1),
                                        getPosOpt(pos_ar,2)))
 end
  | lessFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.lessFun_name,length(vals),2),
						  getPosOpt(pos_ar,0))
fun lessPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedComparison(t1,t2,Int.<,Real.<))
				handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.lessFun_name,i,"numeric term",t))
			      | _ => primError("Failed application of "^N.lessFun_name))
  | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.lessFun_name,2,termLCType,v2))
          | _ =>  primError(wrongArgKind(N.lessFun_name,1,termLCType,v1))))

fun leqPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedComparison(t1,t2,Int.<=,Real.<=))
				handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.lessFun_name,i,"numeric term",t))
			      | _ => primError("Failed application of "^N.lessFun_name))
  | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.lessFun_name,2,termLCType,v2))
          | _ =>  primError(wrongArgKind(N.lessFun_name,1,termLCType,v1))))

fun geqPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedComparison(t1,t2,Int.>=,Real.>=))
				handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.lessFun_name,i,"numeric term",t))
			      | _ => primError("Failed application of "^N.lessFun_name))
  | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.lessFun_name,2,termLCType,v2))
          | _ =>  primError(wrongArgKind(N.lessFun_name,1,termLCType,v1))))

fun greaterPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpOnSignedComparison(t1,t2,Int.>,Real.>))
				handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.lessFun_name,i,"numeric term",t))
			      | _ => primError("Failed application of "^N.greaterFun_name))
  | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.greaterFun_name,2,termLCType,v2))
          | _ =>  primError(wrongArgKind(N.greaterFun_name,1,termLCType,v1))))

fun numEqualPrimBFun(v1,v2,env,_) = 
 (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of
    (SOME(t1),SOME(t2)) => ((doNumOpEqualityComparison(t1,t2))
				handle NonNumericOperand(t,i) =>
				 primError(wrongTermKind(N.numEqualFun_name,i,"numeric term",t))
			      | _ => primError("Failed application of "^N.numEqualFun_name))
  | p => (case p of
            (SOME(_),_) => primError(wrongArgKind(N.numEqualFun_name,2,termLCType,v2))
          | (_,_) => primError(wrongArgKind(N.numEqualFun_name,1,termLCType,v1))))

fun metaIdToStringFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoTerm(v) of 
         SOME(t) => (case AthTerm.isIdeConstant(t) of
                        NONE => evError(wrongArgKind(N.metaIdToStringFun_name,1,varLCType,v),
                                        getPosOpt(pos_ar,2))
                      | SOME(str) => MLStringToAthString(str))
       | _ => evError(wrongArgKind(N.metaIdToStringFun_name,1,varLCType,v),getPosOpt(pos_ar,2)))
  | metaIdToStringFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.metaIdToStringFun_name,length(vals),1),
                                                   getPosOpt(pos_ar,0))

fun metaIdToStringPrimUFun(v,env,_) = 
      (case coerceValIntoTerm(v) of 
         SOME(t) => (case AthTerm.isIdeConstant(t) of
                        NONE => primError(wrongArgKind(N.metaIdToStringFun_name,1,varLCType,v))
                      | SOME(str) => MLStringToAthString(str))
       | _ => primError(wrongArgKind(N.metaIdToStringFun_name,1,varLCType,v)))

fun execCommandFun([v],_,{pos_ar,file}) = 
  (case isStringValConstructive(v) of
      SOME(str) => (OS.Process.system(str);unitVal)
    | _ => evError(wrongArgKind(N.execCommandFun_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  | execCommandFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.execCommandFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun execCommandPrimUFun(v,_,_) = 
  (case isStringValConstructive(v) of
      SOME(str) => (OS.Process.system(str);unitVal)
    | _ => primError(wrongArgKind(N.execCommandFun_name,1,stringLCType,v)))

fun deleteFile1Fun([v],_,{pos_ar,file}) = 
  (case isStringValConstructive(v) of
      SOME(str) => ((OS.FileSys.remove(str);print("\nFile "^str^" was deleted.\n");unitVal)
                    handle _ => (print("\nUnable to delete file "^str^".\n");unitVal))
    | _ => evError(wrongArgKind(N.deleteFile1Fun_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  | deleteFile1Fun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.deleteFile1Fun_name,length(vals),1),getPosOpt(pos_ar,0))

fun deleteFile1PrimUFun(v,_,_) = 
  (case isStringValConstructive(v) of
      SOME(str) => ((OS.FileSys.remove(str);print("\nFile "^str^" was deleted.\n");unitVal)
                    handle _ => (print("\nUnable to delete file "^str^".\n");unitVal))
    | _ => primError(wrongArgKind(N.deleteFile1Fun_name,1,stringLCType,v)))

fun deleteFileFun([v],_,{pos_ar,file}) = 
  (case isStringValConstructive(v) of
      SOME(str) => ((OS.FileSys.remove(str);unitVal)
                    handle _ => unitVal)
    | _ => evError(wrongArgKind(N.deleteFileFun_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  | deleteFileFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.deleteFileFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun deleteFilePrimUFun(v,_,_) = 
  (case isStringValConstructive(v) of
      SOME(str) => ((OS.FileSys.remove(str);unitVal)
                    handle _ => unitVal)
    | _ => primError(wrongArgKind(N.deleteFileFun_name,1,stringLCType,v)))

fun stringToSymbolFun([v],_,{pos_ar,file}) = 
  (case isStringValConstructive(v) of
      SOME(str) => (case stringToSymbolAux(str) of
                       SOME(v) => v
                     | _ => evError("The given string does not represent a function symbol",getPosOpt(pos_ar,2)))
    | _ => evError(wrongArgKind(N.stringToSymbolFun_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  | stringToSymbolFun(vals,_,{pos_ar,file}) = 
        evError(wrongArgNumber(N.stringToSymbolFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun stringToSymbolPrimUFun(v,_,_) = 
  (case isStringValConstructive(v) of
      SOME(str) => 
            (case stringToSymbolAux(str) of
               SOME(v) => v
             | _ => primError("The given string (" ^ str ^ ") does not represent a function symbol"))
    | _ => primError(wrongArgKind(N.stringToSymbolFun_name,1,stringLCType,v)))

fun isQuotedString(str) = 
   let val sz =  String.size(str)
   in
      if Int.<(sz,2) then false  
      else let val (first,last) = (String.sub(str,0),String.sub(str,sz-1))
               val str_char = #"\""
           in
              first = str_char andalso last = str_char
           end
   end

fun stringToMetaIdFun([v],_,{pos_ar,file}) = 
                            (case isStringValConstructive(v) of
                                SOME(str) => let val str' = (if (String.str(String.sub(str,0)) = Names.metaIdPrefix)
                                                             then String.extract(str,1,NONE) else str) handle _ => str
                                                 val _ = print("\nHere is str': "^str'^"\n")
                                             in
                                               if A.canBeId(str') orelse isQuotedString(str') then 
                                                  termVal(AthTerm.makeIdeConstant(str'))
                                               else 
                                                   evError("Invalid argument given to "^N.stringToMetaIdFun_name^
                                                           "---the name "^str'^" cannot be used as an identifier",
                                                           getPosOpt(pos_ar,2))
                                             end
                              | _ => evError(wrongArgKind(N.stringToMetaIdFun_name,1,stringLCType,v),
                                             getPosOpt(pos_ar,2)))
  | stringToMetaIdFun(vals,_,{pos_ar,file}) = 
       evError(wrongArgNumber(N.stringToMetaIdFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun stringToMetaIdPrimUFun(v,_,_) = 
                            (case isStringValConstructive(v) of
                                SOME(str) => let val str' = (if (String.str(String.sub(str,0)) = Names.metaIdPrefix)
                                                             then String.extract(str,1,NONE) else str) handle _ => str
                                             in
                                               if A.canBeId(str') orelse isQuotedString(str') then 
                                                termVal(AthTerm.makeIdeConstant(str'))
                                               else
                                                primError("Invalid argument given to "^N.stringToMetaIdFun_name^
                                                        "---the name "^str'^" cannot be used as an identifier")
                                             end
                              | _ => primError(wrongArgKind(N.stringToMetaIdFun_name,1,stringLCType,v)))
                                                   
fun getSigFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoTermCon(v) of
          SOME(SV.regFSym(afs)) => (case Data.getSignature(Data.fsymName afs) of
                                      (arg_sorts,output_sort,_,has_pred_based_sorts) => listVal((map (fn x => MLStringToAthString(F.toStringDefault(x))) arg_sorts) @
                                                                           [MLStringToAthString(F.toStringDefault output_sort)]))
        | SOME(SV.athNumFSym(A.int_num(_))) => listVal([MLStringToAthString(S.name(Names.int_sort_symbol))])
        | SOME(SV.athNumFSym(A.real_num(_))) => listVal([MLStringToAthString(S.name(Names.real_sort_symbol))])
        | SOME(SV.metaIdFSym(str)) => listVal([MLStringToAthString(S.name(Names.ide_sort_symbol))])
        | _ => evError(wrongArgKind(N.getSigFun_name,1,termConLCType,v),getPosOpt(pos_ar,2)))
  | getSigFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.getSigFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun getSigPrimUFun(v,env,_) = 
      (case coerceValIntoTermCon(v) of
          SOME(SV.regFSym(afs)) => (case Data.getSignature(Data.fsymName afs) of
                                      (arg_sorts,output_sort,_,has_pred_based_sorts) => listVal((map (fn x => MLStringToAthString(F.toStringDefault(x))) arg_sorts) @
                                                                           [MLStringToAthString(F.toStringDefault output_sort)]))
        | SOME(SV.athNumFSym(A.int_num(_))) => listVal([MLStringToAthString(S.name(Names.int_sort_symbol))])
        | SOME(SV.athNumFSym(A.real_num(_))) => listVal([MLStringToAthString(S.name(Names.real_sort_symbol))])
        | SOME(SV.metaIdFSym(str)) => listVal([MLStringToAthString(S.name(Names.ide_sort_symbol))])
        | _ => primError(wrongArgKind(N.getSigFun_name,1,termConLCType,v)))

fun getFSortandSymSortFromSortString(str:string) = 
             let val str = SemanticValues.fullyQualifySortString(str)
                 val sort_as_symterm = (case Terms.parseSymTerm(str,fn s => String.sub(s,0) = #"'") of 
                                            SOME(res) => res)
                 val mod_path = (case !(Paths.open_mod_paths) of
                                    [] => []
                                  | p::_ => p)
                 val sort_as_symterm = Terms.replaceSymTermConstants(sort_as_symterm,fn sym => MS.find(Data.sort_abbreviations,
                                                                     SV.qualifyName(MS.lastName(sym),mod_path))) 
		 val ht = Symbol.makeHTableWithInitialSize(17)
                 fun translateSort(sort_as_symterm) = 
                       (case SymTerm.isApp(sort_as_symterm) of
                           SOME(fsym,sorts) => FTerm.makeApp(fsym,map translateSort sorts)
                         | _ => (case SymTerm.isVar(sort_as_symterm) of 
                                    SOME(v) => (case Symbol.find(ht,v) of
 			 	                   SOME(v') => v' 
                                                 | _ => let val v' = FTerm.makeFreshVar()
                                                            val _ = Symbol.insert(ht,v,v')
                                                        in
                                                           v'
                                                        end)
                                 | _ => Basic.fail("A sym term is either a variable or a constant...\n")))
                 val sort_as_fterm = translateSort(sort_as_symterm)
             in
                (sort_as_symterm,sort_as_fterm)
             end

fun getSigUnifiedPrimBFun(v,sort_string,env,_) = 
  (case isStringValConstructive(sort_string) of
     SOME(sort_str) => 
      let val (sort_as_sym_term,sort_as_fterm) = getFSortandSymSortFromSortString(sort_str)
      in
        (case coerceValIntoTermCon(v) of
            SOME(SV.regFSym(afs)) => 
                  (case Data.getSignature(Data.fsymName afs) of
                     (arg_sorts,output_sort,_,has_pred_based_sorts) => 
                       let val sort_list_1 = sort_as_fterm::arg_sorts
                           val sort_list_2 = output_sort::arg_sorts
                           val U = F.chooseUnificationProcedureForSortLists(sort_list_2,sort_list_1)
                           val theta = U(sort_list_1,sort_list_2,1)
                           val arg_sorts' = FTerm.applySubLst(theta,arg_sorts)
                           val output_sort' = FTerm.applySub(theta,output_sort)
                       in
                          listVal((map (fn x => MLStringToAthString(F.toStringDefault(x))) arg_sorts') @
                                                                       [MLStringToAthString(F.toStringDefault output_sort')])
                       end)
          | SOME(SV.athNumFSym(A.int_num(_))) => listVal([MLStringToAthString(S.name(Names.int_sort_symbol))])
          | SOME(SV.athNumFSym(A.real_num(_))) => listVal([MLStringToAthString(S.name(Names.real_sort_symbol))])
          | SOME(SV.metaIdFSym(str)) => listVal([MLStringToAthString(S.name(Names.ide_sort_symbol))])
          | _ => primError(wrongArgKind(N.getSigFun_name,1,termConLCType,v)))
      end)

fun symbolToStringFun([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoTermConVal(v) of
          SOME(v') => MLStringToAthString(valToString(v'))
        | _ => evError(wrongArgKind(N.symbolToStringFun_name,1,termConLCType,v),getPosOpt(pos_ar,2)))
  | symbolToStringFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.symbolToStringFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun symbolToStringPrimUFun(v,env,_) = 
      (case coerceValIntoTermConVal(v) of
          SOME(v') => MLStringToAthString(valToString(v'))
        | _ => primError(wrongArgKind(N.symbolToStringFun_name,1,termConLCType,v)))

fun vectorLenFun([vectorVal(v)],(env,_),{pos_ar,file}) = 
       termVal(AthTerm.makeNumTerm(A.int_num(Array.length(v),ref "")))
  | vectorLenFun([v],(env,_),{pos_ar,file}) = 
     evError(wrongArgKind(N.vector_len_name,1,vectorLCType,v),getPosOpt(pos_ar,2))
  | vectorLenFun(vals,(env,_),{pos_ar,file}) = 
      evError(wrongArgNumber(N.vector_len_name,length(vals),1),getPosOpt(pos_ar,0))

fun vectorLenPrimUFun(vectorVal(v),env,_) = 
       termVal(AthTerm.makeNumTerm(A.int_num(Array.length(v),ref "")))
  | vectorLenPrimUFun(v,env,_) = primError(wrongArgKind(N.vector_len_name,1,vectorLCType,v))

fun wivFun([vectorVal(A),listVal(L),cellVal(c as ref(termVal(t)))],env,_) = 
       (case AthTerm.getNumVal(t) of
              SOME(A.int_num(i,_),_) => 
                   let val j = ref i 
                       fun f([]) = (c := termVal(AthTerm.makeNumTerm(A.int_num(!j,ref ""))); unitVal)
                         | f(v::rest) = (Array.update(A,!j,v);j := !j + 1;f(rest))
                 in
                    f(L)
                 end)

fun randomIntPrimUFun(v,env,_) = 
     (case coerceValIntoTerm(v) of 
         SOME(t) =>  (case (AthTerm.getNumVal t) of 
                         SOME(A.int_num(k,_),false) => 
                           termVal(AthTerm.makeNumTerm(A.int_num(MT.getRandomInt(k),ref "")))
                       | _ => primError("The argument to "^(N.random_int_name)^" must be a positive integer"))
      | NONE => primError(wrongArgKind(N.random_int_name,1,termLCType,v)))

fun isTermConFun([v],(env,_),_) = 
        (case coerceValIntoTermCon(v) of 
           SOME(_) => true_val | _ => false_val)
  | isTermConFun(vals,_,{pos_ar,file}) = 
        evError(wrongArgNumber(N.isTermConFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isTermConPrimUFun(v,env,_) = 
        (case coerceValIntoTermCon(v) of 
           SOME(_) => true_val | _ => false_val)

fun isUnitFun([unitVal],_,_) = true_val 
  | isUnitFun([_],_,_) = false_val
  | isUnitFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.isUnitFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isUnitPrimUFun(unitVal,_,_) = true_val 
  | isUnitPrimUFun(_,_,_) = false_val

fun isCellFun([cellVal(_)],_,_) = true_val 
  | isCellFun([_],_,_) = false_val
  | isCellFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.isCellFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isCellPrimUFun(cellVal(_),_,_) = true_val 
  | isCellPrimUFun(_,_,_) = false_val

fun isPropFun([v],(env,_),_) =
      (case coerceValIntoProp(v) of SOME(_) => true_val | _ => false_val)
  | isPropFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.isPropFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isPropPrimUFun(v,env,_) = (case coerceValIntoProp(v) of SOME(_) => true_val | _ => false_val)

fun procNameFun([funVal(_,name,_)],_,_) = MLStringToAthString(name)
  | procNameFun([closFunVal(_,_,_)],_,_) = MLStringToAthString("closure")
  | procNameFun([v],(env,_),{pos_ar,file}) = evError(wrongArgKind(N.procNameFun_name,1,functionLCType,v),getPosOpt(pos_ar,2))
  | procNameFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.procNameFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun procNamePrimUFun(v,_,_) = 
     (case v of
         funVal(_,name,_) => MLStringToAthString(name)
       | primUFunVal(_,{name,...}) => MLStringToAthString(name)
       | primBFunVal(_,{name,...}) => MLStringToAthString(name)
       | closUFunVal(_,_,_,{name,...}) => MLStringToAthString(!name)
       | closBFunVal(_,_,_,_,{name,...}) => MLStringToAthString(!name)
       | closFunVal(_,_,{name,...}) => MLStringToAthString(!name)
       | _ => primError(wrongArgKind(N.procNameFun_name,1,functionLCType,v)))

fun isFunctionFun([funVal(_)],_,_) = true_val 
  | isFunctionFun([primUFunVal(_)],_,_) = true_val 
  | isFunctionFun([primBFunVal(_)],_,_) = true_val 
  | isFunctionFun([closFunVal(_)],_,_) = true_val 
  | isFunctionFun([closUFunVal(_)],_,_) = true_val 
  | isFunctionFun([closBFunVal(_)],_,_) = true_val 
  | isFunctionFun([_],_,_) = false_val
  | isFunctionFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.isFunctionFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isFunctionPrimUFun(v,_,_) = 
       (case v of 
          primUFunVal(_) => true_val
        | primBFunVal(_) => true_val
        | closUFunVal(_) => true_val
        | closBFunVal(_) => true_val
        | closFunVal(_) => true_val
        | funVal(_) => true_val
        | _ => false_val)

fun isMethodFun([methodVal(_)],_,_) = true_val 
  | isMethodFun([primUMethodVal(_)],_,_) = true_val 
  | isMethodFun([primBMethodVal(_)],_,_) = true_val 
  | isMethodFun([closMethodVal(_)],_,_) = true_val 
  | isMethodFun(vals,_,{pos_ar,file}) = 
      evError(wrongArgNumber(N.isMethodFun_name,length(vals),1),getPosOpt(pos_ar,0))    

fun isMethodPrimUFun(methodVal(_),_,_) = true_val 
  | isMethodPrimUFun(primUMethodVal(_),_,_) = true_val 
  | isMethodPrimUFun(primBMethodVal(_),_,_) = true_val 
  | isMethodPrimUFun(closMethodVal(_),_,_) = true_val 
  | isMethodPrimUFun(_,_,_) = false_val

fun lenFun([listVal(vals)],_,_) = termVal(AthTerm.makeNumTerm(A.int_num(length(vals),ref "")))
  | lenFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.lenFun_name,1,listLCType,v),getPosOpt(pos_ar,2))
  | lenFun(vals,_,{pos_ar,file}) =  evError(wrongArgNumber(N.lenFun_name,length(vals),1),getPosOpt(pos_ar,0))    

fun lenPrimUFun(listVal(vals),_,_) = termVal(AthTerm.makeNumTerm(A.int_num(length(vals),ref "")))
  | lenPrimUFun(v,_,_) = primError(wrongArgKind(N.lenFun_name,1,listLCType,v))

fun consFun([v,listVal(vs)],_,_) = listVal(v::vs)
  | consFun([v1,v2],_,{pos_ar,file}) = evError(wrongArgKind(N.consFun_name,2,listLCType,v2),
                                               getPosOpt(pos_ar,3))
  | consFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.consFun_name,length(vals),2),getPosOpt(pos_ar,0))

fun consPrimBFun(v,listVal(vs),_,_) = listVal(v::vs)
  | consPrimBFun(v1,v2,_,_) = primError(wrongArgKind(N.consFun_name,2,listLCType,v2))

fun carFun([listVal(v::vs)],_,_) = v
  | carFun([listVal([])],_,{pos_ar,file}) = 
         evError("Empty "^listLCType^" given as argument to "^N.carFun_name^"---a non-empty list "^
                 "is required",getPosOpt(pos_ar,2))
  | carFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.carFun_name,1,listLCType,v),
                                          getPosOpt(pos_ar,2))
  | carFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.carFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun carPrimUFun(v,_,_) = 
       (case v of
           listVal(v::_) => v 
         | listVal(_) => primError("Empty "^listLCType^" given as argument to "^N.carFun_name^"---a non-empty list "^"is required")
         | _ => primError(wrongArgKind(N.carFun_name,1,listLCType,v)))

fun getSymDefFun([v],(env,_),{pos_ar,file}) = 
  (case coerceTermValIntoTermConVal(v) of
     SOME(termConVal(regFSym(some_fsym))) => 
	     let val sname = MS.name(D.fsymName(some_fsym))
                 val (vmap,_) = getValAndModMaps(!top_val_env)
	     in
	      (case Symbol.lookUp(vmap,Symbol.symbol(sname^"-def")) of
	          SOME(res as propVal(P)) => res
	        | _ => let val msym = A.makeMS(sname^"-definition",NONE)
                           val (mods,sym) = MS.split(msym)
                       in
                       (case lookUp(!env,mods,sym) of
	                   SOME(res as propVal(_)) => res
			 | _ => unitVal)
                       end)
	     end
    | _ => evError(wrongArgKind(N.getSymDef_name,1,termConLCType,v),getPosOpt(pos_ar,2)))
  | getSymDefFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.getSymDef_name,length(vals),1),getPosOpt(pos_ar,0))

fun getSymDefPrimUFun(v,env,_) = 
      (case coerceTermValIntoTermConVal(v) of
         SOME(termConVal(regFSym(some_fsym))) => 
	       let val sname = MS.name(D.fsymName(some_fsym))
                   val (vmap,_) = getValAndModMaps(!env)
  	       in
   	         (case Symbol.lookUp(vmap,Symbol.symbol(sname^"-def")) of
	            SOME(res as propVal(P)) => res
  	          | _ => let val msym = A.makeMS(sname^"-definition",NONE)
                             val (mods,sym) = MS.split(msym)
                         in
                         (case lookUp(!top_val_env,mods,sym) of
	                     SOME(res as propVal(_)) => res
	       		   | _ => unitVal)
                         end)
 	       end
    | _ => primError(wrongArgKind(N.getSymDef_name,1,termConLCType,v)))

fun cdrFun([listVal(v::vs)],_,_) = listVal(vs)
  | cdrFun([listVal([])],_,_) = listVal([])
  | cdrFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.cdrFun_name,1,listLCType,v),
                                               getPosOpt(pos_ar,2))
  | cdrFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.cdrFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun cdrPrimUFun(listVal(v::vs),_,_) = listVal(vs)
  | cdrPrimUFun(listVal([]),_,_) = listVal([])
  | cdrPrimUFun(v,_,_) = primError(wrongArgKind(N.cdrFun_name,1,listLCType,v))

fun isNullFun([listVal([])],_,_) = termVal(true_term)
  | isNullFun([listVal(_::_)],_,_) = termVal(false_term)
  | isNullFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.nullFun_name,1,listLCType,v),getPosOpt(pos_ar,2))
  | isNullFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.nullFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isNullPrimUFun(listVal([]),_,_) = termVal(true_term)
  | isNullPrimUFun(listVal(_::_),_,_) = termVal(false_term)
  | isNullPrimUFun(v,_,_) = primError(wrongArgKind(N.nullFun_name,1,listLCType,v))

fun reverseFun([listVal(vals)],_,_) = listVal(List.rev(vals))
  | reverseFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.revFun_name,1,listLCType,v),getPosOpt(pos_ar,2))
  | reverseFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.revFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun reversePrimUFun(listVal(vals),_,_) = listVal(List.rev(vals))
  | reversePrimUFun(v,_,_) = primError(wrongArgKind(N.revFun_name,1,listLCType,v))

fun subComposeFun([v1,v2],_,{pos_ar,file}) = 
     (case v1 of
         subVal(s1) => (case v2 of 
                           subVal(s2) =>  subVal(AthTerm.composeSubs(s1,s2))
                         | _ => evError(wrongArgKind(N.subComposeFun_name,2,subLCType,v2),getPosOpt(pos_ar,3)))
       | _ =>  evError(wrongArgKind(N.subComposeFun_name,1,subLCType,v1),getPosOpt(pos_ar,2)))
  | subComposeFun(vals,_,{pos_ar,file}) = 
         evError(wrongArgNumber(N.subComposeFun_name,length(vals),2),getPosOpt(pos_ar,0))

fun subComposePrimBFun(v1,v2,_,_) = 
     (case v1 of
         subVal(s1) => (case v2 of 
                           subVal(s2) =>  subVal(AthTerm.composeSubs(s1,s2))
                         | _ => primError(wrongArgKind(N.subComposeFun_name,2,subLCType,v2)))
       | _ =>  primError(wrongArgKind(N.subComposeFun_name,1,subLCType,v1)))

fun getRewritesFun([t_val,listVal(eqns_val)],(env,ab),{pos_ar,file}) = 
 (case coerceValIntoTerm(t_val) of 
     SOME(t) =>  let val eqns = Semantics.getProps(eqns_val,"the argument list given to "^N.getRewritesFun_name,env)
                     val terms_and_eqns = TermSearch.getAllRewrites(t,eqns,ab)
                 in
                   listVal(map (fn (t,p,sub) => listVal([termVal(t),propVal(p),subVal(sub)])) terms_and_eqns)
                 end
   | _ => raise Basic.Never)
 | getRewritesFun(_) = raise Basic.Never

fun getRewritesPrimBFun(t_val,listVal(eqns_val),env,ab) = 
 (case coerceValIntoTerm(t_val) of 
     SOME(t) =>  let val eqns = Semantics.getProps(eqns_val,"the argument list given to "^N.getRewritesFun_name,env)
                     val terms_and_eqns = TermSearch.getAllRewrites(t,eqns,ab)
                 in
                   listVal(map (fn (t,p,sub) => listVal([termVal(t),propVal(p),subVal(sub)])) terms_and_eqns)
                 end
   | _ => raise Basic.Never)
 | getRewritesPrimBFun(_) = primError("Incorrect invocation of "^N.getRewritesFun_name)

fun rewriteSearchFun([t1_val,t2_val,listVal(eqns_val),style_val,max_val,silent_val],env,ab) = 
 (case (coerceValIntoTerm(t1_val),coerceValIntoTerm(t2_val)) of
     (SOME(t1),SOME(t2)) => 
        let val eqns = Semantics.getProps(eqns_val,"the argument list given to "^N.rewriteSearchFun_name,env)
            val style_string = (case isStringValConstructive(style_val) of 
                                   SOME(str) => str
                                 | _ => primError(wrongArgKind(N.rewriteSearchFun_name,4,stringLCType,style_val)))
            val max = (case coerceValIntoTerm(max_val) of
                          SOME(t) => (case (AT.getNumVal t) of 
                                         SOME(A.int_num(n,_),_) => n
                                       | _ => primError(wrongArgKind(N.rewriteSearchFun_name,5,numTermLCType,style_val)))
                       | _ => primError(wrongArgKind(N.rewriteSearchFun_name,5,numTermLCType,style_val)))
            val silent = (case isStringValConstructive(silent_val) of 
                             SOME("silent") => true
                           | _ => false)
        in
           (case TermSearch.search(t1,t2,eqns,style_string,max,silent,ab) of
              SOME(s,count) => let val derivation_list = TermSearch.getDerivation(s,[])
                                   val res_val = 
                                        listVal(map (fn (term,SOME(eqn),sub) => listVal([termVal term,propVal(eqn),subVal(sub)])
                                                      | (term,NONE,_)        => listVal([termVal term,propVal(P.makeEquality(term,term)),subVal(AT.empty_sub)]))
                                                    derivation_list)
                               in  
                                   res_val 
                               end
            | _ => let val _ = () 
                   in unitVal end)
                       
        end
    | _ => primError(wrongArgKindGeneric(N.rewriteSearchFun_name,termLCType)))
 | rewriteSearchFun([t1_val,t2_val,_,style_val,max_val,silent_val],env,_) = 
       primError(wrongArgKindGeneric(N.rewriteSearchFun_name,listLCType))
 | rewriteSearchFun(vals,env,_) = primError(wrongArgNumber(N.rewriteSearchFun_name,length(vals),6))
       
fun getTermVars(vals,fun_name) = 
    let fun error() = primError("All members of the list that is given as the third argument to "^fun_name^" must be variables")
        fun getTerm(termVal(t)) = (case AT.isVarOpt(t) of 
                                      SOME(v) => v 
                                    | _ => error())
          | getTerm(_) = error()
    in 
       map getTerm vals
    end

fun renameSortVarsPrimUFun(v,_,_) = 
     (case coerceValIntoTerm(v) of 
         SOME(t) => let val t' = AT.renameSortVars(t)
                    in
                      termVal(t')
                    end
       | _ =>  (case coerceValIntoProp(v) of 
                   SOME(p) => propVal(P.renameSortVars(p))
                 | _ => primError(wrongArgKind(N.renameSortVarsFun_name,1,propLCType,v))))

fun renameSortVarsLstPrimUFun(listVal(vals),e,ab) = 
  let val props = Semantics.getProps(vals,"the argument list given to "^N.renameSortVarsFun_name,e)
      val props' = P.renameSortVarsLst(props)
  in
     listVal(map propVal props')     
  end
  | renameSortVarsLstPrimUFun(v,e,ab) = 
      primError(wrongArgKind(N.renameSortVarsLstFun_name,1,propLCType,v))

fun matchProps3Fun([v1,v2,listVal(var_vals)],env,_) = 
        let val uvars = getTermVars(var_vals,N.matchPropsFun_name)
        in
           (case coerceValIntoProp(v1) of 
               SOME(p1) =>  
                  (case coerceValIntoProp(v2) of 
                      SOME(p2) => (case P.matchRW(p1,p2,uvars) of
                                      SOME(sub) => subVal(sub)
                                    | _ => false_val)
                    | _ => primError(wrongArgKind(N.matchPropsFun_name,2,propLCType,v2)))
             | _ => (case v1 of  
                        listVal(pvals1) =>  
                          (case v2 of
                              listVal(pvals2) => 
                                  let val props1 = Semantics.getProps(pvals1,"the argument list given to "^N.matchPropsFun_name,
                                                                      env)
                                      val props2 = Semantics.getProps(pvals2,"the argument list given to "^N.matchPropsFun_name,
                                                                      env)
                                  in 
                                    (case P.matchLstRW(props1,props2,uvars) of
                                        SOME(sub) => subVal(sub)
                                      | _ => false_val)
                                  end
                            | _ => primError(wrongArgKind(N.matchPropsFun_name,2,listLCType,v2)))
                   | _ => primError(wrongArgKind(N.matchPropsFun_name,1,propLCType^" or "^listLCType^" of "^propLCType^"s",v1))))
        end
  | matchProps3Fun([v1,v2,v3],env,_) = primError(wrongArgKind(N.matchPropsFun_name,3,listLCType^" of "^varLCType^"s",v3))
  | matchProps3Fun(vals,_,_) = primError(wrongArgNumber(N.matchPropsFun_name,length(vals),2))

fun matchPropsPrimBFun(v1,v2,env,_) = 
     (case coerceValIntoProp(v1) of
         SOME(p1) => 
            (case coerceValIntoProp(v2) of
                SOME(p2) => (case P.match(p1,p2) of
                                SOME(sub) => subVal(sub)
                              | _ => false_val)
              | _ => primError(wrongArgKind(N.matchPropsFun_name,2,propLCType,v2)))
       | _ => (case v1 of  
                listVal(pvals1) =>  
                 (case v2 of
                    listVal(pvals2) => 
                       let val  props1 = Semantics.getProps(pvals1,"the argument list given to "^N.matchPropsFun_name,
                                                            env)
                           val props2 = Semantics.getProps(pvals2,"the argument list given to "^N.matchPropsFun_name,
                                                           env)
                       in 
                          (case P.matchLst(props1,props2) of
                             SOME(sub) => subVal(sub)
                            | _ => false_val)
                       end
                  | _ => primError(wrongArgKind(N.matchPropsFun_name,2,listLCType,v2)))
              | _ => primError(wrongArgKind(N.matchPropsFun_name,1,propLCType^" or "^listLCType^" of "^propLCType^"s",v1))))

fun matchFun([v1,v2],env,_) = 
     (case coerceValIntoTerm(v1) of
        SOME(t1) => 
            (case coerceValIntoTerm(v2) of
                SOME(t2) => (case AthTerm.match(t1,t2) of
                                SOME(sub) => subVal(sub)
                              | _ => false_val)
              | _ => primError(wrongArgKind(N.matchFun_name,2,termLCType,v2)))
       | _ => (case v1 of  
                listVal(tvals1) =>  
                 (case v2 of
                    listVal(tvals2) => 
                       let val terms1 = getTermsNoPos(tvals1,"the first list argument of "^N.matchFun_name,NONE)
                           val terms2 = getTermsNoPos(tvals2,"the second list argument of "^N.matchFun_name,NONE)
                       in 
                          (case AthTerm.matchLst(terms1,terms2) of
                             SOME(sub) => subVal(sub)
                            | _ => false_val)
                       end
                  | _ => primError(wrongArgKind(N.matchFun_name,2,listLCType,v2)))
              | _ => primError(wrongArgKind(N.matchFun_name,1,termLCType^" or "^listLCType^" of "^termLCType^"s",v1))))
  | matchFun([v1,v2,listVal(var_vals)],env,_) = 
        let val uvars = getTermVars(var_vals,N.matchFun_name)
        in
           (case coerceValIntoTerm(v1) of
             SOME(t1) => 
                (case coerceValIntoTerm(v2) of
                    SOME(t2) => (case AthTerm.matchRW(t1,t2,uvars) of
                                    SOME(sub) => subVal(sub)
                                  | _ => false_val)
                  | _ => primError(wrongArgKind(N.matchFun_name,2,termLCType,v2)))
           | _ => (case v1 of  
                    listVal(tvals1) =>  
                     (case v2 of
                        listVal(tvals2) => 
                           let val terms1 = getTermsNoPos(tvals1,"the first list argument of "^N.matchFun_name,NONE)
                               val terms2 = getTermsNoPos(tvals2,"the second list argument of "^N.matchFun_name,NONE)
                           in 
                              (case AthTerm.matchLstRW(terms1,terms2,uvars) of
                                 SOME(sub) => subVal(sub)
                                | _ => false_val)
                           end
                      | _ => primError(wrongArgKind(N.matchFun_name,2,listLCType,v2)))
                  | _ => primError(wrongArgKind(N.matchFun_name,1,termLCType^" or "^listLCType^" of "^termLCType^"s",v1))))
        end
  | matchFun([v1,v2,v3],env,_) = primError(wrongArgKind(N.matchFun_name,3,listLCType^" of "^varLCType^"s",v3))
  | matchFun(vals,_,_) = primError(wrongArgNumber(N.matchFun_name,length(vals),2))

fun unifyFun([v1,v2],env,_) = 
      (case coerceValIntoTerm(v1) of
          SOME(t1) => (case coerceValIntoTerm(v2) of
                          SOME(t2) => (case AthTerm.unify(t1,t2) of
                                          SOME(sub) => subVal(sub)
                                        | _ => false_val)
                        | _ => primError(wrongArgKind(N.unifyFun_name,2,termLCType,v2)))
        | _ => primError(wrongArgKind(N.unifyFun_name,1,termLCType,v1)))
  | unifyFun([v1,v2,listVal(var_vals)],env,_) = 
        let val var_constants = getTermVars(var_vals,N.unifyFun_name)
        in
           (case coerceValIntoTerm(v1) of
             SOME(t1) => 
                (case coerceValIntoTerm(v2) of
                    SOME(t2) => (case AthTerm.unifyRW(t1,t2,var_constants) of
                                    SOME(sub) => subVal(sub)
                                  | _ => false_val)
                  | _ => primError(wrongArgKind(N.unifyFun_name,2,termLCType,v2)))
           | _ => (case v1 of  
                    listVal(tvals1) =>  
                     (case v2 of
                        listVal(tvals2) => 
                           let val terms1 = getTermsNoPos(tvals1,"the first list argument of "^N.unifyFun_name,NONE)
                               val terms2 = getTermsNoPos(tvals2,"the second list argument of "^N.unifyFun_name,NONE)
                           in 
                              (case AthTerm.unifyLstRW(terms1,terms2,var_constants) of
                                 SOME(sub) => subVal(sub)
                                | _ => false_val)
                           end
                      | _ => primError(wrongArgKind(N.unifyFun_name,2,listLCType,v2)))
                  | _ => primError(wrongArgKind(N.unifyFun_name,1,termLCType^" or "^listLCType^" of "^termLCType^"s",v1))))
        end
  | unifyFun(vals,_,_) = primError(wrongArgNumber(N.unifyFun_name,length(vals),2));


fun uspecGivenTermToFinalRes(t,v,P,body,ab,pos_opt) = 
             let val v_sort = ATV.getSort(v)
                 val t_sort = AT.getSort(t)
                 val _ = (case pos_opt of 
                             NONE => checkOneAbMemberNoPos(P,ab,N.uspecPrimMethod_name)
		           | SOME(pos)  => checkAbMembers([(P,pos)],ab,N.uspecPrimMethod_name))
                 val msg = "Invalid use of "^N.uspecPrimMethod_name^": the sort of the term\n"^
        		   AT.toPrettyString(0,t,F.varToString)^"\nis incompatible with the sort of the "^
                           "universally quantified variable in the sentence:\n"^P.toPrettyString(0,P,F.varToString)
                 val res_prop = let val sort_sub = 
                                          (case F.isSubSort(t_sort,v_sort) of						             
                                              SOME(sub) => sub
   	                                    | _ => evError(msg,pos_opt))
 		                in
 			           Prop.replaceVarByTermOfSomeSubSort(v,t,body,sort_sub)
		                end
             in
                propVal(res_prop)
             end

fun uSpecPrimMethod([v1,v2],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoProp(v1) of
         SOME(P) => (case P.isUGen(P) of 
                       SOME(v,body) =>
                          (case coerceValIntoTerm(v2) of
                              SOME(t) => uspecGivenTermToFinalRes(t,v,P,body,ab,getPosOpt(pos_ar,0))
                            | _ => let
                                   in
                                     (case D.funSortArity(ATV.getSort(v)) of 
                                       SOME(K) => let val t = Semantics.liftArg(v1,K,getPosOpt(pos_ar,3))
                                                  in
 						    uspecGivenTermToFinalRes(t,v,P,body,ab,getPosOpt(pos_ar,0))
						  end
                                     | _ => evError(wrongArgKind(N.uspecPrimMethod_name,2,termLCType,v2),getPosOpt(pos_ar,3)))
                                  end)
                     | _ => evError(dwrongArgKind(N.uspecPrimMethod_name,1,"a universal generalization",P),
                                    getPosOpt(pos_ar,2)))
       | _ => evError(wrongArgKind(N.uspecPrimMethod_name,1,propLCType,v1),getPosOpt(pos_ar,2)))
  | uSpecPrimMethod(args,(env,ab),{pos_ar,file}) = 
       evError(wrongArgNumber(N.uspecPrimMethod_name,length(args),2),getPosOpt(pos_ar,0))

fun uSpecPrimBMethod(v1,v2,env,ab) = 
  let
  in
     (case coerceValIntoProp(v1) of
         SOME(P) => (case P.isUGen(P) of 
                       SOME(v,body) =>
                          (case coerceValIntoTerm(v2) of
                              SOME(t) => 
                                 let val v_sort = ATV.getSort(v)
				     val t_sort = AT.getSort(t)
				     val _ = checkOneAbMemberNoPos(P,ab,N.uspecPrimMethod_name)
				     val msg = "Invalid use of "^N.uspecPrimMethod_name^
					       ": the sort of the term\n"^
						AT.toPrettyString(0,t,F.varToString)^
						"\nis incompatible with the sort of the "^
						"universally quantified variable in the sentence:\n"^
						P.toPrettyString(0,P,F.varToString)
                                     val res_prop = let val sort_sub = 
						             (case F.isSubSort(t_sort,v_sort) of
						                 SOME(sub) => sub
					                       | _ => primError(msg))
					            in
						      Prop.replaceVarByTermOfSomeSubSort(v,t,body,sort_sub)
					            end
                                 in
                                    propVal(res_prop)
                                 end
                            | _ => (case D.funSortArity(ATV.getSort(v)) of 
                                       SOME(K) => let val t = Semantics.liftArg(v2,K,NONE)
                                                  in
 						    uspecGivenTermToFinalRes(t,v,P,body,ab,NONE)
						  end
                                     | _ => evError(wrongArgKind(N.uspecPrimMethod_name,2,termLCType,v2),NONE)))
                     | _ => primError(dwrongArgKind(N.uspecPrimMethod_name,1,"a universal generalization",P)))
       | _ => primError(wrongArgKind(N.uspecPrimMethod_name,1,propLCType,v1)))
    end

fun egenWitnessToFinalRes(witness_term,v,P,body,ab) = 
      let val v_sort = ATV.getSort(v)
          val w_sort = AT.getSort(witness_term)
          val sort_sub_opt = F.isSubSort(w_sort,v_sort)
          fun f() = let val vsp = F.makeVarSortPrinter()
                    in
                       primError("Failed existential generalization---the sort of the "^"witness term: \n"^(AT.toPrettyString(0,witness_term,vsp))^
  		                 "\nis not a subsort of the existentially "^"quantified variable:\n"^(ATV.toPrettyString(0,v,vsp)))
		    end
	  val sort_sub = (case sort_sub_opt of NONE => f() | SOME(s) => s)
  	  val witness_prop = Prop.replaceVarByTermOfSomeSubSort(v,witness_term,body,sort_sub)
      in
        if ABase.isMember(witness_prop,ab) then
           propVal(P)
        else
           primError("Failed existential generalization---the "^"required witness sentence\n"^
                     pprint(0,witness_prop)^"\nis not in the assumption base")
      end

fun eGenPrimMethod([v1,v2],env,ab) = 
     (case coerceValIntoProp(v1) of 
         SOME(P) => 
            (case P.isEGen(P) of 
                SOME(v,body) => 
                    (case coerceValIntoTerm(v2) of
                        SOME(witness) => egenWitnessToFinalRes(witness,v,P,body,ab)
                      | _ => (case D.funSortArity(ATV.getSort(v)) of 
                                SOME(K) => let val witness_term = Semantics.liftArg(v2,K,NONE)
                                           in
 			  		      egenWitnessToFinalRes(witness_term,v,P,body,ab)
					   end
			      | _ => primError(wrongArgKind(N.egenPrimMethod_name,2,termLCType,v2))))
              | _ => primError(dwrongArgKind(N.egenPrimMethod_name,1,"an existential generalization",P)))
       | _ => primError(wrongArgKind(N.egenPrimMethod_name,1,propLCType,v1)))
  | eGenPrimMethod(args,_,_) = primError(wrongArgNumber(N.egenPrimMethod_name,length(args),2))

fun eGenUniquePrimMethod([v1,v2],env,ab) = 
     (case coerceValIntoProp(v1) of 
         SOME(P) =>
            (case P.isEGenUnique(P) of
                SOME(v,body) => 
                    (case coerceValIntoTerm(v2) of
                        SOME(witness) => 
                            let val body' = body
                                val witness_prop = Prop.replace(v,witness,body)
                                val fresh_var1 = ATV.fresh()
                                val fresh_var2 = ATV.fresh()
                                val (fresh_term1,fresh_term2) =(AthTerm.makeVar(fresh_var1),
                                                                AthTerm.makeVar(fresh_var2))
                                val prop1 = Prop.replace(v,fresh_term1,body')
                                val prop2 = Prop.replace(v,fresh_term2,body')
                                val desired_conclusion1 = Prop.makeEquality(fresh_term1,fresh_term2)
                                val desired_conclusion2 = Prop.makeEquality(fresh_term2,fresh_term1)
                                val uniqueness_prop1 = Prop.makeUGen([fresh_var1],Prop.makeUGen([fresh_var2],
                                                       Prop.makeConditional(Prop.makeConjunction([prop1,prop2]),
                                                                 desired_conclusion1)))
                                val uniqueness_prop2 = Prop.makeUGen([fresh_var1],Prop.makeUGen([fresh_var2],
                                                       Prop.makeConditional(Prop.makeConjunction([prop2,prop1]),
                                                                 desired_conclusion1)))
                                val uniqueness_prop3 = Prop.makeUGen([fresh_var1],Prop.makeUGen([fresh_var2],
                                                       Prop.makeConditional(Prop.makeConjunction([prop1,prop2]),
                                                                 desired_conclusion2)))
                                val uniqueness_prop4 = Prop.makeUGen([fresh_var1],Prop.makeUGen([fresh_var2],
                                                       Prop.makeConditional(Prop.makeConjunction([prop2,prop1]),
                                                                 desired_conclusion2)))
                                val uniqueness_holds = (ABase.isMember(uniqueness_prop1,ab) orelse
                                                        ABase.isMember(uniqueness_prop2,ab) orelse
                                                        ABase.isMember(uniqueness_prop3,ab) orelse
                                                        ABase.isMember(uniqueness_prop4,ab))
                            in
                               if not(ABase.isMember(witness_prop,ab)) then
                                  primError("Failed existential generalization: the witness sentence\n"^
                                          pprint(0,witness_prop)^"\nis not in the assumption base"
                                          )
                               else 
                                  if not(uniqueness_holds) then
                                     primError("Failed unique existential generalization: the required uniqueness "^
                                             "condition:\n"^pprint(0,uniqueness_prop1)^"\nis not in "^
                                             "the assumption base")
                               else
                                   propVal(P)
                            end
                      | _ => primError(wrongArgKind(N.egenUniquePrimMethod_name,2,termLCType,v2)))
              | _ => primError(dwrongArgKind(N.egenUniquePrimMethod_name,1,"a unique existential generalization",P)
                                           ))
       | _ => primError(wrongArgKind(N.egenUniquePrimMethod_name,1,propLCType,v1)))
  | eGenUniquePrimMethod(args,env,ab) = 
        primError(wrongArgNumber(N.egenUniquePrimMethod_name,length(args),2))

fun timeOutPrimBFun(v1,v2,env,ab) =
 (case getIntValue(v2) of
   SOME(max_seconds) => 
     (case v1 of 
       closFunVal(A.functionExp({params as [],body,...}),clos_env,{prec,assoc,...}) => 
          let val capped_fun = Basic.timeOut(fn () => evalClosure(v1,[],ab,SOME(A.posOfExp(body))),max_seconds)
              val (success,res_val,ex_opt) = 
                             ((case (capped_fun ()) of 
                                 SOME(res_val) => (true,res_val,NONE)
  		               | _ => (false,unitVal,NONE)) handle ex => (false,unitVal,SOME(ex)))
          in
             (case ex_opt of 
                 SOME(ex) => raise ex 
	       | _ => let val binding1 = (termVal(AthTerm.makeIdeConstant("outcome")),
                                          termVal(AthTerm.makeIdeConstant(if success then "success" else "timeout")))
                          val binding2 = (termVal(AthTerm.makeIdeConstant("result")),res_val)
                          fun addBindings(m,bindings) = Maps.insertLst(m,bindings)
                      in
                         SV.mapVal(addBindings(Maps.makeMap(SV.compare),[binding1,binding2]))
                      end)
          end
    |  _ => primError(wrongArgKind(N.timeoutFun_name,0,closFunLCType,v1)))
 | _ => primError(wrongArgKind(N.timeoutFun_name,1,closFunLCType,v2)))

fun timeOutPrimBMethod(v1,v2,env,ab) =
 (case getIntValue(v2) of
   SOME(max_seconds) => 
     (case v1 of 
        closMethodVal(A.methodExp({params=[],body,pos,name}),env_ref) =>
          let val capped_method = Basic.timeOut(fn () => evalMethodClosure(v1,[],ab,A.posOfDed(body)),max_seconds)
              val (success,res_val,ex_opt) = 
                             ((case (capped_method ()) of 
                                 SOME(res_val) => (true,res_val,NONE)
  		               | _ => (false,unitVal,NONE)) handle ex => (false,unitVal,SOME(ex)))
          in
             (case ex_opt of 
                 SOME(ex) => raise ex 
	       | _ => if success then res_val else primError("Method call timed out: no result produced after " ^ (Int.toString max_seconds) ^ " milliseconds."))
                           
          end
    |  _ => primError(wrongArgKind(N.timeoutMethod_name,0,closFunLCType,v1)))
 | _ => primError(wrongArgKind(N.timeoutMethod_name,1,closFunLCType,v2)))

fun catchPrimBFun(v1,v2,env,ab) = 
     (case (v1,v2) of
        (closFunVal(e1,ref env1,_),closUFunVal(e2,arg_name,ref env2,_)) => 
           let val _ = (case (getClosureArity(v1),getClosureArity(v2)) of
                           (0,1) => ()
                         | (0,n) => primError("The second procedure argument given to "^(N.catchFun_name)^" must take exactly one argument,\n"^
                                              "but here it takes "^(Int.toString(n)))
                         | (n,_) =>   primError("The first procedure argument given to "^(N.catchFun_name)^" must take zero arguments,\n"^
                                                "but here it takes "^(Int.toString(n))))
           in
             ((evalClosure(v1,[],ab,NONE))
                handle e => let val str = MLStringToAthString(Semantics.exceptionToString(e))
                            in 
                              evalClosure(v2,[str],ab,NONE)
                            end)
           end
      | (closFunVal(_),v) => 
           
              primError(wrongArgKind(N.catchFun_name,1,closFunLCType,v2))
      | (_,closFunVal(_)) => primError(wrongArgKind(N.catchFun_name,1,closFunLCType,v1)))


end;


