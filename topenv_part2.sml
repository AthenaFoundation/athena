(*======================================================================

Definitions of primitive procedures and methods (bound in Athena's top-level
environment), part 2 of 2. 

=======================================================================*)

structure TopEnv = 
struct

open TopEnv1

fun isSortInstanceFun([v1,v2],(env,_),{pos_ar,file}) = 
     (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of 
         (SOME(t1),SOME(t2)) => (case AT.isSortInstance(t1,t2) of
                                    SOME(_) => true_val
                                  | _ => false_val)
       | _ => (case (coerceValIntoProp(v1),coerceValIntoProp(v2)) of
                  (SOME(p1),SOME(p2)) => (case Prop.isSortInstance(p1,p2) of
                                             SOME(_) => true_val
                                           | _ => false_val)
                | _ => evError(wrongArgKind(N.isSortInstanceFun_name,2,termLCType,v2),getPosOpt(pos_ar,0))))
  | isSortInstanceFun(vals,(env,_),{pos_ar,file}) =
       evError(wrongArgNumber(N.isSortInstanceFun_name,length(vals),2),getPosOpt(pos_ar,0)) 

fun comparePrimBFun(v1,v2,env,_) = 
   (case SV.compare(v1,v2) of
       GREATER => termVal(AT.makeIdeConstant("GR"))
     | LESS => termVal(AT.makeIdeConstant("LS"))
     | EQUAL => termVal(AT.makeIdeConstant("EQ")))

fun isSortInstancePrimBFun(v1,v2,env,_) = 
     (case (coerceValIntoTerm(v1),coerceValIntoTerm(v2)) of 
         (SOME(t1),SOME(t2)) => (case AT.isSortInstance(t1,t2) of
                                    SOME(_) => true_val
                                  | _ => false_val)
       | _ => (case (coerceValIntoProp(v1),coerceValIntoProp(v2)) of
                  (SOME(p1),SOME(p2)) => (case Prop.isSortInstance(p1,p2) of
                                             SOME(_) => true_val
                                           | _ => false_val)
                | _ => primError(wrongArgKind(N.isSortInstanceFun_name,2,termLCType,v2))))

fun sortInstancePrimMethod([v1,v2],env:value_environment ref,ab) = 
        (case coercePositionlessValsIntoProps([v1,v2],N.sortInstancePrimMethod_name) of 
                plst as [P,Q] =>  let val _ = checkAbMembersNoPos([Q],ab,N.sortInstancePrimMethod_name)
                                                in
                                                  (case Prop.isSortInstance(P,Q) of
                                                      SOME(_) => propVal(P)
                                                    | _ => let val msg = "Failed application of "^N.sortInstancePrimMethod_name^". "^
                                                                         "The sentence\n"^(P.toPrettyString(0,P,makeVarSortPrinter()))^
                                                                         "\nis not a sort instance of the sentence\n"^(P.toPrettyString(0,Q,makeVarSortPrinter()))
                                                           in primError(msg)
                                                           end)
                                                end)
  | sortInstancePrimMethod(args,env,ab) = primError(wrongArgNumber(N.sortInstancePrimMethod_name,length(args),2))

fun lubFun([v1,v2],(env,_),{pos_ar,file}) = 
  (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
     (SOME(str1),SOME(str2)) => (case (SortOrder.lub(A.makeMS(str1,NONE),A.makeMS(str2,NONE))) of
				    SOME(ms) => MLStringToAthString(MS.name(ms))
				  | _ => MLStringToAthString("NONE"))
   | _ => evError(wrongArgKind("lub",1,stringLCType,v1),getPosOpt(pos_ar,2)))
  | lubFun(vals,(env,_),{pos_ar,file}) = 
     evError(wrongArgNumber("lub",length(vals),2),getPosOpt(pos_ar,0))

fun lubPrimBFun(v1,v2,env,_) = 
  (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
     (SOME(str1),SOME(str2)) => (case (SortOrder.lub(A.makeMS(str1,NONE),A.makeMS(str2,NONE))) of
				    SOME(ms) => MLStringToAthString(MS.name(ms))
				  | _ => MLStringToAthString("NONE"))
   | _ => primError(wrongArgKind("lub",1,stringLCType,v1)))

fun glbFun([v1,v2],(env,_),{pos_ar,file}) = 
  (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
     (SOME(str1),SOME(str2)) => (case (SortOrder.glb(A.makeMS(str1,NONE),A.makeMS(str2,NONE))) of
				    SOME(ms) => MLStringToAthString(MS.name(ms))
				  | _ => MLStringToAthString("NONE"))
   | _ => evError(wrongArgKind("glb",1,stringLCType,v1),getPosOpt(pos_ar,2)))
  | glbFun(vals,(env,_),{pos_ar,file}) = 
     evError(wrongArgNumber("glb",length(vals),2),getPosOpt(pos_ar,0))

fun glbPrimBFun(v1,v2,env,_)  = 
  (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
     (SOME(str1),SOME(str2)) => (case (SortOrder.glb(A.makeMS(str1,NONE),A.makeMS(str2,NONE))) of
				    SOME(ms) => MLStringToAthString(MS.name(ms))
				  | _ => MLStringToAthString("NONE"))
   | _ => primError(wrongArgKind("glb",1,stringLCType,v1)))

fun escapeStringPrimUFun(v,env,_)  = 
  (case isStringValConstructive(v) of
      SOME(str) => MLStringToAthString(Basic.escape(str))
    | _ => primError(wrongArgKind(Names.escapeStringFun_name,1,stringLCType,v)))

fun nnfFun(v,env,_)  = 
        (case coerceValIntoProp(v) of
            SOME(p) => propVal(P.nnf(p))
          | _ => primError(wrongArgKind(Names.nnf_fun_name,1,propLCType,v)))

fun makePrivatePrimUFun(v,env,_)  = 
  (case isStringValConstructive(v) of
      SOME(str) => (Semantics.makePrivate(str);unitVal)
    | _ => primError(wrongArgKind("make-private",1,stringLCType,v)))

fun extendSubFun([sval as subVal(sub),v1,v2],env,_) = 
     (case coerceValIntoTerm(v1) of
        SOME(t1) => 
           (case AT.isVarOpt(t1) of 
              SOME(v) => 
                 (case coerceValIntoTerm(v2) of
                    SOME(t2) => (subVal(AthTerm.composeSubs(sub,getLegalBinding(v,t2))))
                  | _ => primError(wrongArgKind(N.extendSubFun_name,3,termLCType,v2)))
            | _ => primError(wrongArgKind(N.extendSubFun_name,2,varLCType,v1)))
      | _ => primError(wrongArgKind(N.extendSubFun_name,2,varLCType,v1)))
  | extendSubFun([subVal(sub),listVal(pair_args)],env,_) = 
      let fun getPairs([],sub,i) = sub
            | getPairs(listVal([v1,v2])::more,sub,i) = 
                (case coerceValIntoTerm(v1) of
                   SOME(t1) => 
                     (case AT.isVarOpt(t1) of 
                        SOME(v) =>  
                          (case coerceValIntoTerm(v2) of
                             SOME(t2) => getPairs(more,AT.composeSubs(sub,getLegalBinding(v,t2)),i+1)
                           | _ => primError("Wrong kind of value found in the second element of the "^
                                            ordinal(i)^" pair of the list argument to "^N.extendSubFun_name^
                                            "---"^expect(termLCType,v2)))
                      | _ => primError("Wrong kind of value found in the first element of the "^
                                       ordinal(i)^" pair of the list argument to "^N.extendSubFun_name^
                                        "---"^expect(varLCType,v1)))
                 | _ => primError("Wrong kind of value found in the first element of the "^
                                   ordinal(i)^" pair of the list argument to "^N.extendSubFun_name^
                                   "---"^expect(varLCType,v1)))
            | getPairs(v::more,sub,i) = primError("Wrong kind of value found in the "^ordinal(i)^
                                                  " position of the list argument of "^N.extendSubFun_name^
                                                  "---"^expect(listLCType,v))
          val sub' = getPairs(pair_args,sub,1)
      in
         subVal(sub')
      end
  | extendSubFun([v1,listVal(_)],_,_) = 
      primError(wrongArgKind(N.extendSubFun_name,1,subLCType,v1))
  | extendSubFun([subVal(_),v2],_,_) = 
      primError(wrongArgKind(N.extendSubFun_name,2,listLCType,v2))
  | extendSubFun([v1,_,_],_,_) = 
      primError(wrongArgKind(N.extendSubFun_name,1,subLCType,v1))
  | extendSubFun(vals,_,_) = primError(wrongArgNumberFlex(N.extendSubFun_name,length(vals),[2,3]))
and getLegalBinding(var,t) = (case AT.incSubAndReturnSubAndSuccessFlag(AT.empty_sub,(var,t)) of 
                                            (sub,true) => sub
                                          | _ => primError(N.extendSubFun_name^
                                                         " failed.\nIncompatible sorts for the binding "^(ATV.toStringDefault(var))^" --> "^
                                                         (AT.toStringDefault(t))))
         
fun isNumeralFun([v],(env,ab),{pos_ar,file}) = MLBoolToAth(isNumeralValue(v))
 | isNumeralFun(vals,_,{pos_ar,file}) = 
       evError(wrongArgNumber(N.isNumeralFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun isNumeralPrimUFun(v,env,ab) = 
   (case coerceValIntoTerm(v) of
       SOME(t) => (case (AthTerm.getNumVal(t)) of
                      SOME(_) => MLBoolToAth(true)
                    | _ => MLBoolToAth(false))
     | _ => MLBoolToAth(false))

fun fsymsInFunDefTableFun([],_,_) = 
    let val msyms = map #1 (MS.listItemsi P.fsym_def_table)
    in
      listVal(map (fn f => (case MS.find(fsym_table,f) of
                               SOME(afsym) => termConVal(regFSym(afsym))))
                  msyms)
    end
  | fsymsInFunDefTableFun(vals,_,_) = primError(wrongArgNumber(N.fsymsInFunDefTableFun_name,length(vals),0))

exception Halt

fun getStandardReduceProcNameSuffixFun([],_,_) = MLStringToAthString(Names.standardReduceProcNameTailString)
 | getStandardReduceProcNameSuffixFun(vals,_,_) = primError(wrongArgNumber("standard-reduce-proc-name-suffix",length(vals),0))

fun haltFun([],_,_) = raise Halt
  | haltFun(vals,_,_) = primError(wrongArgNumber(N.haltFun_name,length(vals),0))

fun getCurrentModPathFun([],_,_) = listVal(map (fn s => MLStringToAthString(S.name(s)))  (!Paths.current_mod_path))
  | getCurrentModPathFun(vals,_,_) = primError(wrongArgNumber(N.haltFun_name,length(vals),0))

fun makeMapFun([],_,_) = mapVal(Maps.makeMap(SV.compare))
  | makeMapFun(vals,_,_) = primError(wrongArgNumber(N.makeMapFun_name,length(vals),0))

fun getABTagFun([],_,ab) = termVal(AthTerm.makeNumTerm(A.int_num(ABase.getTag(ab),ref "")))
  | getABTagFun(vals,_,_) = primError(wrongArgNumber("get-ab-tag",length(vals),0))

fun allStructuresFun([],_,_) = 
       let val struc_name_strings = List.map (fn {name,...}:ath_structure => MS.name(name)) (Data.getAllStructures())
       in
          listVal(map MLStringToAthString struc_name_strings)
       end
  | allStructuresFun(vals,_,_) = primError(wrongArgNumber(N.getAllStructures_name,length(vals),0))

fun getDebugModeFun([],_,_) = (if !Options.detailed_stack_trace then MLStringToAthString("detailed")
                               else if !Options.stack_trace then MLStringToAthString("simple") 
                               else if !Options.rewriting_trace then MLStringToAthString("rewriting") 
                               else if !Options.conclude_trace then MLStringToAthString("conclude") 
                               else MLStringToAthString("off"))
  | getDebugModeFun(vals,_,_) = primError(wrongArgNumber(N.getDebugModeFun_name,length(vals),0))

fun setDebugModePrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
         SOME(str) => MLStringToAthString(Options.setDebugModeFlag(str,NONE))
       | _ => primError(wrongArgKind(N.setDebugModeFun_name,1,stringLCType,v)))

fun getTraceLevelFun([],_,_) = Semantics.termVal(AthTerm.makeNumTerm(AbstractSyntax.int_num(!Semantics.level,ref "")))
  | getTraceLevelFun(vals,_,_) = primError(wrongArgNumber(N.getTraceLevelFun_name,length(vals),0))

fun getFlag(name) = 
  if S.symEq(name,Names.print_var_sorts_flag_symbol) then 
           Basic.boolToString(!Options.print_var_sorts) else 
  if S.symEq(name,Names.debug_mode_flag_symbol) then 
        (case (!Options.conclude_trace,!Options.rewriting_trace,!Options.stack_trace,!Options.detailed_stack_trace) of
           (false,false,false,false) => "off"
         | (true,false,false,false) => "conclude"
         | (true,true,false,false) => "rewriting"
         | (true,true,true,false) => "simple"
         | (true,true,true,true) => "detailed"
         | _ => "off") else 
  if S.symEq(name,Names.infix_parsing_flag_symbol) then 
      Basic.boolToString(!Options.infix_parsing_option) else 
  if S.symEq(name,Names.check_fun_defs_symbol) then 
     Basic.boolToString(!Options.check_fun_defs_option) else
  if S.symEq(name,Names.demons_active_flag_symbol) then 
     Basic.boolToString(!Options.demons_active_option) else 
  if S.symEq(name,Names.fundef_mlstyle_flag_symbol) then 
     Basic.boolToString(!Options.fundef_mlstyle_option) else

  if S.symEq(name,Names.proof_tracking_flag_symbol) then 
     Basic.boolToString(!Options.proof_tracking_option) else

  if S.symEq(name,Names.simplify_fun_def_flag_symbol) then 
     Basic.boolToString(!Options.fundef_simplifying_option) else

  if S.symEq(name,Names.ATPs_in_chain_flag_symbol) then 
     Basic.boolToString(!Options.atps_in_chain_option) else

  if S.symEq(name,Names.call_stack_size_limit_flag_symbol) then 
     Int.toString(!Options.call_stack_size) else

  if S.symEq(name,Names.dom_as_dt_default_size_flag_symbol) then 
     Int.toString(!Options.dt_for_dom_default_size) else

  if S.symEq(name,Names.explicit_wildcard_patterns_flag_symbol) then 
     Int.toString(!Options.fundef_explicit_wildcard_patterns_option) else


  if S.symEq(name,Names.option_valued_selectors_flag_symbol) then 
     Basic.boolToString(!Options.option_valued_selectors_option) else

  if S.symEq(name,Names.auto_assert_dt_axioms_flag_symbol) then 
     Basic.boolToString(!Options.auto_assert_dt_axioms) else

  if S.symEq(name,Names.auto_assert_selector_axioms_flag_symbol) then 
     Basic.boolToString(!Options.auto_assert_selector_axioms) else

  if S.name(name) = "compilation" then 
     Basic.boolToString(!Options.compilation_on) 
  else Basic.fail((Symbol.name(name))^" is not a flag")

fun getBoolFlag(name) = 
  if S.symEq(name,Names.infix_parsing_flag_symbol) then 
      MLBoolToAth(!Options.infix_parsing_option) else 
  if S.symEq(name,Names.check_fun_defs_symbol) then 
     MLBoolToAth(!Options.check_fun_defs_option) else
  if S.symEq(name,Names.demons_active_flag_symbol) then 
     MLBoolToAth(!Options.demons_active_option) else 
  if S.symEq(name,Names.fundef_mlstyle_flag_symbol) then 
     MLBoolToAth(!Options.fundef_mlstyle_option) else
  if S.symEq(name,Names.ATPs_in_chain_flag_symbol) then 
     MLBoolToAth(!Options.atps_in_chain_option) else
  Basic.fail((Symbol.name(name))^" is not a boolean flag")

fun getFlagPrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
         SOME(str) => ((MLStringToAthString(getFlag(Symbol.symbol(str)))) 
                         handle Basic.Fail(msg) => primError(msg))
       | _ => primError(wrongArgKind(N.getFlagFun_name,1,stringLCType,v)))

fun getBoolFlagPrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
         SOME(str) => ((getBoolFlag(Symbol.symbol(str)))
                         handle Basic.Fail(msg) => primError(msg))
       | _ => primError(wrongArgKind(N.getBoolFlagFun_name,1,stringLCType,v)))

fun ranVarFun([subVal(sub)],_,_) = let val vars = AthTerm.rangeVars(sub)
                                       val var_vals = map (fn v => termVal(AthTerm.makeVar(v))) vars   
                                   in
                                      listVal(var_vals)
                                   end
  | ranVarFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.ranVarFun_name,1,subLCType,v),getPosOpt(pos_ar,2))
  | ranVarFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.ranVarFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun ranVarPrimUFun(subVal(sub),_,_) = 
      let val vars = AthTerm.rangeVars(sub)
          val var_vals = map (fn v => termVal(AthTerm.makeVar(v))) vars   
      in
         listVal(var_vals)
      end
  | ranVarPrimUFun(v,_,_) = primError(wrongArgKind(N.ranVarFun_name,1,subLCType,v))

fun suppFun([subVal(sub)],_,_) = 
     let val vars = AthTerm.supp(sub)
         val var_vals = map (fn v => termVal(AthTerm.makeVar(v))) vars
     in
        listVal(var_vals)
     end
  | suppFun([v],_,{pos_ar,file}) = evError(wrongArgKind(N.suppFun_name,1,subLCType,v),getPosOpt(pos_ar,2))
  | suppFun(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.suppFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun suppPrimUFun(subVal(sub),_,_) = 
     let val vars = AthTerm.supp(sub)
         val var_vals = map (fn v => termVal(AthTerm.makeVar(v))) vars
     in
        listVal(var_vals)
     end
  | suppPrimUFun(v,_,_) = primError(wrongArgKind(N.suppFun_name,1,subLCType,v))

fun proofErrorMethod([v],_,{pos_ar,file}) =  
      (case isStringValConstructive(v) of
          SOME(msg) => makeAthenaError(msg)
        | _ => evError(wrongArgKind(N.proofErrorMethod_name,1,subLCType,v),getPosOpt(pos_ar,2)))
  | proofErrorMethod(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.proofErrorMethod_name,length(vals),1),getPosOpt(pos_ar,0))

fun proofErrorPrimUMethod(v,_,_) = 
      (case isStringValConstructive(v) of
          SOME(msg) => makeAthenaError(msg)
        | _ => primError(wrongArgKind(N.proofErrorMethod_name,1,subLCType,v)))

fun compErrorPrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
          SOME(msg) => makeAthenaError(msg)
        | _ => primError(wrongArgKind(N.compErrorFun_name,1,subLCType,v)))

fun catchPrimBFun(v1,v2,env,ab) = 
     (case (v1,v2) of
        (closFunVal(e1,ref env1,_),closFunVal(e2,ref env2,_)) => 
           let val _ = (case (getClosureArity(v1),getClosureArity(v2)) of
                           (0,1) => ()
                         | (0,n) => primError("The second procedure argument given to "^(N.catchFun_name)^" must take exactly one argument,\n"^
                                              "but here it takes "^(Int.toString(n)))
                         | (n,_) =>   primError("The first procedure argument given to "^(N.catchFun_name)^" must take zero arguments,\n"^
                                                "but here it takes "^(Int.toString(n))))
           in
             ((evalClosure(v1,[],ab,NONE))
                handle EvalError(msg,_) => 
                          let val str = MLStringToAthString(msg)
                          in 
                            evalClosure(v2,[str],ab,NONE)
                          end)
           end
      | (closFunVal(_),_) => primError(wrongArgKind(N.catchFun_name,1,closFunLCType,v2))
      | (_,closFunVal(_)) => primError(wrongArgKind(N.catchFun_name,1,closFunLCType,v1)))

fun getMethodValClosureArity(closUMethodVal(_)) = 1
  | getMethodValClosureArity(closBMethodVal(_)) = 2
  | getMethodValClosureArity(closMethodVal(e,_)) = getMethodClosureArity(e)
  | getMethodValClosureArity(_) = ~1

fun catchMethod([v1,v2],(env,ab),{pos_ar,file}) = 
     if isClosMethod(v1) andalso isClosMethod(v2) then
        let val _ = (case (getMethodValClosureArity(v1),getMethodValClosureArity(v2)) of
                           (0,1) => ()
                         | (0,n) => evError("The second method argument given to "^(N.catchMethod_name)^" must take exactly one argument,\n"^
                                            "but here it takes "^(Int.toString(n)),getPosOpt(pos_ar,3))
                         | (n,_) =>   evError("The first method argument given to "^(N.catchMethod_name)^" must take zero arguments,\n"^
                                               "but here it takes "^(Int.toString(n)),getPosOpt(pos_ar,2)))
        in
             ((evalMethodClosure(v1,[],ab,getPos(pos_ar,2)))
                handle EvalError(msg,_) => 
                          let val str = MLStringToAthString(msg)
                          in 
                            evalMethodClosure(v2,[str],ab,getPos(pos_ar,3))
                          end)
        end
     else (if not(isClosMethod(v1)) then 
              evError(wrongArgKind(N.catchMethod_name,1,closMethodLCType,v1),getPosOpt(pos_ar,2))
           else evError(wrongArgKind(N.catchMethod_name,1,closMethodLCType,v2),getPosOpt(pos_ar,3)))
  | catchMethod(vals,_,{pos_ar,file}) = evError(wrongArgNumber(N.catchMethod_name,length(vals),1),getPosOpt(pos_ar,0))

fun catchPrimBMethod(v1,v2,env,ab) = 
     if isClosMethod(v1) andalso isClosMethod(v2) then
        let val _ = (case (getMethodValClosureArity(v1),getMethodValClosureArity(v2)) of
                           (0,1) => ()
                         | (0,n) => primError("The second method argument given to "^(N.catchMethod_name)^" must take exactly one argument,\n"^
                                              "but here it takes "^(Int.toString(n)))
                         | (n,_) =>   primError("The first method argument given to "^(N.catchMethod_name)^" must take zero arguments,\n"^
                                                "but here it takes "^(Int.toString(n))))
        in
             ((evalMethodClosure(v1,[],ab,A.dum_pos))
                handle EvalError(msg,_) => 
                          let val str = MLStringToAthString(msg)
                          in 
                            evalMethodClosure(v2,[str],ab,A.dum_pos)
                          end)
        end
     else (if not(isClosMethod(v1)) then 
              primError(wrongArgKind(N.catchMethod_name,1,closMethodLCType,v1))
           else primError(wrongArgKind(N.catchMethod_name,1,closMethodLCType,v2)))

fun concatFun(arg_val_list,_,_) = 
     let fun loop([],res,i) = listVal(res)
           | loop(v::more,res,i) = 
               (case v of
                   listVal(vals) => loop(more,res@vals,i+1)
                 | _ => primError(wrongArgKind(N.concatFun_name,i,listLCType,v)))
     in
       loop(arg_val_list,[],1)
     end

fun makeEvalExpFunction(env,ab) = (fn (e,binding_map) => (case binding_map of 
                                                                  NONE => Semantics.evalExp(e,env,ab)
                                                                | SOME(map) => Semantics.evalExp(e,ref(augmentWithMap(!env,map)),ab)))
          
val naive_rev_sym = Symbol.symbol("naive-rev") 
val temp_join_sym = Symbol.symbol("join")
val CE1 = A.listExp({members=[],pos=A.dum_pos})
val CE0 = A.UAppExp({proc=A.exp(A.idExp({msym=MS.makeModSymbol'([],naive_rev_sym),mods=[],sym=naive_rev_sym,no_mods=true,pos=A.dum_pos})),
                                    arg=A.exp(A.idExp({msym=MS.makeModSymbol'([],Symbol.symbol("rest")),mods=[],sym=Symbol.symbol("rest"),no_mods=true,pos=A.dum_pos})),
                                    pos=A.dum_pos})
val CE2 = A.BAppExp({proc=A.exp(A.idExp({msym=MS.makeModSymbol'([],temp_join_sym),
                                         mods=[],sym=temp_join_sym,no_mods=true,pos=A.dum_pos})),
                    arg1=A.exp(CE0),
                    arg2=A.exp(A.listExp({members=[A.exp(A.idExp({msym=MS.makeModSymbol'([],Symbol.symbol("x")),mods=[],sym=Symbol.symbol("x"),no_mods=true,pos=A.dum_pos}))],
                                          pos=A.dum_pos})),
                    pos=A.dum_pos})

fun naiveRevPrimUFun(L,env,ab) = 
      let val e_fun = makeEvalExpFunction (env,ab)
      in
         (case Semantics.matchPat(L,A.listPats({member_pats=[],pos=A.dum_pos}),e_fun) of 
             SOME(map,_) => let val new_env = ref(augmentWithMap(!env,map))
                          in
                            Semantics.evalExp(CE1,new_env,ab)
                          end
           | _ => (case Semantics.matchPat(L,A.listPat({head_pat=A.idPat({name=Symbol.symbol("x"),pos=A.dum_pos,sort_as_sym_term=NONE,op_tag=NONE,
                                                                          sort_as_fterm=NONE,sort_as_exp=NONE}),
                                                     tail_pat=A.idPat({name=Symbol.symbol("rest"),pos=A.dum_pos,sort_as_sym_term=NONE,op_tag=NONE,
                                                                       sort_as_fterm=NONE,sort_as_exp=NONE}),pos=A.dum_pos}),e_fun) of
                       SOME(map,_) => let val new_env = ref(augmentWithMap(!env,map))
                                    in
                                       Semantics.evalExp(CE2,new_env,ab)
                                    end
                     | _ => primError("match failed---the "^valLCTypeAndStringNoColon(L)^
                                      "\ndid not match any of the given patterns")))
      end

fun naiveRevPrimUFun2(L,env,ab) = 
         (case L of
             listVal([]) => listVal([])
           | listVal(x::rest) => let val listVal(L1) = naiveRevPrimUFun2(listVal(rest),env,ab)
                                 in
                                    listVal(L1@[x])
                                 end)

fun naiveRevPrimUFun3(listVal(L),env,ab) = listVal(Basic.nrev(L))

fun naiveAppendPrimBFun(listVal(L1),L2,env,ab) = 
   (case L1 of
      [] => L2
    | x::rest => consPrimBFun(x,naiveAppendPrimBFun(listVal(rest),L2,env,ab),env,ab))
   
fun doFetchTest(propTest,env,ab,pos) = 
             let fun test(p) = let val v = propTest(p) 
                               in
                                  case coerceValIntoTerm(v) of
                                     SOME(t) => AthTerm.termEq(t,true_term)
                                   | _ => evError("The test procedure given to "^N.fetchFun_name^" must "^
                                                  "produce either true or false---but here\nit produced the "^
                                                   valLCTypeAndString(v),SOME(pos))
                               end
             in    
                case ABase.fetch(ab,test) of                           
                   SOME(P) => propVal(P)
                 | _ => unitVal
             end  

fun doFetchTest1(propTest,env,ab) = 
             let fun test(p) = let val v = propTest(p) 
                               in
                                  case coerceValIntoTerm(v) of
                                     SOME(t) => AthTerm.termEq(t,true_term)
                                   | _ => primError("The test procedure given to "^N.fetchFun_name^" must "^
                                                    "produce either true or false---but here\nit produced the "^
                                                     valLCTypeAndString(v))
                               end
             in    
                case ABase.fetch(ab,test) of                           
                   SOME(P) => propVal(P)
                 | _ => unitVal
             end  

fun doFetchAllTest(propTest,env,ab,pos) = 
             let fun test(p) = let val v = propTest(p) 
                               in
                                  case coerceValIntoTerm(v) of
                                     SOME(t) => AthTerm.termEq(t,true_term)
                                   | _ => evError("The test procedure given to "^N.fetchFun_name^" must "^
                                                  "produce either true or false---but here\nit produced the "^
                                                   valLCTypeAndString(v),SOME(pos))
                               end
             in    
                propLstToAthPropLst(ABase.fetchAll(ab,test))
             end

fun doFetchAllTest1(propTest,env,ab) = 
             let fun test(p) = let val v = propTest(p) 
                               in
                                  case coerceValIntoTerm(v) of
                                     SOME(t) => AthTerm.termEq(t,true_term)
                                   | _ => primError("The test procedure given to "^N.fetchFun_name^" must "^
                                                    "produce either true or false---but here\nit produced the "^
                                                    valLCTypeAndString(v))
                               end
             in    
                propLstToAthPropLst(ABase.fetchAll(ab,test))
             end

fun fetchPrimUFun(v,env,ab) = 
      (case v of
          closUFunVal(body,param,clos_env as ref(valEnv({val_map,mod_map,...})),_) =>                    
             doFetchTest1(fn P => let val vm = Symbol.enter(val_map,param,propVal(P))
                                  in 
                                     Semantics.evalExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab)
                                  end,env,ab)
        | primUFunVal(f,_) => doFetchTest1((fn P => f(propVal(P),env,ab)),env,ab)
        | _ => primError(wrongArgKind(N.fetchFun_name,1,closFunLCType,v)))

fun fetchAllPrimUFun(v,env,ab) = 
      (case v of
          closUFunVal(body,param,clos_env as ref(valEnv({val_map,mod_map,...})),_) =>                    
             doFetchAllTest1(fn P => let val vm = Symbol.enter(val_map,param,propVal(P))
                                     in 
                                        Semantics.evalExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab)
                                     end,env,ab)
        | primUFunVal(f,_) => doFetchAllTest1((fn P => f(propVal(P),env,ab)),env,ab)
        | _ => primError(wrongArgKind(N.fetchAllFun_name,1,closFunLCType,v)))

fun stringToNumFun(args as [v],(env,ab),{pos_ar,file}) = 
 let fun error(str) = evError("Failed application of "^N.stringToNumFun_name^"---the\ngiven string, \""^
                              str^"\", does not represent a numeric term",
                              getPosOpt(pos_ar,2))
 in
      (case isStringValConstructive(v) of
         SOME(str) => 
                    (case AbstractSyntax.getAthNumber(str) of
                        SOME(anum) => termVal(AthTerm.makeNumTerm(anum))
                      | _ => if String.sub(str,0) = #"-" then 
                                (case AbstractSyntax.getAthNumber(String.substring(str,1,String.size(str) - 1)) of
                                    SOME(anum) => termVal(AT.makeApp(Names.msubtraction_symbol,[AT.makeNumTerm(anum)]))
                                  | _ => error(str))
                              else error(str))
       | _ => evError(wrongArgKind(N.stringToNumFun_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  end
  | stringToNumFun(args,(env,ab),{pos_ar,file}) = 
         evError(wrongArgNumber(N.stringToNumFun_name,length(args),1),getPosOpt(pos_ar,0))

fun stringToNumPrimUFun(v,env,ab) = 
 let fun error(str) = primError("Failed application of "^N.stringToNumFun_name^"---the\ngiven string, \""^
                                str^"\", does not represent a numeric term")
 in
      (case isStringValConstructive(v) of
         SOME(str) => 
                    (case AbstractSyntax.getAthNumber(str) of
                        SOME(anum) => termVal(AthTerm.makeNumTerm(anum))
                      | _ => if String.sub(str,0) = #"-" then 
                                (case AbstractSyntax.getAthNumber(String.substring(str,1,String.size(str) - 1)) of
                                    SOME(anum) => termVal(AT.makeApp(Names.msubtraction_symbol,[AT.makeNumTerm(anum)]))
                                  | _ => error(str))
                              else error(str))
       | _ => primError(wrongArgKind(N.stringToNumFun_name,1,stringLCType,v)))
  end

datatype num_const = intConst of int | realConst of real

fun isNumericConstant(s,minus_sign,op_name,i,pos) = 
  let fun f(t,negative) = 
       (case AthTerm.isNumConstantOpt(t) of
           SOME(A.int_num(i,_)) => if negative then intConst(~i) else intConst(i)
         | SOME(A.real_num(r,_)) => if negative then realConst(~r) else realConst(r)
         | _ => (case AthTerm.isApp(t) of 
                    SOME(g,args) => if MS.modSymEq(g,minus_sign) then f(hd(args),not(negative)) else
                                       evError(wrongArgKind(op_name,i,numTermLCType,termVal(t)),SOME(pos))
                  | _ => evError(wrongArgKind(op_name,i,numTermLCType,termVal(t)),SOME(pos))))
  in
     f(s,false)
  end

(*************************************************************************************************************)
(*                                       TOP-LEVEL METHODS                                                   *)
(*************************************************************************************************************)

fun claimPrimUMethod(v,env,ab) = 
        (case coerceValIntoProp(v) of
            SOME(p) => (checkOneAbMemberNoPos(p,ab,N.claimPrimMethod_name);propVal(p))
          | _ => primError(wrongArgKind(N.claimPrimMethod_name,1,propLCType,v)))


fun mpPrimBMethod(v1,v2,env,ab) =  
      (case getTwoProps(v1,v2,N.mpPrimMethod_name,env) of 
          plst as [P,Q] =>
	    (case P.isCond(P) of
		SOME(P1,P2) => let val _ = checkAbMembersNoPos(plst,ab,N.mpPrimMethod_name) 
		                   fun decide(str) = if Util.small(str,40) then str else "\n"^str
		               in
		                if P.alEq(P1,Q) then
		                   propVal(P2)
		                else
		                   primError("Failed application of "^N.mpPrimMethod_name^"---"^
	                           "the second given sentence should be\nidentical to the antecedent "^
				   "of the first, "^"namely: "^decide(pprint(0,P1))^".\nInstead, it was this:\n"^
	                           pprint(0,Q))
		              end
             | _ => primError(dwrongArgKind(N.mpPrimMethod_name,1,"a conditional",P))))

fun absurdPrimBMethod(v1,v2,env,ab) = 
       let val mname = N.absurdPrimMethod_name 
           fun msg(P1,P2) = "Failed application of "^mname^"---the second\ngiven sentence must be the "^
                            "negation of the first, namely:\n"^pprint(0,P1)^
                            "\nInstead, it was this: "^pprint(23,P2)
       in
          (case getTwoProps(v1,v2,mname,env) of 
              plst as [P1,P2] =>
                (case P.isNeg(P2) of
		   SOME(P1') => 
	                  if Prop.alEq(P1,P1') then 
	                     (checkAbMembersNoPos(plst,ab,N.absurdPrimMethod_name);propVal(Prop.makeFalseProp()))
	                  else
	                     primError(msg(Prop.makeNegation(P1),P2))
                 | _ => primError(msg(Prop.makeNegation(P1),P2))))
       end

fun appMethodMethod(args as [v,listVal arg_vals],env,ab) = 
       let val mname = N.appMethod_method_name
       in
          (case v of
             closUMethodVal(body,parameter,clos_env,name) =>
                 let val (vmap,mmap) = getValAndModMaps(!clos_env)
                     val arg_val = (case arg_vals of 
                                      [v] => v
                                    | _ => let val name' = !name
                                           in 
                                              if name' = "" then
                                                 primError("Wrong number of arguments ("^(Int.toString(length(arg_vals)))^") given to unary method")
                                              else   
                                                 primError("Wrong number of arguments ("^(Int.toString(length(arg_vals)))^") given to unary method "^name')
                                           end)
                     val new_env = ref(valEnv({val_map=Symbol.enter(vmap,parameter,arg_val),mod_map=mmap}))
                 in
                    evalDed(body,new_env,ab)
                 end 
           | closBMethodVal(body,parameter1,parameter2,clos_env,name_ref) =>
                 let val (vmap,mmap) = getValAndModMaps(!clos_env)
                     val name = !name_ref
                     val [arg_val1,arg_val2] = 
                                  (case arg_vals of 
                                      [_,_] => arg_vals
                                    | _ => primError("Wrong number of arguments ("^(Int.toString(length(arg_vals)))^") given to binary method "^name))
                     val new_env = ref(valEnv({val_map=Symbol.enter(Symbol.enter(vmap,parameter1,arg_val1),parameter2,arg_val2),mod_map=mmap}))
                 in
                    evalDed(body,new_env,ab)
                 end 
            | closMethodVal(A.methodExp({params,body,pos=mexp_pos,name=rname,...}),clos_env) => 
                 let val (vmap,mmap) = getValAndModMaps(!clos_env)
                     val new_env = ref(valEnv({val_map=enterParamValLst(vmap,params,arg_vals),mod_map=mmap}))
                 in
                    evalDed(body,new_env,ab)
                 end 
            | methodVal(f,string) => f(arg_vals,env,ab)
            | primUMethodVal(f,_) => f(hd arg_vals,env,ab)
            | primBMethodVal(f,_) => f(hd arg_vals,hd(tl(arg_vals)),env,ab)
            | v =>  primError(wrongArgKind(N.appMethod_method_name,1,methodLCType,v)))
       end
  | appMethodMethod([_,v2],env,ab) = primError(wrongArgKind(N.appMethod_method_name,2,listLCType,v2))
  | appMethodMethod(args,env,ab) = primError(wrongArgNumber(N.appMethod_method_name,length(args),2))

fun appProcPrimBFun(v1,v2,env,ab) = 
   (case v2 of
     listVal(arg_vals) =>
       let val mname = N.appProc_proc_name
       in
          (case v1 of
              primUFunVal(f,{name,...}) => let val arg_num = length(arg_vals)
                                           in
                                              if not(arg_num = 1) then
                                                 primError("Failed application of "^N.appProc_proc_name^": wrong number of arguments ("^(Int.toString(arg_num))^
                                                           ") supplied to unary procedure "^name)
                                              else f(hd arg_vals,env,ab)
                                           end
            | primBFunVal(f,{name,...}) => let val arg_num = length(arg_vals)
                                           in
                                              if not(arg_num = 2) then
                                                 primError("Failed application of "^N.appProc_proc_name^": wrong number of arguments ("^(Int.toString(arg_num))^
                                                         ") supplied to binary procedure "^name)
                                              else f(hd arg_vals,hd(tl(arg_vals)),env,ab)
                                           end
            | funVal(f,string,_) => f(arg_vals,env,ab)
            | _ => evalClosure(v1,arg_vals,ab,NONE))
       end
    | _ => primError(wrongArgKind(N.appProc_proc_name,2,listLCType,v2)))

fun propKind1(P) = let val str = Prop.propKind(P) in if str = "a negation" then "a single negation" else str end

fun isDoubleNegation(P) = 
  (case P.isNeg(P) of 
      SOME(Q) => P.isNeg(Q)
    | _ => NONE)

fun forcePrimMethod(args as [v],(env,ab),{pos_ar,file}) = 
       (case coerceValIntoProp(v) of
           SOME(prop) => propVal(prop)
         | _ => evError(wrongArgKind(N.force_name,1,propLCType,v),getPosOpt(pos_ar,2)))
  | forcePrimMethod(args,(env,ab),{pos_ar,file}) = 
      evError(wrongArgNumber(N.bothPrimMethod_name,length(args),1),getPosOpt(pos_ar,0))

fun forcePrimUMethod(v,env,ab) = 
       (case coerceValIntoProp(v) of
           SOME(prop) => propVal(prop)
         | _ => primError(wrongArgKind(N.force_name,1,propLCType,v)))

fun dnPrimUMethod(v,env,ab) = 
     (case coerceValIntoProp(v) of
         SOME(prop) =>
           (case isDoubleNegation(prop) of
	       SOME(P) => (checkOneAbMemberNoPos(prop,ab,N.dnPrimMethod_name);propVal(P))
             | _ => primError("Failed application of "^N.dnPrimMethod_name^"---"^
                              "the given sentence\nshould be a double negation, but "^
                              "instead it was "^propKind1(prop)^":\n"^pprint(0,prop))))

fun bothPrimBMethod(v1,v2,env,ab) = 
       (case getTwoProps(v1,v2,N.bothPrimMethod_name,env) of
           plst as [P1,P2] => (checkAbMembersNoPos(plst,ab,N.bothPrimMethod_name);
                               propVal(Prop.makeConjunction(plst))))

fun conjIntroPrimMethod([listVal(vals)],(env,ab),{pos_ar,file}) = 
       let val pplst = rev(coercePositionedValsIntoPropsAndPositionCopies(vals,Array.sub(pos_ar,0),N.conjIntroPrimMethod_name))
       in 
         (checkAbMembers(pplst,ab,N.conjIntroPrimMethod_name);
                     propVal(Prop.makeConjunction(#1(Basic.unZip(pplst)))))
       end
  | conjIntroPrimMethod(args,(env,ab),{pos_ar,file}) = 
       evError(wrongArgNumber(N.conjIntroPrimMethod_name,length(args),1),getPosOpt(pos_ar,0))

fun conjIntroPrimUMethod(listVal(vals),env,ab) = 
      (case getAProps(vals,N.conjIntroPrimMethod_name,env) of
         pplst => (checkAbMembersNoPos(pplst,ab,N.conjIntroPrimMethod_name);
                   propVal(Prop.makeConjunction(pplst))))
  | conjIntroPrimUMethod(v,env,ab) = 
        primError(wrongArgKind(N.conjIntroPrimMethod_name,1,"list of sentences",v))

fun failPrimMethod([v],env,ab) = 
       (case isStringValConstructive(v) of
           SOME(msg) => primError(msg)
         | _ => primError(wrongArgKind(N.fail_method_name,1,stringLCType,v)))
  | failPrimMethod([],env,ab) = primError("Proof failure")

fun failPrimUMethod(v,env,ab,{pos_ar,file}) = 
       (case isStringValConstructive(v) of
           SOME(msg) => primError(msg)
         | _ => primError(wrongArgKind(N.fail_method_name,1,stringLCType,v)))

fun leftAndPrimUMethod(v,env,ab) = 
     (case coerceValIntoProp(v) of
           SOME(P) => 
              (case P.isConj(P) of
	 	  SOME(P1::_) => (checkOneAbMemberNoPos(P,ab,N.leftAndPrimMethod_name);
                                  propVal(P1))
               | _ => primError("Failed application of "^N.leftAndPrimMethod_name^"---"^
                                "the given sentence must be\n"^"a conjunction, "^
                                "but here it was "^Prop.propKind(P)^": "^
	   		        (Util.decide(pprint(0,P),16))))
         | _ => primError(getPropArgMessage(v,1,N.leftAndPrimMethod_name)))

fun rightAndPrimUMethod(v,env,ab) = 
     (case coerceValIntoProp(v) of
           SOME(P) => 
              (case P.isConj(P) of
	 	  SOME([_,P2]) => (checkOneAbMemberNoPos(P,ab,N.rightAndPrimMethod_name);
                                   propVal(P2))
               |  SOME(P1::rest) => (if null(rest) then 
                                      primError("Failed application of "^N.rightAndPrimMethod_name^"---"^
				                "the given conjunction must have at least two elements.\n"^
                                                "But here it had one element only:\n"^pprint(0,P1))
                                    else (checkOneAbMemberNoPos(P,ab,N.rightAndPrimMethod_name);
                                          propVal(P.makeConjunction(rest))))
               | _ => primError("Failed application of "^N.rightAndPrimMethod_name^"---"^
                                "the given sentence must be\n"^"a conjunction, "^
                                "but here it was "^Prop.propKind(P)^": "^
	   		        (Util.decide(pprint(0,P),16))))
         | _ => primError(getPropArgMessage(v,1,N.leftAndPrimMethod_name)))

fun equivPrimBMethod(v1,v2,env,ab) = 
     let val mname = N.equivPrimMethod_name 
         fun msg1(must,instead) = 
                           "Failed application of "^mname^"---the second given conditional must be the "^
                           "converse of the first,\nnamely: "^pprint(8,must)^
                           "\nInstead, it was this: "^pprint(22,instead)
         fun msg2(ord,given) = "Failed application of "^mname^"---the "^ord^" given sentence must be\n"^
                               "a conditional, but here it was "^Prop.propKind(given)^":\n"^
                                pprint(0,given)
     in
       (case getTwoProps(v1,v2,N.equivPrimMethod_name,env) of
            plst as [prop1,prop2] => 
               (case (P.isCond(prop1),P.isCond(prop2)) of
		   (SOME(P1,P2),SOME(P3,P4)) => 
                       if Prop.alEq(P3,P2) andalso Prop.alEq(P4,P1) then
                          (checkAbMembersNoPos(plst,ab,N.equivPrimMethod_name);
			   propVal(Prop.makeBiConditional(P1,P2)))
                       else    
                          primError(msg1(Prop.makeConditional(P2,P1),prop2))
                | (NONE,_) => primError(msg2("first",prop1))
                | (SOME(_),NONE) => primError(msg2("second",prop2))))
     end

fun leftIffPrimUMethod(v,env,ab) = 
     (case coerceValIntoProp(v) of
           SOME(P) => 
             (case P.isBiCond(P) of
		SOME(P1,P2) => 
	             (checkOneAbMemberNoPos(P,ab,N.leftIffPrimMethod_name);
                      propVal(Prop.makeConditional(P1,P2)))
             | _ => primError("Failed application of "^N.leftIffPrimMethod_name^"---"^
                              "the given sentence must be\n"^"a biconditional, "^
                              "but here it was "^Prop.propKind(P)^":\n"^pprint(0,P)))
        | _ => primError(getPropArgMessage(v,1,N.leftIffPrimMethod_name)))

fun rightIffPrimUMethod(v,env,ab) = 
     (case coerceValIntoProp(v) of
           SOME(P) => 
             (case P.isBiCond(P) of
		SOME(P1,P2) => 
	             (checkOneAbMemberNoPos(P,ab,N.leftIffPrimMethod_name);
                      propVal(Prop.makeConditional(P2,P1)))
             | _ => primError("Failed application of "^N.rightIffPrimMethod_name^"---"^
                              "the given sentence must be\n"^"a biconditional, "^
                              "but here it was "^Prop.propKind(P)^":\n"^pprint(0,P)))
        | _ => primError(getPropArgMessage(v,1,N.leftIffPrimMethod_name)))

fun leftEitherPrimBMethod(v1,v2,env,ab) = 
       (case getTwoProps(v1,v2,N.leftEitherPrimMethod_name,env) of
           plst as [P1,_] => 
              if ABase.isMember(P1,ab) then
                 propVal(Prop.makeDisjunction(plst))
              else
                 primError("Failed application\nof "^N.leftEitherPrimMethod_name^"---the sentence:\n"^
                         pprint(0,P1)^"\nis not in the assumption base."))

fun rightEitherPrimBMethod(v1,v2,env,ab) = 
       (case getTwoProps(v1,v2,N.leftEitherPrimMethod_name,env) of
           plst as [_,P2] => 
              if ABase.isMember(P2,ab) then
                 propVal(Prop.makeDisjunction(plst))
              else
                 primError("Failed application\nof "^N.rightEitherPrimMethod_name^"---the sentence:\n"^
                         pprint(0,P2)^"\nis not in the assumption base."))

fun eitherPrimBMethod(v1,v2,env,ab) = 
       (case getTwoProps(v1,v2,N.eitherPrimMethod_name,env) of
           plst as [P1,P2] => 
              if ABase.isMember(P1,ab) orelse ABase.isMember(P2,ab) then
                 propVal(Prop.makeDisjunction(plst))
              else
                 primError("Failed application of "^N.eitherPrimMethod_name^"---neither the first sentence:\n"^
                         pprint(0,P1)^"\nnor the second sentence:\n"^
                         pprint(0,P2)^"\nis in the assumption base"))

fun eitherPrimMethod([v1,v2],env,ab) = 
       (case getTwoProps(v1,v2,N.eitherPrimMethod_name,env) of
           plst as [P1,P2] => 
              if ABase.isMember(P1,ab) orelse ABase.isMember(P2,ab) then
                 propVal(Prop.makeDisjunction(plst))
              else
                 primError("Failed application of "^N.eitherPrimMethod_name^"---neither the first sentence:\n"^
                         pprint(0,P1)^"\nnor the second sentence:\n"^
                         pprint(0,P2)^"\nis in the assumption base"))
  | eitherPrimMethod([v],env,ab) = 
     (case v of
       listVal(vals) =>
         let val pplst = Semantics.getAProps(vals,N.eitherPrimMethod_name,env)
  	     val res = if (List.exists (fn P => ABase.isMember(P,ab)) pplst) then propVal(P.makeDisjunction(pplst))
                       else 
	  	         primError("Failed application of "^N.eitherPrimMethod_name^"---none of the\n"^
		    	           "given sentences are in the assumption base")
         in  
            res
         end
   | propVal(d) => (case Prop.isDisj(d) of
                       SOME(_) => let val pplst = Prop.getDisjunctsWithoutDups(d) 
            	                      val res = if (List.exists (fn P => ABase.isMember(P,ab)) pplst) then v 
                                                else 
	  	                                primError("Failed application of "^N.eitherPrimMethod_name^"---none of the\n"^
		    	                                  "given sentences are in the assumption base")
                                  in
                                     res
                                  end
                     | _ => primError(wrongArgKind(N.eitherPrimMethod_name,1,"disjunction",v)))
  | _ => primError(wrongArgKind(N.eitherPrimMethod_name,1,"disjunction",v)))
  | eitherPrimMethod(vals,env,ab) = primError(wrongArgNumber(N.eitherPrimMethod_name,length(vals),2))

fun cdPrimMethod(arg_vals as _::_::_,env:value_environment ref,ab) = 
     let val mname = N.cdPrimMethod_name 
         fun msg2(ord,kind,given) = 
                               "Failed application of "^mname^"---the "^ord^" given sentence\nshould be "^
                               "a "^kind^", but here it was "^Prop.propKind(given)^":\n"^
                                pprint(0,given)
         fun msg3(i,given,must) = let val _ = ()
                                    in
                                      "Failed application of "^mname^"---the antecedent of the\n"^
                                     ordinal(i-1)^" given "^
                                      "conditional must be identical to the "^ordinal(i-1)^" component\n"^
                                      "of the given disjunction, namely:\n"^pprint(0,must)^
                                      "\nInstead, it was this:\n"^pprint(0,given)
                                    end
         fun msg3'(i,given,must,cases) = 
                            "Failed application of "^mname^"---the antecedent of the\n"^
                                    ordinal(i-1)^" given "^
                                      "conditional, namely\n"^(pprint(0,given))^"\nwas not one of the disjunctive cases, namely: " ^
                                    (Basic.printListStr(cases,(fn p => pprint(0,p)),", "))
         fun msg4(given,must) = "Failed application of "^mname^". All given conditionals should have\n"^
                                "the same consequent, but in this case, two different consequents were found:\n"^
                                pprint(0,must)^"\nand\n"^pprint(0,given)
       val T: (P.prop,bool) HashTable.hash_table = HashTable.mkTable(P.hash, P.alEq) (30,Data.GenEx("Failed table creation"))
       fun alreadySeen(p) = (case (HashTable.find T p) of 
                                SOME(_) => true
                              | _ => let val _ = HashTable.insert  T (p,true)
                                     in
   			               false 
                                     end)
       fun checkConds(props,cases) = 
          let val antecedent_disjuncts = ref([[]])
              fun f([],[],_,concl,not_in_ab) = (concl,not_in_ab)
                | f(imp::more_props,remaining_cases as (C::more_cases),i,concl,not_in_ab) = 
                   (case P.isCond(imp) of
		     SOME(P1,P2) => if alreadySeen(P1) then f(more_props,remaining_cases,i+1,concl,not_in_ab)
		                    else 
                                    if not(Prop.alEq(P2,concl)) then primError(msg4(P2,concl))
                                    else let val _ = antecedent_disjuncts := (P.getDisjunctsWithoutDups(P1))::(!antecedent_disjuncts)
                                         in
                                          (case Basic.findAndSplit(remaining_cases,fn C => Prop.alEq(P1,C),Prop.alEq) of 
                                             (SOME(_),rest_cases) => (case not_in_ab of
                                                                        SOME(_) => f(more_props,rest_cases,i+1,concl,not_in_ab)
                                                                      | _ => if ABase.isMember(imp,ab) then 
                                                                                f(more_props,rest_cases,i+1,concl,NONE)
                                                                             else f(more_props,rest_cases,i+1,concl,SOME(imp)))
                                           | _ => (primError(msg3'(i,P1,C,cases))))
                                          end
                 | _ => primError(msg2(ordinal(i),"conditional",imp)))
                | f(imp::more_props,[],i,concl,not_in_ab) = 
                         (case P.isCond(imp) of
                            SOME(P1,P2) => let val _ = alreadySeen(P1)
                                           in
                                              f(more_props,[],i+1,concl,not_in_ab)
                                           end
                          | _ => primError(msg2(ordinal(i),"conditional",imp)))
                | f([],rem_cases:Prop.prop list as C::_,i,concl,not_in_ab) = 
                       let val remaining_cases_flattened = Basic.flatten (List.map Prop.getDisjuncts rem_cases) 
                       in
                         if Basic.subsetEq(remaining_cases_flattened,Basic.flatten(!antecedent_disjuncts),P.alEq) 
                         then (concl,not_in_ab) else 
                          primError("Failed application of "^mname^"---the given conditionals\n"^
                                             "do not exhaust the disjunction; the following case is not covered:\n"^
                                             pprint(0,C))
                       end 
         in
            (case (props,cases) of
               (P::more_props,all_cases as (C::more_cases)) =>
                 (case P.isCond(P) of
		    SOME(P1,P2) => let val _ = alreadySeen(P1)
                                   in
                                   (case Basic.findAndSplit(all_cases,fn C => Prop.alEq(P1,C),Prop.alEq) of 
                                       (SOME(_),rest_cases) => (antecedent_disjuncts := (P.getDisjunctsWithoutDups(P1))::(!antecedent_disjuncts);
                                                                if ABase.isMember(P,ab) then f(more_props,rest_cases,3,P2,NONE)
                                                               else f(more_props,rest_cases,3,P2,SOME(P)))
                                     | _ => primError(msg3'(2,P1,C,cases)))
                                   end
                  | _ =>  primError(msg2(ordinal(2),"conditional",P)))
             | ([],_::_) => primError("Failed application of "^mname^"."^Int.toString(length(cases))^
                                      " conditionals were expected; none were found")
             | (_,[]) => raise Basic.Never)
         end
     in        
       (case ((coercePositionlessValsIntoProps(rev(arg_vals),N.cdPrimMethod_name)) handle _ => []) of
            plst as alt::rest => 
              (case (P.getDisjunctsWithoutDups alt) of
		  (cases as (case_1::_)) => 
                     (case checkConds(rest,cases) of
                       res => if ABase.isMember(alt,ab) then 
                                 (case res of 
                                    (concl,NONE) => propVal(concl)
                                  | (_,SOME(imp)) => 
                                        primError("Failed application of "^mname^"---the conditional\n"^
                                                  pprint(0,imp)^"\nis not in the assumption base"))
                               else primError("Failed application of "^mname^"---the disjunction\n"^
                                              pprint(0,alt)^"\nis not in the assumption base"))
              | _ => primError(msg2("first","disjunction",alt)))
          | _ => (case (coerceValIntoProp(hd(arg_vals)),tl(arg_vals)) of
                     (SOME(alt),[listVal(implications)]) => 
                         let val rest = coercePositionlessValsIntoProps(rev(implications),N.cdPrimMethod_name)
                         in
                               (case (P.getDisjunctsWithoutDups alt) of
                	 	  (cases as (case_1::_)) => 
                                     (case checkConds(rest,cases) of
                                        res => if ABase.isMember(alt,ab) then 
                                               (case res of 
                                                  (concl,NONE) => propVal(concl)
                                               | (_,SOME(imp)) => 
                                                        primError("Failed application of "^mname^"---the conditional\n"^
                                                                  pprint(0,imp)^"\nis not in the assumption base"))
                                               else primError("Failed application of "^mname^"---the disjunction\n"^
                                                              pprint(0,alt)^"\nis not in the assumption base"))
                                    | _ => primError(msg2("first","disjunction",alt)))
                          end)

       )
     end
  | cdPrimMethod(args,_,_) = 
        primError("Wrong number of arguments ("^Int.toString(length(args))^") given to "^N.cdPrimMethod_name^";\nat least two arguments are required")

fun applyExtractedSortSubFun([v1,v2],env,ab) = 
    (case coerceValIntoProp(v1) of
       SOME(p) => 
          (case coerceValIntoTerm(v2) of
              SOME(t) => (case P.applyExtractedSortSub(p,t) of
                             SOME(q) => propVal(q)    
                           | _ => unitVal)
            | _ => primError(wrongArgKind(N.applyExtractedSortSubFun_name,2,termLCType,v2)))
     | _ => primError(wrongArgKind(N.applyExtractedSortSubFun_name,1,propLCType,v1)))
  | applyExtractedSortSubFun(vals,_,_) = primError(wrongArgNumber(N.applyExtractedSortSubFun_name,length(vals),3))


fun getSelectorsFun([termConVal(regFSym(some_fsym))],_,{pos_ar,file}) = 
       let val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
       in
         (case (StructureAnalysis.isStructureConstructorOpt name) of     
             NONE => evError("Wrong kind of argument given to "^N.getSelectorsFun_name^
                              "---a constructor was expected,\nbut the given argument was "^MS.name(name)^
                              ", which is is not a constructor",getPosOpt(pos_ar,2))
           | SOME({selectors,...}) => let val sel_names = List.map (fn SOME(name) => MS.name(name)
                                                                     | NONE => "")
                                                          selectors
                                      in 
                                         listVal(map MLStringToAthString sel_names)
                                      end)
       end
  | getSelectorsFun([v],_,{pos_ar,file}) = 
           evError(wrongArgKind(N.getSelectorsFun_name,1,"constructor",v),getPosOpt(pos_ar,2))
  | getSelectorsFun(vals,_,{pos_ar,file}) = 
        evError(wrongArgNumber(N.getSelectorsFun_name,length(vals),1),getPosOpt(pos_ar,0))


fun getSelectorsPrimUFun(v,_,_) = 
   (case coerceValIntoTermConVal(v) of 
     SOME(termConVal(regFSym(some_fsym))) =>
       let val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
       in
         (case (StructureAnalysis.isStructureConstructorOpt name) of     
             NONE => primError("Wrong kind of argument given to "^N.getSelectorsFun_name^
                               "---a constructor was expected,\nbut the given argument was "^MS.name(name)^
                               ", which is is not a constructor")
           | SOME({selectors,...}) => let val sel_names = List.map (fn SOME(name) => MS.name(name)
                                                                     | NONE => "")
                                                          selectors
                                      in 
                                         listVal(map MLStringToAthString sel_names)
                                      end)
       end
  | _ => primError(wrongArgKind(N.getSelectorsFun_name,1,"constructor",v)))

fun constructorInjAux([termConVal(regFSym(some_fsym))],_,{pos_ar,file},free) = 
       let val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
           fun msg() = evError("Wrong kind of argument given to "^N.constructor_inj_name^
                              "---a constructor was expected,\nbut the given argument was "^MS.name(name)^
                              ", which is is not a constructor",getPosOpt(pos_ar,2))
	   val _ = if not(free) then ()
                   else 
                    (case ((StructureAnalysis.isStructureConstructorAsMS) name) of
		       NONE => msg()
		     | SOME(sname) => if not(StructureAnalysis.isFreeStructure(sname)) 
				      then evError(N.constructor_inj_name^" requires a datatype "^
							 "constructor as an argument. The given argument, "^
							 MS.name(name)^", is a structure constructor",
							 getPosOpt(pos_ar,2))
				      else ())
           val (vars1,vars2) = (StructureAnalysis.getFirstNVars(arity,"x"),StructureAnalysis.getFirstNVars(arity,"y"))
           val (vars1_terms,vars2_terms) = (map AthTerm.makeVar vars1,map AthTerm.makeVar vars2)
           val t1 = applyTermConstructor(name,arity,vars1_terms,A.dum_pos)
           val t2 = applyTermConstructor(name,arity,vars2_terms,A.dum_pos) 
           val antecedent = Prop.makeEquality(t1,t2)
           val equalities = map Prop.makeEquality (ListPair.zip(vars1_terms,vars2_terms))
           val consequent = (case equalities of
			       [P] => P
			     | _ => Prop.makeConjunction(equalities))
       in
          propVal(Prop.makeUGen(vars1@vars2,Prop.makeBiConditional(antecedent,consequent)))
       end  
  | constructorInjAux([v as termVal(t)],_,{pos_ar,file},_) = 
      (case AthTerm.isConstant(t) of 
          SOME(cname) => if StructureAnalysis.isConstantStructureConstructor(cname) then
                            evError("Nullary constructor ("^MS.name(cname)^") given as argument "^
                                    "to "^N.constructor_inj_name^";\na constructor "^
                                    "of positive arity is required",getPosOpt(pos_ar,2))
                         else evError(wrongArgKind(N.constructor_inj_name,1,"constructor",v),getPosOpt(pos_ar,2))
        | _ => evError(wrongArgKind(N.constructor_inj_name,1,"constructor",v),getPosOpt(pos_ar,2)))
  | constructorInjAux([v],_,{pos_ar,file},_) = 
           evError(wrongArgKind(N.constructor_inj_name,1,"constructor",v),getPosOpt(pos_ar,2))
  | constructorInjAux(args,_,{pos_ar,file},_) = 
        evError(wrongArgNumber(N.constructor_inj_name,length(args),1),getPosOpt(pos_ar,0))    

fun constructorInjAuxPrimUMethod(termConVal(regFSym(some_fsym)),env,ab,free) = 
       let val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
           fun msg() = primError("Wrong kind of argument given to "^N.constructor_inj_name^
                              "---a constructor was expected,\nbut the given argument was "^MS.name(name)^
                              ", which is is not a constructor")
	   val _ = if not(free) then ()
                   else 
                    (case ((StructureAnalysis.isStructureConstructorAsMS) name) of
		       NONE => msg()
		     | SOME(sname) => if not(StructureAnalysis.isFreeStructure(sname)) 
				      then primError(N.constructor_inj_name^" requires a datatype "^
							 "constructor as an argument. The given argument, "^
							 MS.name(name)^", is a structure constructor")
				      else ())
           val (vars1,vars2) = (StructureAnalysis.getFirstNVars(arity,"x"),StructureAnalysis.getFirstNVars(arity,"y"))
           val (vars1_terms,vars2_terms) = (map AthTerm.makeVar vars1,map AthTerm.makeVar vars2)
           val t1 = applyTermConstructor(name,arity,vars1_terms,A.dum_pos)
           val t2 = applyTermConstructor(name,arity,vars2_terms,A.dum_pos) 
           val antecedent = Prop.makeEquality(t1,t2)
           val equalities = map Prop.makeEquality (ListPair.zip(vars1_terms,vars2_terms))
           val consequent = (case equalities of
			       [P] => P
			     | _ => Prop.makeConjunction(equalities))
       in
          propVal(Prop.makeUGen(vars1@vars2,Prop.makeBiConditional(antecedent,consequent)))
       end  
  | constructorInjAuxPrimUMethod(v as termVal(t),_,_,_) = 
      (case AthTerm.isConstant(t) of 
          SOME(cname) => if StructureAnalysis.isConstantStructureConstructor(cname) then
                            primError("Nullary constructor ("^MS.name(cname)^") given as argument "^
                                      "to "^N.constructor_inj_name^";\na constructor "^
                                      "of positive arity is required")
                         else primError(wrongArgKind(N.constructor_inj_name,1,"constructor",v))
        | _ => primError(wrongArgKind(N.constructor_inj_name,1,"constructor",v)))
  | constructorInjAuxPrimUMethod(v,_,_,_) = primError(wrongArgKind(N.constructor_inj_name,1,"constructor",v))
           
fun constructorInjMethod(x,y,z) =  constructorInjAux(x,y,z,true)

fun constructorInjPrimUMethod(x,y,z) =  constructorInjAuxPrimUMethod(x,y,z,true)

fun constructorInjFun(x,y,z) =  constructorInjAux(x,y,z,false)

fun constructorInjPrimUFun(x,y,z) =  constructorInjAuxPrimUMethod(x,y,z,false)

fun constructorExclAux([v1,v2],(env,_),{pos_ar,file},free) = 
       (case coerceValIntoTermCon(v1) of 
           SOME(regFSym(some_fsym1)) => 
              (case coerceValIntoTermCon(v2) of 
                  SOME(regFSym(some_fsym2)) => 
                     let val (name1,arity1,name2,arity2) = (D.fsymName(some_fsym1),D.fsymArity(some_fsym1),
                                                            D.fsymName(some_fsym2),D.fsymArity(some_fsym2))
                         fun msg(cname) = evError(N.constructor_excl_name^" requires two datatype constructors as "^
						   "arguments; here, "^cname^" is not a datatype constructor",
					           getPosOpt(pos_ar,0))
			 val _ = if not(free) then () else
                                 (case (StructureAnalysis.isStructureConstructorAsMS(name1),StructureAnalysis.isStructureConstructorAsMS(name2)) of
				     (SOME(sname1),SOME(sname2)) => 
					if not(StructureAnalysis.isFreeStructure(sname1)) then
				           msg(MS.name name1) else 
                                        if not(StructureAnalysis.isFreeStructure(sname2)) then
					   msg(MS.name name2) else ()
				    | _ => ())
			 val _ = if not(StructureAnalysis.areConstructorsOfSameStructure(name1,name2)) then
                                    evError("Failed application of "^N.constructor_excl_name^"---two constructors "^
                                            "of the same structure were expected,\nbut the given arguments were "^
                                            valToString(v1)^" and "^ valToString(v2),getPosOpt(pos_ar,0))
                                 else
                                    if MS.modSymEq(name1,name2) then
                                      evError("Failed application of "^N.constructor_excl_name^"---duplicate "^
                                              "occurence of "^MS.name(name2)^"\nTwo *distinct* constructors "^
                                              "(of the same structure) are required as arguments",
                                               getPosOpt(pos_ar,3))
                                    else ()
                         val (vars1,vars2) = (StructureAnalysis.getFirstNVars(arity1,"x"),StructureAnalysis.getFirstNVars(arity2,"y"))
                         val (vars1_terms,vars2_terms) = (map AthTerm.makeVar vars1,map AthTerm.makeVar vars2)
                         val (t1,t2) = (AthTerm.makeApp(name1,vars1_terms),
                                        AthTerm.makeApp(name2,vars2_terms))
                     in
                        propVal(Prop.makeUGen(vars1@vars2,Prop.makeNegation(Prop.makeEquality(t1,t2))))
                     end
                | _ => evError(wrongArgKind(N.constructor_excl_name,2,termConLCType,v2),getPosOpt(pos_ar,3)))
         | _ => evError(wrongArgKind(N.constructor_excl_name,1,termConLCType,v1),getPosOpt(pos_ar,3)))
  | constructorExclAux(args,_,{pos_ar,file},_) =  
          evError(wrongArgNumber(N.constructor_excl_name,length(args),2),getPosOpt(pos_ar,0))    

fun constructorExclAuxBPrimMethod(v1,v2,env,ab,free) = 
       (case coerceValIntoTermCon(v1) of 
           SOME(regFSym(some_fsym1)) => 
              (case coerceValIntoTermCon(v2) of 
                  SOME(regFSym(some_fsym2)) => 
                     let val (name1,arity1,name2,arity2) = (D.fsymName(some_fsym1),D.fsymArity(some_fsym1),
                                                            D.fsymName(some_fsym2),D.fsymArity(some_fsym2))
                         fun msg(cname) = primError(N.constructor_excl_name^" requires two datatype constructors as "^
						    "arguments; here, "^cname^" is not a datatype constructor")
			 val _ = if not(free) then () else
                                 (case (StructureAnalysis.isStructureConstructorAsMS(name1),StructureAnalysis.isStructureConstructorAsMS(name2)) of
				     (SOME(sname1),SOME(sname2)) => 
					if not(StructureAnalysis.isFreeStructure(sname1)) then
				           msg(MS.name name1) else 
                                        if not(StructureAnalysis.isFreeStructure(sname2)) then
					   msg(MS.name name2) else ()
				    | _ => ())
			 val _ = if not(StructureAnalysis.areConstructorsOfSameStructure(name1,name2)) then
                                    primError("Failed application of "^N.constructor_excl_name^"---two constructors "^
                                              "of the same structure were expected,\nbut the given arguments were "^
                                              valToString(v1)^" and "^ valToString(v2))
                                 else
                                    if MS.modSymEq(name1,name2) then
                                      primError("Failed application of "^N.constructor_excl_name^"---duplicate "^
                                                "occurence of "^MS.name(name2)^"\nTwo *distinct* constructors "^
                                                "(of the same structure) are required as arguments")
                                    else ()
                         val (vars1,vars2) = (StructureAnalysis.getFirstNVars(arity1,"x"),StructureAnalysis.getFirstNVars(arity2,"y"))
                         val (vars1_terms,vars2_terms) = (map AthTerm.makeVar vars1,map AthTerm.makeVar vars2)
                         val (t1,t2) = (AthTerm.makeApp(name1,vars1_terms),
                                        AthTerm.makeApp(name2,vars2_terms))
                     in
                        propVal(Prop.makeUGen(vars1@vars2,Prop.makeNegation(Prop.makeEquality(t1,t2))))
                     end
                | _ => primError(wrongArgKind(N.constructor_excl_name,2,termConLCType,v2)))
         | _ => primError(wrongArgKind(N.constructor_excl_name,1,termConLCType,v1)))

fun constructorExclMethod(x,y,z) =  constructorExclAux(x,y,z,true)
fun constructorExclPrimBMethod(v1,v2,env,ab) =  constructorExclAuxBPrimMethod(v1,v2,env,ab,true)
fun constructorExclFun(x,y,z) =  constructorExclAux(x,y,z,false)
fun constructorExclPrimBFun(v1,v2,env,ab) =  constructorExclAuxBPrimMethod(v1,v2,env,ab,false)

fun structureConstructorsFun([v],_,{pos_ar,file}) = 
      (case isStringValConstructive(v) of
           SOME(str) => 
               let val _ = print("\nHere's given str: " ^ str)
                   val str = SemanticValues.fullyQualifySortString(str)
                   val _ = print("\nAnd here's qualified str: " ^ str)
               in
                  (case StructureAnalysis.findStructure(A.makeMS(hd (String.tokens (fn c => c = #" " orelse c = #"(") str),NONE)) of 
                            SOME(struc as {constructors,...}) => 
				listVal(map (fn ac as {name,arity,...} => 
                                               termConVal(regFSym(D.struc_con(ac))))
                                            constructors)
                          | _ => listVal([]))
               end
         | _ => evError(wrongArgKind(N.structureConstructorsFun_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  | structureConstructorsFun(args,_,{pos_ar,file}) = 
          evError(wrongArgNumber(N.structureConstructorsFun_name,length(args),1),getPosOpt(pos_ar,0))

fun structureConstructorsPrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
           SOME(str) => 
             let val _ = print("\nLooking up the constructors of: " ^ str)
	         val str = SemanticValues.fullyQualifySortString(str)
		 val _ = print("\nFully qualified: " ^ str)
             in
               (case StructureAnalysis.findStructure(A.makeMS(hd (String.tokens (fn c => c = #" " orelse c = #"(") str),NONE)) of 
                            SOME(struc as {constructors,...}) => 
				listVal(map (fn ac as {name,arity,...} => 
                                               termConVal(regFSym(D.struc_con(ac))))
                                            constructors)
                          | _ => listVal([]))
            end
         | _ => primError(wrongArgKind(N.structureConstructorsFun_name,1,stringLCType,v)))

fun structureConstructorsPrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
           SOME(str) => 
             let val (sort_as_symterm,sort_as_fterm) = getFSortandSymSortFromSortString(str)
                 val str = SymTerm.toStringDefault(sort_as_symterm)
             in
               (case StructureAnalysis.findStructure(A.makeMS(hd (String.tokens (fn c => c = #" " orelse c = #"(") str),NONE)) of 
                            SOME(struc as {constructors,...}) => 
				listVal(map (fn ac as {name,arity,...} => 
                                              if arity = 0 then 
                                                  termVal(AT.makeSortedConstant(name,sort_as_fterm))
                                              else 
                                               termConVal(regFSym(D.struc_con(ac))))
                                            constructors)
                          | _ => listVal([]))
            end
         | _ => primError(wrongArgKind(N.structureConstructorsFun_name,1,stringLCType,v)))

fun isStructureWithoptionValuedSelectorsFun(v,_,_) = 
      (case isStringValConstructive(v) of
           SOME(str) => let val str = SemanticValues.fullyQualifySortString(str)
                        in
                           MLBoolToAth(StructureAnalysis.hasOptionValuedSelectors(MS.makeModSymbol'([],Symbol.symbol(str))))
                        end
         | _ => primError(wrongArgKind(N.isStructureWithoptionValuedSelectorsFun_name,1,stringLCType,v)))

fun qualifySortNamePrimUFun(v,_,_) = 
      (case isStringValConstructive(v) of
           SOME(str) => MLStringToAthString(SemanticValues.fullyQualifySortString(str))
         | _ => primError(wrongArgKind("qualify-sort-name",1,stringLCType,v)))

fun constructorExhaustMethod([v],_,{pos_ar,file}) = 
      (case isStringValConstructive(v) of
           SOME(str) => 
             let val str = SemanticValues.fullyQualifySortString(str)
             in
                (case StructureAnalysis.findStructure(A.makeMS(hd (String.tokens (fn c => c = #" " orelse c = #"(") str),NONE)) of
                            SOME(struc) => propVal(StructureAnalysis.doStrucSpan(struc))
                          | _ => evError("Failed application of "^N.constructor_exhaust_name^"---there "^
                                         "is no structure by the name of "^str,getPosOpt(pos_ar,2)))
             end
         | _ => evError(wrongArgKind(N.constructor_exhaust_name,1,stringLCType,v),getPosOpt(pos_ar,2)))
  | constructorExhaustMethod(args,_,{pos_ar,file}) = 
          evError(wrongArgNumber(N.constructor_exhaust_name,length(args),1),getPosOpt(pos_ar,0))    

fun constructorExhaustPrimUMethod(v,_,_) = 
      (case isStringValConstructive(v) of
           SOME(str) => 
             let val str = SemanticValues.fullyQualifySortString(str)
             in
                (case StructureAnalysis.findStructure(A.makeMS(hd (String.tokens (fn c => c = #" " orelse c = #"(") str),NONE)) of
                            SOME(struc) => propVal(StructureAnalysis.doStrucSpan(struc))
                          | _ => primError("Failed application of "^N.constructor_exhaust_name^"---there "^
                                           "is no structure by the name of "^str))
             end
         | _ => primError(wrongArgKind(N.constructor_exhaust_name,1,stringLCType,v)))

fun trueIntroPrimMethod([],_,_) = propVal(Prop.makeTrueProp())
  | trueIntroPrimMethod(args,_,_) = primError(wrongArgNumber(N.true_intro_PrimMethod_name,length(args),0))

fun eqReflexPrimMethod([v],(env,_),{pos_ar,file}) = 
      (case coerceValIntoTerm(v) of 
          SOME(t) => propVal(Prop.makeEquality(t,t))
        | _ => evError(wrongArgKind(N.eqReflexPrimMethod_name,1,termLCType,v),getPosOpt(pos_ar,2)))
  | eqReflexPrimMethod(args,_,{pos_ar,file}) = 
         evError(wrongArgNumber(N.eqReflexPrimMethod_name,length(args),1),getPosOpt(pos_ar,0))

fun eqReflexPrimUMethod(v,env,_) = 
      (case coerceValIntoTerm(v) of 
          SOME(t) => propVal(Prop.makeEquality(t,t))
        | _ => primError(wrongArgKind(N.eqReflexPrimMethod_name,1,termLCType,v)))

fun eqTranPrimMethod(vals as [v1,v2],(env,ab),{pos_ar,file}) = 
         let val (props as [P1,P2]) = Semantics.getProps(vals,"the arguments given to "^N.eqTranPrimMethod_name,env)
         in 
           (case (P.isEquality(P1),P.isEquality(P2)) of
              (SOME(t1,t2),SOME(t3,t4)) => if AT.termEq(t2,t3) then
                                              (checkAbMembers([(P1,Array.sub(pos_ar,2)),(P2,Array.sub(pos_ar,3))],ab,N.eqTranPrimMethod_name);
                                               propVal(P.makeEquality(t1,t4)))
                                           else evError("Incorrect application of "^N.eqTranPrimMethod_name^".\nThe right term of the first equation is not identical to"^
                                                        "\nthe left term of the second equation",getPosOpt(pos_ar,0))
            | _ => evError("Incorrect application of "^N.eqTranPrimMethod_name^"; both arguments must be identities.",getPosOpt(pos_ar,0)))
         end
  | eqTranPrimMethod(vals,(env,ab),{pos_ar,file}) = evError(wrongArgNumber(N.eqTranPrimMethod_name,length(vals),2),getPosOpt(pos_ar,0))

fun eqTranPrimBMethod(v1,v2,env,ab) = 
        (case getTwoProps(v1,v2,N.eqTranPrimMethod_name,env) of
          props as [P1,P2] =>
           (case (P.isEquality(P1),P.isEquality(P2)) of
              (SOME(t1,t2),SOME(t3,t4)) => if AT.termEq(t2,t3) then
                                              (checkAbMembersNoPos(props,ab,N.eqTranPrimMethod_name);
                                               propVal(P.makeEquality(t1,t4)))
                                           else primError("Incorrect application of "^N.eqTranPrimMethod_name^".\nThe right term of the first equation is not identical to"^
                                                          "\nthe left term of the second equation")
            | _ => primError("Incorrect application of "^N.eqTranPrimMethod_name^"; both arguments must be identities.")))

fun eqSymPrimMethod(vals as [v],(env,ab),{pos_ar,file}) = 
  (case coerceValIntoProp(v) of
      SOME(P) => (case P.isEquality(P) of 
                     SOME(t1,t2) => (checkAbMembers([(P,Array.sub(pos_ar,2))],ab,N.eqSymPrimMethod_name);
                                     propVal(P.makeEquality(t2,t1)))
                   | _ => evError("Incorrect application of "^N.eqSymPrimMethod_name^"; the given argument must be an identity",getPosOpt(pos_ar,0)))
    | _ => evError("Incorrect application of "^N.eqSymPrimMethod_name^"; the given argument must be an identity.",getPosOpt(pos_ar,0)))
  | eqSymPrimMethod(vals,(env,ab),{pos_ar,file}) = evError(wrongArgNumber(N.eqSymPrimMethod_name,length(vals),1),getPosOpt(pos_ar,0))

fun eqSymPrimUMethod(v,env,ab) = 
  (case coerceValIntoProp(v) of
      SOME(P) => (case P.isEquality(P) of 
                     SOME(t1,t2) => (checkOneAbMemberNoPos(P,ab,N.eqSymPrimMethod_name);
                                     propVal(P.makeEquality(t2,t1)))
                   | _ => primError("Incorrect application of "^N.eqSymPrimMethod_name^"; the given argument must be an identity"))
    | _ => primError("Incorrect application of "^N.eqSymPrimMethod_name^"; the given argument must be an identity."))

fun uSpecPrimMethod([v1,v2],(env,ab),{pos_ar,file}) = 
     (case coerceValIntoProp(v1) of
         SOME(P) => (case P.isUGen(P) of 
                       SOME(v,body) =>
                          (case coerceValIntoTerm(v2) of
                              SOME(t) => 
                                 let val v_sort = ATV.getSort(v)
				     val t_sort = AT.getSort(t)
				     val _ = checkAbMembers([(P,Array.sub(pos_ar,2))],ab,
							     N.uspecPrimMethod_name)
				     val msg = "Invalid use of "^N.uspecPrimMethod_name^
					       ": the sort of the term\n"^
						AT.toPrettyString(0,t,F.varToString)^
						"\nis incompatible with the sort of the "^
						"universally quantified variable in the sentence:\n"^
						P.toPrettyString(0,P,F.varToString)
                                     val res_prop = let val sort_sub = 
						             (case F.isSubSort(t_sort,v_sort) of
						                 SOME(sub) => sub
					                       | _ => evError(msg,getPosOpt(pos_ar,0)))
					            in
						      Prop.replaceVarByTermOfSomeSubSort(v,t,body,sort_sub)
					            end
                                 in
                                    propVal(res_prop)
                                 end
                            | _ => evError(wrongArgKind(N.uspecPrimMethod_name,2,termLCType,v2),getPosOpt(pos_ar,3)))
                     | _ => evError(dwrongArgKind(N.uspecPrimMethod_name,1,"a universal generalization",P),
                                    getPosOpt(pos_ar,2)))
       | _ => evError(wrongArgKind(N.uspecPrimMethod_name,1,propLCType,v1),getPosOpt(pos_ar,2)))
  | uSpecPrimMethod(args,(env,ab),{pos_ar,file}) = 
       evError(wrongArgNumber(N.uspecPrimMethod_name,length(args),2),getPosOpt(pos_ar,0))

fun uSpecPrimBMethod(v1,v2,env,ab) = 
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
                            | _ => primError(wrongArgKind(N.uspecPrimMethod_name,2,termLCType,v2)))
                     | _ => primError(dwrongArgKind(N.uspecPrimMethod_name,1,"a universal generalization",P)))
       | _ => primError(wrongArgKind(N.uspecPrimMethod_name,1,propLCType,v1)))

fun eGenPrimMethod([v1,v2],env,ab) = 
     (case coerceValIntoProp(v1) of 
         SOME(P) => 
            (case P.isEGen(P) of 
                SOME(v,body) => 
                    (case coerceValIntoTerm(v2) of
                        SOME(witness) => 
                            let val v_sort = ATV.getSort(v)
				val w_sort = AT.getSort(witness)
				val sort_sub_opt = F.isSubSort(w_sort,v_sort)
				fun f() = let val vsp = F.makeVarSortPrinter()
 				          in
						primError("Failed existential generalization---the sort of the "^
						          "witness term: \n"^(AT.toPrettyString(0,witness,vsp))^
						          "\nis not a subsort of the existentially "^
						          "quantified variable:\n"^(ATV.toPrettyString(0,v,vsp)))
					   end
				val sort_sub = (case sort_sub_opt of NONE => f() | SOME(s) => s)
				val witness_prop = Prop.replaceVarByTermOfSomeSubSort(v,witness,body,sort_sub)
                            in
                               if ABase.isMember(witness_prop,ab) then
                                  propVal(P)
                               else
                                  primError("Failed existential generalization---the "^
					  "required witness sentence\n"^
                                          pprint(0,witness_prop)^"\nis not in the assumption base")
                            end
                      | _ => primError(wrongArgKind(N.egenPrimMethod_name,2,termLCType,v2)))
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

val init_last_proof_val = MLStringToAthString("(apply-method claim true)")

fun propCountFun([],_,_) = 
                        let val count = ABase.propCount()
                         in
                            termVal(AthTerm.makeNumTerm(A.int_num(count,ref "")))
                         end
  | propCountFun(_) = primError("Incorrect invocation of prop-count")

fun insertCountFun([],_,_) = let val count = !ABase.insertions
                             in
                               termVal(AthTerm.makeNumTerm(A.int_num(count,ref "")))
                             end
  | insertCountFun(_) = primError("Incorrect invocation of insertions")

fun isPolyPrimUFun(v,_,_) =
      (case v of
         termVal(t) => MLBoolToAth(AthTerm.isPoly(t))
       | propVal(p) => MLBoolToAth(Prop.isPoly(p))
       | termConVal(f) => (case Data.getSignature(A.makeMS(funSymName(f),NONE)) of 
                                         (_,_,b,has_pred_based_sorts) => MLBoolToAth(b))      
       | _ => MLBoolToAth(false))

fun hasVarsPrimUFun(v,_,_) = 
     (case coerceValIntoTerm(v) of
        SOME(t) => MLBoolToAth(AthTerm.hasVars(t))
      | _ => MLBoolToAth(false))

fun codePrimUFun(v,_,_) = 
   (case coerceValIntoProp(v) of
       SOME(p) => (case (!(Prop.getCode(p))) of
				  SOME(i) => MLStringToAthString(Int.toString(i))
                                | _ => MLStringToAthString("NONE")))

fun abCodePrimUFun(v,_,ab) = 
   (case coerceValIntoProp(v) of
       SOME(p) =>  MLStringToAthString(Int.toString(ABase.getPropCode(p))))


fun codeFun([propVal(P)],_,_) = (case (!(Prop.getCode(P))) of
				  SOME(i) => MLStringToAthString(Int.toString(i))
                                | _ => MLStringToAthString("NONE"))
   | codeFun(_,(env,ab),{pos_ar,file}) = 
	evError("\nA sentence must be given as an argument to code2",getPosOpt(pos_ar,0))

fun hashPrimUFun(v,_,_) = 
      (case v of 
         propVal(P) => 
               let val res =  Word.toString(Prop.fastHash(P))
               in MLStringToAthString(res) end
       | termVal(t) =>
          (case coerceValIntoProp(v) of
              SOME(P) =>       let val res =  Word.toString(Prop.fastHash(P))
                               in MLStringToAthString(res)
                               end
           | _ => MLStringToAthString(Word.toString(AT.fastHash(t)))))

fun hashIntFun([propVal(P)],_,_) = 
      let val res =  Word.toInt(Prop.hash(P))
      in 
         termVal(AthTerm.makeNumTerm(A.int_num(res,ref "")))
      end
  | hashIntFun(_,(env,ab),{pos_ar,file}) = 
	evError("\nA sentence must be given as an argument to hash-int",getPosOpt(pos_ar,0))

fun hasVarsPropFun([propVal(P)],_,_) = MLBoolToAth(Prop.hasFreeVars(P) orelse Prop.hasBoundVars(P))
  | hasVarsPropFun(_) = raise Basic.Never 

fun hasBVarsPropFun([propVal(P)],_,_) = MLBoolToAth(Prop.hasBoundVars(P))
  | hasBVarsPropFun(_) = raise Basic.Never 

fun isPolyPropFun([propVal(P)],_,_) = MLBoolToAth(Prop.isPoly(P))
  | isPolyPropFun(_) = raise Basic.Never

fun holdsFun([v],(env,ab),{pos_ar,file}) = 
       (case coerceValIntoProp(v) of
           SOME(P) => MLBoolToAth(ABase.isMember(P,ab))
         | _ => evError(wrongArgKind(N.holdsFun_name,1,propLCType,v),getPosOpt(pos_ar,2)))
  | holdsFun(vals,_,{pos_ar,file}) = 
       evError(wrongArgNumber(N.holdsFun_name,length(vals),1),getPosOpt(pos_ar,0))

fun holdsPrimUFun(v,env,ab) = 
       (case coerceValIntoProp(v) of
           SOME(P) => MLBoolToAth(ABase.isMember(P,ab))
         | _ => primError(wrongArgKind(N.holdsFun_name,1,propLCType,v)))

fun sortVarsPrimUFun(v,env,ab) = 
       (case coerceValIntoProp(v) of 
           SOME(p) => let val sort_vars = P.sortVars(p)
                          val sort_var_strings = map F.varToString sort_vars
                      in
                          listVal(map MLStringToAthString sort_var_strings)
                      end
        | _ => primError(wrongArgKind(N.sortVarsFun_name,1,propLCType,v)))

fun dependenciesPrimUFun(v,env,ab) = 
       (case coerceValIntoProp(v) of 
           SOME(p) => (case PropSet.lookUpDependency(p) of
                          SOME(props) => listVal(map propVal props)
                        | _ => unitVal)
        | _ => primError(wrongArgKind(N.dependenciesFun_name,1,propLCType,v)))

fun dependenciesTranPrimUFun(v,env,ab) = 
       (case coerceValIntoProp(v) of 
           SOME(p) => listVal(map propVal (PropSet.lookUpDependencyTransitively(p)))
        | _ => primError(wrongArgKind(N.dependenciesTranFun_name,1,propLCType,v)))

fun makeMonomorphicInstancePrimUFun(v,env,ab) = 
       (case coerceValIntoTerm(v) of 
           SOME(t) => termVal(AT.makeMonomorphicInstance t)
         | _ =>  (case coerceValIntoProp(v) of 
                     SOME(p) => propVal(P.makeMonomorphicInstance p)
                   | _ => primError(wrongArgKind(N.monoInstanceFun_name,1,propLCType,v))))

fun lookupCountFun([],_,_) = let val count = !ABase.look_ups
                             in
                               termVal(AthTerm.makeNumTerm(A.int_num(count,ref "")))
                             end
  | lookupCountFun(_) = primError("Incorrect invocation of look-ups")

fun timeFun([],_,_) = termVal(AthTerm.makeNumTerm(A.real_num(Time.toReal(Time.now()),ref "")))
  | timeFun(vals,_,_) = primError(wrongArgNumber(N.timeFun_name,length(vals),0))

fun printFile(in_stream) = 
	            let fun loop() = let val line =  TextIO.inputLine(in_stream)
			             in
                                       if line = "" then ()
				       else (print(line);loop())
 				     end
			           in 
				      loop()
			           end

fun printParadoxFile(in_stream) = 
	            let fun loop() = let val line =  TextIO.inputLine(in_stream)
					 val cl = explode(line)
					 val ol =  if not(null(cl)) andalso 
						      hd(cl) = #"a" then implode(tl(cl)) else line
			             in
                                       if ol = "" then ()
				       else (print(ol);loop())
 				     end
			           in 
				      loop()
			           end
				   
fun printMSParadoxFile(in_stream,is_sort_names,sym_sig_pair_list) = 
let val dom_count = length(is_sort_names)
    val dom_ar = Array.array(dom_count,("",[]))
    val const_elems = Array.array(512,[]:string list)
    fun getSig(listVal([listVal(dom_names),res_name])) = 
			((List.map AthStringToMLString dom_names),AthStringToMLString(res_name))
      | getSig(_) = raise Basic.Never 
    fun getSS([],res) = res
      | getSS(listVal([sym_name,sym_sig])::rest,res) = 
	  getSS(rest,(AthStringToMLString(sym_name),getSig(sym_sig))::res)
      | getSS(_) = raise Basic.Never 
    val sym_sig_pair_list' = getSS(sym_sig_pair_list,[])
     fun printDomAr() = 
	let val _ = print("\nThere are "^Int.toString(dom_count)^" domains.\n")
	    val _ = Array.app (fn (str,elem_list) => (print("\n"^str^" has the following elements: ");
						     List.app (fn i => print(Int.toString(i))) elem_list)) dom_ar
			      
	in
	   print("\n")
	end
    fun initDomNames([],_) = () 
      | initDomNames(str::more,i) = (Array.update(dom_ar,i,(str,[]));
				     initDomNames(more,i+1))
    val _ = initDomNames(is_sort_names,0)
    fun domIndex(str) = 
	let fun loop(i) = if Int.>=(i,dom_count) then ~1
                          else
			  let val (name,elms) = Array.sub(dom_ar,i)
			  in
			     if name = str then i else loop(i+1)
			  end
	in
	   loop(0)
	end
    fun getElemCount() = 
	let fun loop(i,maximum) = if Int.>=(i,dom_count) then maximum
                          else
			  let val (name,elms) = Array.sub(dom_ar,i)
			  in
			     loop(i+1,Int.max(maximum,Basic.maxLst(elms)))
			  end
	in
	   loop(0,0)
	end
    fun getElemNames(elem_count,const_elems) = 
	let val name_array = Array.array(elem_count+1,(0,""))
	    fun loop(i) = let fun assign(_,name,[],_) = ()
				| assign(dom_index,name,e::rest,i) = 
				    let val elem_name = (case Array.sub(const_elems,e) of
				       			    [const_name] => const_name
							  | _ => name^"-"^(Int.toString(i)))
				    in
				            (Array.update(name_array,e,(dom_index,elem_name));
				             assign(dom_index,name,rest,i+1))
				    end
			  in 
				  if Int.>=(i,dom_count) then ()
	                          else
  				    let val (name,elms) = Array.sub(dom_ar,i)
					val cl = List.map (Char.toLower) (tl(tl(explode(name))))
					val new_name = implode cl
				    in
				       (assign(i,new_name,elms,1);loop(i+1))
				    end
			   end
	in
	   (loop(0);name_array)
	end
     fun f(str) = String.tokens (fn c => (c = #"(") orelse (c = #")") orelse (c = #",") orelse (c = #" ")
			orelse (c = #"'") orelse (c = #"\n") orelse (c = #"=") orelse (c = #":")) str
     datatype Result = boolRes of bool | intRes of int
     fun stringTail(s) = String.substring(s,1,String.size(s)-1)
     fun isWhiteSpaceLine(str) = List.all (Char.isSpace) (explode str)
     fun breakLine(line) = let val lst = f line
			       fun getInt(str) = Option.getOpt(Int.fromString(str),0)
			       val args = List.map getInt (tl(List.take(lst,List.length(lst)-1)))
			       val res = (case hd(rev(lst)) of
					   "TRUE" => boolRes(true)
					 | "FALSE" => boolRes(false)
				         | s => intRes(getInt(s)))
			   in
			      {sym_name=stringTail(hd(lst)),arguments=args,result=res}
			   end
    fun getLines(is,res) = let val line = TextIO.inputLine(is)
			   in
			      if line = "" then rev(res)
			      else (if isWhiteSpaceLine(line) then getLines(is,res)
			            else (case breakLine(line) of
					     line_res as {sym_name=sname,arguments=[],result=intRes(i)} =>
					       let val names = Array.sub(const_elems,i)
					       in
					          (Array.update(const_elems,i,sname::names);
						   getLines(is,line_res::res))
					       end
					   | line_res => getLines(is,line_res::res)))
			   end
    val all_lines = getLines(in_stream,[])
    fun showLine({sym_name,arguments,result}) = 
	(print("\nName: "^sym_name^"\nArguments: ");
	 Basic.printList(arguments,Int.toString);
	 print("\nResult: "^(case result of boolRes(true) => "TRUE" 
					  | boolRes(false) => "FALSE"
					  | intRes(n) => Int.toString(n))))
    fun buildDomArray() = 
	let fun processLine(line as {sym_name:string,arguments: int list,result: Result}) = 
		  let val index = domIndex(sym_name)
		  in
		    if index < 0 then ()
		    else 
 			(case (hd(arguments),result) of 
			    (k,boolRes(true)) => let val (str,nums) = Array.sub(dom_ar,index)
						 in
						   Array.update(dom_ar,index,(str,k::nums))
						 end
			   | _ => ())
		  end
	in
	  List.app processLine all_lines
	end
     val _ = buildDomArray()
     val elem_count = getElemCount()
     val sym_count = length sym_sig_pair_list
     fun pairLeft(a,b) = a
     fun pairRight(a,b) = b
     fun doSig(sym_name,ssig) = {name=sym_name,arg_doms=(List.map (fn s => domIndex("is"^s)) (pairLeft ssig)),
				res_dom=(case (pairRight  ssig) of "Boolean" => NONE 
				| str => SOME(domIndex("is"^str)))}
     val sigs = map doSig sym_sig_pair_list'
     fun printSig({name,arg_doms,res_dom=NONE}) = 
	(print("\nRelation "^name^", domains: "^(Basic.printListStrCommas(arg_doms,Int.toString))))
       | printSig({name,arg_doms,res_dom=SOME(i)}) = 
	(print("\nFunction "^name^",domains: "^(Basic.printListStrCommas(arg_doms,Int.toString)));
	 print("and result domain: "^Int.toString(i)))
     fun printGivenSig(sym_name,ssig) = (print("\nSymbol name: "^sym_name^", domains: "^
					 Basic.printListStrCommas(pairLeft(ssig),fn x => x)^", and result domain: "^	
					 pairRight(ssig)))
     val name_map = getElemNames(elem_count,const_elems)
     fun domName(dom_name) = implode(tl(tl(explode(dom_name))))
     fun elName(el_index) = pairRight(Array.sub(name_map,el_index))
     fun getEquations() = let fun f(elem_index) = (case Array.sub(const_elems,elem_index) of
						     names as _::_::_ => List.map 
						       (fn s => s^" = "^(elName elem_index)) names
						   | _ => [])
			      fun loop(i,res) = if i > 511 then res
						else loop(i+1,f(i)@res)
			   in
			     loop(1,[])
			   end
     fun writeLines([]) = ()
       | writeLines(l::rest) = (print("\n");print(l);writeLines(rest))
     fun printDomElems(dom_name,elems) =
	    (print("\n"^domName(dom_name)^" has "^Int.toString(length(elems))^(if length(elems) = 1 then
	    " element: " else " elements: ")^
             Basic.printListStrCommas(List.map (fn el_index => elName(el_index)) elems,Basic.id)^
	     ".");
	     let val eqns = getEquations()
	     in if null(eqns) then () else (print("\n\nWe also have the following identities:\n");
					    writeLines(eqns))
	     end)
     fun showDomainElements() = Array.app printDomElems dom_ar
     fun printElemNames() = 
	List.app (fn i => let val (dom_index,name) = Array.sub(name_map,i)
			      val (dom_name,_) = Array.sub(dom_ar,dom_index)			
			  in
			    print("\nElement "^Int.toString(i)^" is a member of domain "^Int.toString(dom_index)^
				  ", i.e., domain "^dom_name^". It is named "^name^".\n")
			  end)
 		 (Basic.firstNumbersFast(1,elem_count))
     fun getResName(boolRes(b)) = Basic.bool2Str(b)
       | getResName(intRes(i)) = pairRight(Array.sub(name_map,i))
     fun wellSorted([],[]) = true
       | wellSorted(x::rest1,d::rest2) = Basic.isMember(x,pairRight(Array.sub(dom_ar,d))) andalso wellSorted(rest1,rest2)
       | wellSorted(_) = false
     fun findSym(_,[]) = NONE
       | findSym(sname,(sym_sig as {name,arg_doms,res_dom})::rest) = 
	   if sname = name then SOME(sym_sig) else findSym(sname,rest)
     fun printLines([],_) = ()
       | printLines((line as {sym_name:string,arguments: int list,result: Result})::rest,last_sym) = 
	   (case findSym(sym_name,sigs) of
	      SOME({arg_doms=[],...}) => printLines(rest,last_sym)
	    | SOME({arg_doms=adl, ...}) =>
               (if wellSorted(arguments,adl) then
		    let val arg_names = map (fn i => pairRight(Array.sub(name_map,i))) arguments
			val res_name = getResName(result)
		        val spaces = (case last_sym of
					SOME(sym_name') => if sym_name = sym_name' then "\n" else "\n\n"
				      | _ => "\n\n")
	            in
		      (print(spaces^sym_name^"("^Basic.printListStrCommas(arg_names,Basic.id)^") = "^res_name);		
		       printLines(rest,SOME(sym_name)))
		    end
		else printLines(rest,last_sym))
             | _ => (printLines(rest,last_sym)))
in 
 (showDomainElements();
  print("\n\nPress enter to see the function/relation definitions: ");
  Basic.promptAndReadLine("");
  printLines(rev(all_lines),NONE);
  print("\n"))
end

fun findLine(in_stream,l) = let fun loop() = 
           	  		     let val line =  TextIO.inputLine(in_stream)
			             in
                                       if line = "" then false
				       else
				         if line = l then true else loop()
 				     end
			           in 
				      loop()
			           end
				   
fun findUsedPremises(in_stream) =  
     let fun loop(res) = let val line = TextIO.inputLine(in_stream) 
                             val is_prefix = String.isPrefix "fof(" line
                             val tokens = if is_prefix then String.tokens (fn c => Basic.isMember(c,[#",",#"(",#")",#"\n"])) line else []
                             fun getNumber(str) = let val digit_str = List.hd(String.tokens (fn c => not(Basic.isDigit(c))) str)
                                                  in  
                                                     (case Int.fromString digit_str of
                                                         SOME(i) => i
                                                       | _ => ~1)
                                                  end
                             val number = if not(List.null(tokens)) andalso List.hd(List.tl(List.tl(tokens))) = "axiom" 
                                             then getNumber(List.hd(List.tl(tokens))) else ~1 
                         in
                            if line = "" then (rev res) else 
                               (if is_prefix andalso number >= 0 then loop(number::res) else loop(res))
                         end
      in  loop([]) end
        
val spass_counter = ref(IntInf.fromInt(0))
val vamp_counter = ref(IntInf.fromInt(0))
val e_counter = ref(IntInf.fromInt(0))
val paradox_counter = ref(IntInf.fromInt(0))
val flotter_counter = ref(IntInf.fromInt(0))
val gandalf_counter = ref(IntInf.fromInt(0))
val usm_counter = ref(IntInf.fromInt(0))
val infIntUnit = IntInf.fromInt(1)

fun getSpassIndex() = let val cv = !spass_counter
		            val _ = spass_counter := IntInf.+(cv,infIntUnit)
			in
			   IntInf.toString(cv)
			end

fun getVampIndex() = let val cv = !vamp_counter
		            val _ = vamp_counter := IntInf.+(cv,infIntUnit)
			in
			   IntInf.toString(cv)
			end

fun getEIndex() = let val cv = !e_counter
		      val _ = e_counter := IntInf.+(cv,infIntUnit)
                  in
                    IntInf.toString(cv)
                  end

fun getGandalfIndex() = let val cv = !gandalf_counter
		            val _ = gandalf_counter := IntInf.+(cv,infIntUnit)
			in
			   IntInf.toString(cv)
			end

fun getParadoxIndex() = let val cv = !paradox_counter
		            val _ = paradox_counter := IntInf.+(cv,infIntUnit)
			in
			   IntInf.toString(cv)
			end

fun getUSMIndex() = let val cv = !usm_counter
		            val _ = usm_counter := IntInf.+(cv,infIntUnit)
			in
			   IntInf.toString(cv)
			end

fun getFlotterIndex() = let val cv = !flotter_counter
		            val _ = flotter_counter := IntInf.+(cv,infIntUnit)
			in
			   IntInf.toString(cv)
			end

val spass_proof_line = "SPASS beiseite: Proof found.\n"
val vamp_proof_line = "Satisfiable!\n"
val e_proof_line = "# Proof found!\n"
val paradox_proof_line = "== Model ==================================================================="

fun spassProve(fun_sym_str,pred_sym_str,hyp_str_lst,concl_str,max_seconds) = 
  let val si = getSpassIndex()
      val (in_file_name,out_file_name,error_file_name) = (Paths.spass_input_file si, Paths.spass_output_file si,Paths.spass_error_file si)
      val stream =  TextIO.openOut(in_file_name)
      fun writeStream(str) = TextIO.output(stream,str)
      fun findProof(stream) = let fun loop(l1,l2,l3) = 
           			   let val line =  TextIO.inputLine(stream)
			           in
                                     if line = "" then (l1 = spass_proof_line)
				     else
				       loop(l2,l3,line)
 				   end
			      in 
				loop("","","")
			      end
      val _ = writeStream "begin_problem(athena).\n\n"
      fun writeSyms([]) = ()
        | writeSyms(str::more) = (writeStream(str);writeStream(".\n");writeSyms(more))
      fun writeHyps([]) = ()
        | writeHyps(str::more) = if str = "" then writeHyps(more)
                                 else (writeStream("formula(");writeStream(str);writeStream(").\n");writeHyps(more))
      val _ = (writeStream("list_of_descriptions.\n");writeStream("name({*Hilbert's eleventh problem*}).\n");
               writeStream("author({*David Hilbert*}).\n");
	       writeStream("status(unsatisfiable).\n");
	       writeStream("description({*LL*}).\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_symbols.\n");
              (if fun_sym_str = "" then () else (writeStream("  functions[");
               writeStream(fun_sym_str);writeStream("].\n")));
              (if pred_sym_str = "" then () else (writeStream("  predicates[");
               writeStream(pred_sym_str);writeStream("].\n")));
	       writeStream("end_of_list.\n\n"))
      val _ = writeStream("list_of_formulae(axioms).\n\n")
      val _ = (writeHyps(hyp_str_lst);writeStream("\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_formulae(conjectures).\n\n");writeStream("formula(");
	       writeStream(concl_str);writeStream(").\n\n");writeStream("end_of_list.\n\n"))
      val _ = writeStream("end_problem.")
      val _ = TextIO.closeOut(stream)
      val cmd = Names.spass_binary ^ " -PStatistic=0 -TimeLimit="^max_seconds^" "^in_file_name^" > "^out_file_name^" 2> "^error_file_name
      val _ = OS.Process.system(cmd)
      val in_stream = TextIO.openIn(out_file_name)
      val answer_bit = findProof(in_stream)
      val sp_output_string = TextIO.inputAll(in_stream)
      val _ = TextIO.closeIn(in_stream)
      val _ = TextIO.closeOut(stream)
      val _ = (deleteFile(in_file_name);deleteFile(out_file_name))
  in
    (sp_output_string,answer_bit)
  end

fun unLimSpassProve(fun_sym_str,pred_sym_str,hyp_str_lst,concl_str) = 
  let val si = getSpassIndex()
      val (in_file_name,out_file_name,error_file_name) = (Paths.spass_input_file si, Paths.spass_output_file si,Paths.spass_error_file si)
      val stream =  TextIO.openOut(in_file_name)
      fun writeStream(str) = TextIO.output(stream,str)
      fun findProof(stream) = let fun loop(l1,l2,l3) = 
           			   let val line =  TextIO.inputLine(stream)
			           in
                                     if line = "" then (l1 = spass_proof_line)
				     else
				       loop(l2,l3,line)
 				   end
			      in 
				loop("","","")
			      end
      val _ = writeStream "begin_problem(athena).\n\n"
      fun writeSyms([]) = ()
        | writeSyms(str::more) = (writeStream(str);writeStream(".\n");writeSyms(more))
      fun writeHyps([]) = ()
        | writeHyps(str::more) = (writeStream("formula(");writeStream(str);writeStream(").\n");
				  writeHyps(more))
      val _ = (writeStream("list_of_descriptions.\n");writeStream("name({*Hilbert's eleventh problem*}).\n");
               writeStream("author({*David Hilbert*}).\n");
	       writeStream("status(unsatisfiable).\n");
	       writeStream("description({*LL*}).\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_symbols.\n");
              (if fun_sym_str = "" then () else (writeStream("  functions[");
               writeStream(fun_sym_str);writeStream("].\n")));
              (if pred_sym_str = "" then () else (writeStream("  predicates[");
               writeStream(pred_sym_str);writeStream("].\n")));
	       writeStream("end_of_list.\n\n"))
      val _ = writeStream("list_of_formulae(axioms).\n\n")
      val _ = (writeHyps(hyp_str_lst);writeStream("\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_formulae(conjectures).\n\n");writeStream("formula(");
	       writeStream(concl_str);writeStream(").\n\n");writeStream("end_of_list.\n\n"))
      val _ = writeStream("end_problem.")
      val _ = TextIO.closeOut(stream)
      val cmd = Names.spass_binary ^ " -PStatistic=0  "^in_file_name^" > "^out_file_name^" 2> "^error_file_name
      val _ = OS.Process.system(cmd)
      val in_stream = TextIO.openIn(out_file_name)
      val answer_bit = findProof(in_stream)
      val sp_output_string = TextIO.inputAll(in_stream)
      val _ = TextIO.closeIn(in_stream)
      val _ = TextIO.closeOut(stream)
      val _ = (deleteFile(in_file_name);deleteFile(out_file_name))
  in
    (sp_output_string,answer_bit)
  end

fun TTPP_CNF_Strings(flotter_stream:TextIO.instream,conjectures_present) = 
  let val isPrintable = Char.isPrint
      val cl = Basic.findAndSkipLine(flotter_stream,"list_of_clauses(axioms, cnf).\n")
      fun inc(n) = n := !n + 1
      fun findOr(#"]"::(#","::(#"o"::(#"r"::(#"("::rest)))))= (rest,true)
        | findOr(#"o"::(#"r"::(#"("::rest))) = (rest,false)
	| findOr(_::more) = findOr(more)
	| findOr([]) = ([],false)
      fun findChar([],_) = NONE
	| findChar(c::rest,c') = if c = c' then SOME(rest) else findChar(rest,c')
      fun extractUntil([],_,_,res) = (res,[])
        | extractUntil(c::rest,f,pred,res) = (f(c);if pred() then (res,rest) else 
	extractUntil(rest,f,pred,c::res))
      fun skipUntil([],_) = []
        | skipUntil(cl as c::rest,pred) = if pred(c) then cl else skipUntil(rest,pred)
      fun update(c,lp,rp) = (case c of
	  		       #"(" => inc(lp)
     		             | #")" => inc(rp)
  		             | _ => ())
      fun getTerm(cl,cur_ch,lp,rp,final,inside_forall) = 
           let val (chars,rest') = extractUntil(cl,fn c => (cur_ch := c;update(c,lp,rp)),
						fn () => !cur_ch = #"," andalso Int.>=(!rp,!lp),[])
	   in
	      if Int.>(!rp,!lp) then (if inside_forall then (final := true;(tl(tl(chars)),rest'))
				      else (final := true;(tl(chars),rest')))
	      else (chars,rest')
	   end
      fun getLit(#"n"::(#"o"::(#"t"::(#"("::rest))),final,inside_forall) = 
	   let val  (cur_ch,lp,rp) = (ref(#"o"),ref 1, ref 0)
	       val (chars,rest') = getTerm(rest,cur_ch,lp,rp,final,inside_forall)
	       val rev_chars = rev(tl(chars))
	       val chars' = (case rev_chars  of
		                #"S"::(#"k"::rest) => #"s"::(#"k"::rest)
		              | _ => rev_chars)
           in 
	      (#"-"::(#"-"::chars'),rest')
	   end
        | getLit(cl,final,inside_forall) = let val (chars,rest) = 
						  getTerm(cl,ref(#"o"),ref(0),ref(0),final,inside_forall)
	 				       val rev_chars = rev chars
					       val chars' = (case rev_chars of
						               #"S"::(#"k"::rest) => #"s"::(#"k"::rest)
					                    | _ => rev_chars)
			     in (#"+"::(#"+"::chars'),rest)
			     end
      fun getClause(cl,inside_forall) = let val final = ref false
			      fun loop(cl,res) = let val (lit,rest) = getLit(cl,final,inside_forall)
						 in
						    if !final then (rev(lit::res),rest)
						    else loop(rest,lit::res)
					         end
			  in
			     loop(cl,[])
			  end
	fun printListStrCommas(lst,f) = 
      		let fun p([]) = ""
           	    | p([x]) = f(x)
	            | p(x::y::more) = f(x)^", "^p(y::more)
	      in
	         p(lst)
	      end
      fun getClauses(cl,label) = 
        let val i = ref 1
            val prefix = if label = "axiom" then "a" else (if label = "conjecture" then "c" else "h") 
            fun loop(cl,clauses) = let val (cl',in_forall) = findOr(cl)
				       val (lits,rest) = getClause(cl',in_forall)
  				       val string_lits = List.map implode lits
				        val new_clause = "\ninput_clause("^prefix^(Int.toString(!i))^","^label^",["^
					   	        (printListStrCommas(string_lits,fn x => x))^"]).\n"
				       val _ = i := !i + 1
				       val rest' = skipUntil(rest,Char.isAlpha)
		               in
				 (case rest' of
                                    #"c"::_ => loop(rest',new_clause::clauses)
				  | _ => (rev(new_clause::clauses),rest'))
			       end
	in
          loop(cl,[])
        end
     fun getClauses'(cl,label) = let val cl' = skipUntil(cl,isPrintable)
                                 in  
                                    (case cl' of
                                      (#"e"::(#"n"::(#"d"::(#"_"::(#"o"::(#"f"::(#"_"::(#"l"::(#"i"::(#"s"::(#"t"::_))))))))))) => ([],cl')
                                    | _ => getClauses(cl',label))
                                 end
in
    (case skipUntil(cl,Char.isAlpha) of
	   #"c"::_ => let val (vamp_ax,rest) = getClauses(cl,"axiom");
             	  	  val (vamp_conj,_) = if conjectures_present then getClauses(rest,"conjecture")
					      else ([],[])
		      in
			(vamp_ax,vamp_conj)
		      end
	 | cl' => let val (vamp_conj,_) = if conjectures_present then getClauses(cl',"conjecture")
					  else ([],[])
		  in 
		     ([],vamp_conj)
		  end)
end

fun gandalfStrings(flotter_stream:TextIO.instream) = 
  let val isPrintable = Char.isPrint
      val cl = Basic.findAndSkipLine(flotter_stream,"list_of_clauses(axioms, cnf).\n")
      fun inc(n) = n := !n + 1
      fun findOr(#"]"::(#","::(#"o"::(#"r"::(#"("::rest)))))= (rest,true)
        | findOr(#"o"::(#"r"::(#"("::rest))) = (rest,false)
	| findOr(_::more) = findOr(more)
	| findOr([]) = ([],false)
      fun findChar([],_) = NONE
	| findChar(c::rest,c') = if c = c' then SOME(rest) else findChar(rest,c')
      fun extractUntil([],_,_,res) = (res,[])
        | extractUntil(c::rest,f,pred,res) = (f(c);if pred() then (res,rest) else 
	extractUntil(rest,f,pred,c::res))
      fun skipUntil([],_) = []
        | skipUntil(cl as c::rest,pred) = if pred(c) then cl else skipUntil(rest,pred)
      fun update(c,lp,rp) = (case c of
	  		       #"(" => inc(lp)
     		             | #")" => inc(rp)
  		             | _ => ())
      fun getTerm(cl,cur_ch,lp,rp,final,inside_forall) = 
           let val (chars,rest') = extractUntil(cl,fn c => (cur_ch := c;update(c,lp,rp)),
						fn () => !cur_ch = #"," andalso Int.>=(!rp,!lp),[])
	   in
	      if Int.>(!rp,!lp) then (if inside_forall then (final := true;(tl(tl(chars)),rest'))
				      else (final := true;(tl(chars),rest')))
	      else (chars,rest')
	   end
      fun getLit(#"n"::(#"o"::(#"t"::(#"("::rest))),final,inside_forall) = 
	   let val  (cur_ch,lp,rp) = (ref(#"o"),ref 1, ref 0)
	       val (chars,rest') = getTerm(rest,cur_ch,lp,rp,final,inside_forall)
	       val rev_chars = rev(tl(chars))
	       val chars' = (case rev_chars  of
		                #"S"::(#"k"::rest) => #"s"::(#"k"::rest)
		              | _ => rev_chars)
           in 
	      (#"-"::(#"-"::chars'),rest')
	   end
        | getLit(cl,final,inside_forall) = let val (chars,rest) = 
						  getTerm(cl,ref(#"o"),ref(0),ref(0),final,inside_forall)
	 				       val rev_chars = rev chars
					       val chars' = (case rev_chars of
						               #"S"::(#"k"::rest) => #"s"::(#"k"::rest)
					                    | _ => rev_chars)
			     in (#"+"::(#"+"::chars'),rest)
			     end
      fun getClause(cl,inside_forall) = let val final = ref false
			      fun loop(cl,res) = let val (lit,rest) = getLit(cl,final,inside_forall)
						 in
						    if !final then (rev(lit::res),rest)
						    else loop(rest,lit::res)
					         end
			  in
			     loop(cl,[])
			  end
	fun printListStrCommas(lst,f) = 
      		let fun p([]) = ""
           	    | p([x]) = f(x)
	            | p(x::y::more) = f(x)^", "^p(y::more)
	      in
	         p(lst)
	      end
      fun getClauses(cl,label) = 
        let val i = ref 1
            val prefix = if label = "axiom" then "a" else (if label = "conjecture" then "c" else "h") 
            fun loop(cl,clauses) = let val (cl',in_forall) = findOr(cl)
				       val (lits,rest) = getClause(cl',in_forall)
  				       val string_lits = List.map implode lits
				        val new_clause = "\ninput_clause("^prefix^(Int.toString(!i))^","^label^",["^
					   	        (printListStrCommas(string_lits,fn x => x))^"]).\n"
				       val _ = i := !i + 1
				       val rest' = skipUntil(rest,Char.isAlpha)
		               in
				 (case rest' of
                                    #"c"::_ => loop(rest',new_clause::clauses)
				  | _ => (rev(new_clause::clauses),rest'))
			       end
	in
          loop(cl,[])
        end
in
    (case skipUntil(cl,Char.isAlpha) of
	   #"c"::_ => let val (vamp_ax,rest) = getClauses(cl,"axiom");
             	  	  val (vamp_conj,_) = getClauses(rest,"conjecture")
		      in
			(vamp_ax,vamp_conj)
		      end
	 | cl' => let val (vamp_conj,_) = getClauses(cl',"conjecture")
		  in 
		     ([],vamp_conj)
		  end)
end

fun Flotter_CNF_To_TTPP_CNF(fun_sym_str,pred_sym_str,hyp_str_lst,concl_str_opt) = 
  let val fl_ind = getFlotterIndex()
      val (fof_file_name,cnf_file_name,error_file_name) = (Paths.fof_file fl_ind,Paths.cnf_file fl_ind,Paths.cnf_error_file fl_ind)
      val flotter_fof_stream =  TextIO.openOut(fof_file_name)
      fun writeStream(str) = TextIO.output(flotter_fof_stream,str)
      val _ = writeStream "begin_problem(athena).\n\n"
      fun writeSyms([]) = ()
        | writeSyms(str::more) = (writeStream(str);writeStream(".\n");writeSyms(more))
      fun writeHyps([]) = ()
        | writeHyps(str::more) = (writeStream("formula(");writeStream(str);writeStream(").\n");
				  writeHyps(more))
      val _ = (writeStream("list_of_descriptions.\n");writeStream("name({*Hilbert's eleventh problem*}).\n");
               writeStream("author({*David Hilbert*}).\n");
	       writeStream("status(unsatisfiable).\n");
	       writeStream("description({*LL*}).\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_symbols.\n");
              (if fun_sym_str = "" then () else (writeStream("  functions[");
               writeStream(fun_sym_str);writeStream("].\n")));
              (if pred_sym_str = "" then () else (writeStream("  predicates[");
               writeStream(pred_sym_str);writeStream("].\n")));
	       writeStream("end_of_list.\n\n"))
      val _ = writeStream("list_of_formulae(axioms).\n\n")
      val _ = (writeHyps(hyp_str_lst);writeStream("\n");writeStream("end_of_list.\n\n"))
      val _ = (case concl_str_opt of
                 SOME(concl_str) => (writeStream("list_of_formulae(conjectures).\n\n");writeStream("formula(");
 	       			     writeStream(concl_str);writeStream(").\n\n");writeStream("end_of_list.\n\n"))
	      | _ => ())
      val _ = writeStream("end_problem.")
      val _ = TextIO.closeOut(flotter_fof_stream) 
      val _ = OS.Process.system("oldspass -Flotter "^fof_file_name^" > "^cnf_file_name^" 2> "^error_file_name)
      val flotter_cnf_stream = TextIO.openIn(cnf_file_name)
      val conj_present = (case concl_str_opt of 
			    SOME(_) => true
			  | _ => false)
      val res = TTPP_CNF_Strings(flotter_cnf_stream,conj_present)
      val _ = TextIO.closeIn(flotter_cnf_stream)
      val _ = TextIO.closeOut(flotter_fof_stream)
      val _ = (deleteFile(fof_file_name);deleteFile(cnf_file_name))
  in
    res
  end

fun FlotterToGandalf(fun_sym_str,pred_sym_str,hyp_str_lst,concl_str) = 
  let val fl_ind = getFlotterIndex()
      val (fof_file_name,cnf_file_name) = (Paths.fof_file fl_ind,Paths.cnf_file fl_ind)
      val flotter_fof_stream =  TextIO.openOut(fof_file_name)
      fun writeStream(str) = TextIO.output(flotter_fof_stream,str)
      val _ = writeStream "begin_problem(athena).\n\n"
      fun writeSyms([]) = ()
        | writeSyms(str::more) = (writeStream(str);writeStream(".\n");writeSyms(more))
      fun writeHyps([]) = ()
        | writeHyps(str::more) = (writeStream("formula(");writeStream(str);writeStream(").\n");
				  writeHyps(more))
      val _ = (writeStream("list_of_descriptions.\n");writeStream("name({*Hilbert's eleventh problem*}).\n");
               writeStream("author({*David Hilbert*}).\n");
	       writeStream("status(unsatisfiable).\n");
	       writeStream("description({*LL*}).\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_symbols.\n");
              (if fun_sym_str = "" then () else (writeStream("  functions[");
               writeStream(fun_sym_str);writeStream("].\n")));
              (if pred_sym_str = "" then () else (writeStream("  predicates[");
               writeStream(pred_sym_str);writeStream("].\n")));
	       writeStream("end_of_list.\n\n"))
      val _ = writeStream("list_of_formulae(axioms).\n\n")
      val _ = (writeHyps(hyp_str_lst);writeStream("\n");writeStream("end_of_list.\n\n"))
      val _ = (writeStream("list_of_formulae(conjectures).\n\n");writeStream("formula(");
	       writeStream(concl_str);writeStream(").\n\n");writeStream("end_of_list.\n\n");
               writeStream("end_problem."))
      val _ = TextIO.closeOut(flotter_fof_stream)
      val cmd = Names.spass_binary ^ " -Flotter "^fof_file_name^" > "^cnf_file_name
      val _ = OS.Process.system(cmd)
      val flotter_cnf_stream = TextIO.openIn(cnf_file_name)
      val res = gandalfStrings(flotter_cnf_stream)
      val _ = TextIO.closeIn(flotter_cnf_stream)
      val _ = TextIO.closeOut(flotter_fof_stream)
      val _ = (deleteFile(fof_file_name);deleteFile(cnf_file_name))
  in
    res
  end

fun makeSpassPropStringFun([listVal(vals)],env,_) = 
   let val  hyp_props = getProps(vals,"the list argument of "^N.spfPrimMethod_name,env)
       val (fs,ps,prop_strings) = Prop.makeSpassPropList(hyp_props,Basic.fsymRenamer)
   in 
      listVal(map MLStringToAthString (fs::ps::prop_strings))
   end
  | makeSpassPropStringFun(_) = raise Basic.Never

fun makePolySpassPropStringFun([v],env,_) = 
   let val  [p] = getProps([v],"the list argument of "^"make-poly-spass-prop-string-fun",env)

       val id = fn x => x
       val variableRenamer = Basic.varRenamer;
       val fsymRenamer = Basic.fsymRenamer;
       val (p_str,fsyms,fsymbols,psyms,sort_vars,osorts) = Prop.makePolySpassProp(p,variableRenamer,fsymRenamer)
       val sort_vars_string = Basic.printListStrCommas(sort_vars,id)
       val fsym_string = Basic.printListStrCommas(fsyms,id)
       val fsymbols_string = Basic.printListStrCommas(fsymbols,MS.name)
       val psym_string = Basic.printListStrCommas(psyms,id)
       val osorts_string = Basic.printListStrCommas(osorts,MS.name)
   in 
      listVal([MLStringToAthString p_str,MLStringToAthString fsym_string,MLStringToAthString fsymbols_string,
               MLStringToAthString psym_string,
               MLStringToAthString sort_vars_string,MLStringToAthString osorts_string])
   end
  | makePolySpassPropStringFun(_) = raise Basic.Never

fun makePolySpassTermStringFun([v],env,_) = 
   let val [term] = getTermsNoPos([v],"the argument of "^"make-poly-spass-term")
       val printer = F.makePolyVarSortPrinter()     
       val variableRenamer = Basic.varRenamer;
       val fsymRenamer = Basic.fsymRenamer;
       val (term_str,{vars,fsyms,fsymbols,osorts}) = AT.makePolySpassTerm(term,[],variableRenamer,fsymRenamer,printer)
       val id = fn x => x
       val vars_string = Basic.printListStrCommas(vars,id)
       val fsym_string = Basic.printListStrCommas(fsyms,id)
   in 
      listVal([MLStringToAthString term_str, MLStringToAthString vars_string,  MLStringToAthString fsym_string])
   end
  | makePolySpassTermStringFun(_) = raise Basic.Never

fun makeEPropStringFun([v],env,_) = 
   let val  hyp_props = getProps([v],"the list argument of "^N.spfPrimMethod_name,env)
       val str = Prop.makeTSTPProp (hd hyp_props)
   in 
      MLStringToAthString str 
   end
  | makeEPropStringFun(_) = raise Basic.Never

fun hasEquality(P) = 
 (case P.isAtom(P) of
    SOME(t) => AT.fsymOccursIn(N.mequal_logical_symbol,t)
  | _ => (case P.isCompound(P) of
             SOME(_,props) => List.exists hasEquality props
           | _ => raise Basic.Never))

fun unparsePrimUFun(v,env,_) = 
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
    | closMethodVal(e,_) => 
              MLStringToAthString("Method: " ^ (A.unparseExp(e)))
    | _ =>  primError(wrongArgKind(N.unparseFun_name,1,functionLCType,v)))

fun make_CNF_Result(clauses,output_format,inverse_atom_table) = 
 let fun makeAtom(i) = (case (HashTable.find inverse_atom_table i) of
      	                   SOME(A) => A
                         | _=> P.makeAtom(AT.makeVar(ATV.athTermVarWithSort("X"^(Int.toString(i)),F.boolean_sort))))
     fun makeLiteral(i) = if i < 0 then P.makeNegation(makeAtom(~i))
                          else makeAtom(i)
     fun makeClauseSentence(c) = (case (map makeLiteral c) of
                                     [p] => p
                                   | L => P.makeDisjunction(L))
  in
     if (output_format = "dimacs-list") then
         listVal(map (fn c => listVal(map makeAthenaInt c)) clauses)
     else if (output_format = "sentence-list") 
          then listVal(map (fn c => propVal(makeClauseSentence(c))) clauses)
          else propVal(P.makeConjunction(map makeClauseSentence clauses)) 
  end

fun make_CNF_Map(r:Prop.cnf_conversion_result
		  as {clauses,
		      table: (int,P.prop) HashTable.hash_table,
                      total_var_num: int,
	              tseitin_var_num: int,
		      clause_num: int,
	              cnf_conversion_time: real,
		      array_n: int},
		 output_format) = 

  let val init_map = Maps.makeMap(SV.compare)
      val t3 = Time.toReal(Time.now())
      val result:SV.value = make_CNF_Result(clauses,output_format,table)
      val t4 = Time.toReal(Time.now())
      val clause_formatting_time = Real.-(t4,t3)
      val t5 = Time.toReal(Time.now())
      val ints_and_props = HashTable.listItemsi table
      val ht = HashTable.mkTable(SemanticValues.hashVal, valEq) (!(Options.default_table_size),Data.GenEx("Failed table creation"))
      val _ = List.app (fn (i,p) => HashTable.insert ht (makeAthenaInt(i),propVal(p)))
                       ints_and_props
      val t6 = Time.toReal(Time.now())
      val table_formatting_time = Real.-(t6,t5)
      val (key1,val1) = (termVal(AT.makeIdeConstant("result")),result)
      val (key2,val2) = (termVal(AT.makeIdeConstant("atom-table")),tableVal(ht))
      val (key3,val3) = (termVal(AT.makeIdeConstant("cnf-conversion-time")),makeAthenaReal(cnf_conversion_time))
      val (key4,val4) = (termVal(AT.makeIdeConstant("total-var-num")),makeAthenaInt(total_var_num))
      val (key5,val5) = (termVal(AT.makeIdeConstant("tseitin-var-num")),makeAthenaInt(tseitin_var_num))
      val (key6,val6) = (termVal(AT.makeIdeConstant("clause-num")),makeAthenaInt(clause_num))
      val (key7,val7) = (termVal(AT.makeIdeConstant("table-formatting-time")),makeAthenaReal(table_formatting_time))
      val (key8,val8) = (termVal(AT.makeIdeConstant("clause-formatting-time")),makeAthenaReal(clause_formatting_time))
      val key_val_pairs = [(key1,result),(key2,val2),(key3,val3),(key4,val4),
                           (key5,val5),(key6,val6),(key7,val7),(key8,val8)]
      val res_map = Maps.insertLst(init_map,key_val_pairs)	

  in
     mapVal(res_map)
  end

fun make_Sat_Result(r as {assignment,total_var_num,tseitin_var_num,clause_num,
    	                  cnf_conversion_time,dimacs_file_prep_time,sat_solving_time}) =
    let val init_map = Maps.makeMap(SV.compare)
        val (is_sat,asgn) = (case assignment of
                                NONE => (false,unitVal)
                              | SOME(ht) => (true,tableVal(ht)))
      val (key1,val1) = (termVal(AT.makeIdeConstant("satisfiable")),MLBoolToAth(is_sat))
      val (key2,val2) = (termVal(AT.makeIdeConstant("assignment")),asgn)
      val (key3,val3) = (termVal(AT.makeIdeConstant("cnf-conversion-time")),makeAthenaReal(cnf_conversion_time))
      val (key4,val4) = (termVal(AT.makeIdeConstant("sat-solving-time")),makeAthenaReal(sat_solving_time))
      val (key5,val5) = (termVal(AT.makeIdeConstant("dimacs-prep-time")),makeAthenaReal(dimacs_file_prep_time))
      val (key6,val6) = (termVal(AT.makeIdeConstant("clause-num")),makeAthenaInt(clause_num))
      val (key7,val7) = (termVal(AT.makeIdeConstant("total-var-num")),makeAthenaInt(total_var_num))
      val (key8,val8) = (termVal(AT.makeIdeConstant("tseitin-var-num")),makeAthenaInt(tseitin_var_num))
      val key_val_pairs = [(key1,val1),(key2,val2),(key3,val3),(key4,val4),
                           (key5,val5),(key6,val6),(key7,val7),(key8,val8)]
      val res_map = Maps.insertLst(init_map,key_val_pairs)	
    in
      mapVal(res_map)
    end

fun cnfPrimBFun(v1,v2,env,_) =  
 (case coerceValIntoTerm(v2) of
   SOME(t) => 
    (case AT.isIdeConstant(t) of
       SOME(output_format) => 
         (case coerceValIntoProp(v1) of
            SOME(p) => let val r = P.cnf(p)
                       in
                          make_CNF_Map(r,output_format)
                       end
         | _ => (case v1 of
                   listVal(args) =>
                     let val  props = getProps(args,"the argument list of "^N.cnfFun_name,env)
                         val r = P.cnfLst(props)
                     in
                       make_CNF_Map(r,output_format)
                     end
               | _ => primError(wrongArgKind(N.cnfFun_name,1,propLCType,v1))))
     | _ => primError(wrongArgKind(N.cnfFun_name,2,metaIdLCType,v2)))
 | _ => primError(wrongArgKind(N.cnfFun_name,2,metaIdLCType,v2)))

fun satPrimUFun(v,env,_) = 
   (case v of
       listVal(vals) =>
          let val  props = getProps(vals,"the argument list of "^N.satFun_name,env)
	      val table: (value,value) HashTable.hash_table = HashTable.mkTable(SV.hashVal, valEq) (8543,TermHashTable)
              val res = make_Sat_Result(Prop.propSat(props,table,propVal,MLBoolToAth))
          in 
	     res
          end
    | _ => (case coerceValIntoProp(v) of
               SOME(p) => let val table: (value,value) HashTable.hash_table = HashTable.mkTable(SV.hashVal, valEq) (8543,TermHashTable)
                              val res = make_Sat_Result(Prop.propSat([p],table,propVal,MLBoolToAth))
                          in
			     res
                          end
             | _ => primError(wrongArgKind(N.satFun_name,1,listLCType,v))))

fun iteFun([v1,v2,v3],_,_) = 
   (case coerceValIntoTerm(v1) of
       SOME(t) => if AT.isTrueTerm(t) then v2 else v3
     | _ => primError("A boolean term must be given as the first argument to ite'"))
  | iteFun(args,_,_) = primError(wrongArgNumber("ite'",length(args),3))

fun fastSatFun([listVal(prop_vals),selector as SV.closBFunVal(_)],env,ab) = 
     let val props = getProps(prop_vals,"the argument list given to "^N.fastSatFun_name,env)
         fun selector'(t:AT.term,b:bool) = 
                 (case Semantics.evalClosure(selector,[termVal(t),MLBoolToAth(b)],ab,NONE) of
                    termVal(t') => AT.termEq(true_term,t'))
         val res = P.fastSat(props,selector')
         fun f(t,b) = listVal[termVal(t),MLBoolToAth(b)]
     in
       (case res of 
           NONE => termVal(AT.makeIdeConstant("Unsat"))
         | SOME(L) => listVal(map f L))
     end
  | fastSatFun([listVal(prop_vals)],env,ab) = 
     let val props = getProps(prop_vals,"the argument list given to "^N.fastSatFun_name,env)
         val res = P.fastSat(props,fn _ => true) 
         fun f(t,b) = listVal[termVal(t),MLBoolToAth(b)]
     in
       (case res of 
           NONE => termVal(AT.makeIdeConstant("Unsat"))
         | SOME(L) => listVal(map f L))
     end
  | fastSatFun([v],env,ab) = 
      (case coerceValIntoProp(v) of
          SOME(p) => let val res = P.fastSat([p],fn _ => true)
                     in
                       (case res of 
                          NONE => termVal(AT.makeIdeConstant("Unsat"))
                         | SOME(L) => listVal(map (fn (t,b) => listVal[termVal(t),MLBoolToAth(b)]) L))
                     end
        | _ => primError(wrongArgKind(N.fastSatFun_name,1,propLCType,v)))
  | fastSatFun(vals,_,_) = primError(wrongArgNumber(N.fastSatFun_name,length(vals),2))

fun argListName(name) = "the argument list of "^name

fun isSatFun([listVal(vals)],env,_) = 
      let val  props = getProps(vals,"the argument list of "^N.isSatFun_name,env)
          val res = Sat.isSat(map Prop.translateAthenaProp props)
      in 
         MLBoolToAth(res)
      end
  | isSatFun([v],env,_) = primError(wrongArgKind(N.isSatFun_name,1,propLCType,v))
  | isSatFun(args,env,_) = primError(wrongArgNumber(N.isSatFun_name,length(args),1))

fun getIdentifier(v,env) = 
      (case coerceValIntoTerm(v) of
          SOME(t) => (case AthTerm.isIdeConstant(t) of
                         SOME(i) => i 
                       | _ => primError("Only identifiers can appear as options"))
        | _ => primError("Only identifiers can appear as options"))

fun getBoolVal(v,option_name,env) = 
 let fun getBoolTerm(t) = 
           if AthTerm.termEq(t,true_term) then true
           else if AthTerm.termEq(t,false_term) then false
           else primError("Only boolean terms can appear as values for the option "^option_name)
 in
   (case coerceValIntoTerm(v) of
       SOME(t) => getBoolTerm(t)
     | _ => primError("Only boolean terms can appear as values for the option "^option_name))
 end

fun getIntVal(v,option_name,env) = 
 let fun getIntTerm(t) = 
           (case AthTerm.getNumVal(t) of
               SOME(A.int_num(i,_),_) => i
             | _ => primError("Only integer numerals can appear as values for the option "^option_name))
 in
   (case coerceValIntoTerm(v) of
       SOME(t) => Int.toString(getIntTerm(t))
     | _ => primError("Only integer numerals can appear as values for the option "^option_name))
 end

fun getOptions(option_pairs,env) = 
       let val (poly_val,subsorting_val,maxtime_val,cell_opt:value ref option ref) = (ref true,ref false,ref "60",ref NONE)
           fun getOptionValue(option_name as "poly",v) = (poly_val := getBoolVal(v,option_name,env))
             | getOptionValue(option_name as "subsorting",v) = (subsorting_val := getBoolVal(v,option_name,env))
             | getOptionValue(option_name as "max-time",v) = (maxtime_val := getIntVal(v,option_name,env))
             | getOptionValue(option_name,_) = primError("Invalid option name: "^option_name)
           fun loop([],_) = ()
             | loop((listVal([v1,v2]))::more,options_so_far) = 
                 let val option_name = getIdentifier(v1,env)
                     val _ = if Basic.isMember(option_name,options_so_far) then 
                                primError("Duplicate occurrence of option "^option_name)
                             else ()
                     val option_val = getOptionValue(option_name,v2)
                 in  
                    loop(more,option_name::options_so_far)
                 end
             | loop((cellVal c)::more,options_so_far) = 
                     let val _ = cell_opt := SOME(c)
                     in 
                        loop(more,options_so_far)
                     end
             | loop(v::_,_) = primError("Only pairs consisting of an option name and an option value can appear in this option list")
           val _ = loop(option_pairs,[])
       in
         {poly=(!poly_val),subsorting=(!subsorting_val),time=(!maxtime_val),cell_option=(!cell_opt)}
       end

fun stringToSort(str) = 
     let val stream = TextIO.openString (str)
         val sort_var_table: FTerm.term Symbol.htable = Symbol.makeHTable()
         fun find(sort_var) = Symbol.find(sort_var_table,sort_var)
         fun translateSort(sort_as_symterm) = 
   	      (case SymTerm.isVar(sort_as_symterm) of 
  	          SOME(v) => (case find(v) of 
			         SOME(v') => v' 
 			            | _ => (let val v' = FTerm.makeFreshVar() 
				                val _ = Symbol.insert(sort_var_table,v,v')
				            in v' end))
 	        | _ => (case SymTerm.isApp(sort_as_symterm) of
		            SOME(fsym,sorts) => let val sorts' = map translateSort sorts
			  	                in FTerm.makeApp(fsym,sorts') end
                          | _ => raise Basic.Never))
     in
       (case hd(Parse.parse_from_stream(stream)) of 
            A.phraseInput(A.exp(e)) => (case A.isTermAppWithQuotedSymbolsAsVars(e) of
                                           SOME(t) => ((SOME(t,translateSort(t))) handle _ => NONE)
                                         | _ => NONE)
          | _ => NONE) handle _ => NONE
     end    

fun unifiableSortsPrimBFun(v1,v2,_,_) = 
      (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
         (SOME(str1),SOME(str2)) =>
            (case (stringToSort(str1),stringToSort(str2)) of
                (SOME(_,sort_as_fterm1),SOME(_,sort_as_fterm2)) => 
                   let val res = FTerm.unifiable(sort_as_fterm1,sort_as_fterm2)
                   in
                     MLBoolToAth(res)
                   end
              | (NONE,_) => primError("The first string argument given to "^N.unifiable_sort_fun_name^"\ndoes not represent a valid sort: "^str1)
              | _ => primError("The second string argument given to "^N.unifiable_sort_fun_name^"\ndoes not represent a valid sort: "^str2))
      | (SOME(_),NONE) => primError(wrongArgKind(N.unifiable_sort_fun_name,2,stringLCType,v2))
      | _ => primError(wrongArgKind(N.unifiable_sort_fun_name,1,stringLCType,v1)))

fun makeNewProblem(res as ((fsym_string,fsym_strings,fsymbols),(pred_string,pred_strings),conc_and_hyp_strings,osorts),pred_str_ht,all_props,is_mono,format) = 
  let fun inPredTable(str) = (case HashTable.find pred_str_ht str of
                                 SOME(_) => true
                               | _ => false)
      fun debugPrint(str) = ()
      val boolean_fsyms_and_arities = Basic.mapSelect((fn f => let val res = (case Data.getSignature(f) of
                                                                                (arg_sorts,output_sort,_,has_pred_based_sorts) => if F.sortEq(output_sort,F.boolean_sort) 
                                                                                                             then (f,length(arg_sorts)) else (f,~1))
                                                               in
                                                                  res
                                                               end),
                                                      fsymbols,
                                                      (fn (f,i) => let val prefix = if i > 0 then "f" else "c"
                                                                       val str = "("^prefix^(Basic.fsymRenamer (MS.name f))^","^(Int.toString i)^")"
                                                                   in
                                                                      i >= 0 andalso (inPredTable(str) orelse MS.modSymEq(f,Names.mequal_logical_symbol))
                                                                   end))
  in
     if null(boolean_fsyms_and_arities) then NONE
     else 
        let fun makeNewFSym(f) = let val (mods,last_name) = MS.split(f)
                                     fun findName(str) = let val sym = Symbol.symbol(str)
                                                             val whole_sym = Symbol.symbol((if null(mods) then "" else MS.modulePrefix f)^str)
                                                             val msym = MS.makeModSymbol(mods,sym,whole_sym)
                                                             fun alreadyExists(f) = Data.isTermConstructorBool(f)
                                                         in
                                                            if alreadyExists(msym) then findName("fresh_"^str) else msym 
                                                         end
                                 in
                                    findName("fresh_"^(Symbol.name last_name)^"_fun")
                                 end
            val syms_arities_and_new_syms = map (fn (f,i) => (f,i,makeNewFSym f)) boolean_fsyms_and_arities
            val syms_and_new_syms = map (fn (f,i,f') => (f,f')) syms_arities_and_new_syms
            fun addNewFSym(f,f') = (case MS.find(Data.fsym_table,f) of
                                       SOME(afs) => let val afs' = Data.switchNames(f',afs)
                                                        val _ = Data.addFSym(afs')
                                                    in
                                                      ()
                                                    end
                                     | _ => ())
            val _ = map addNewFSym syms_and_new_syms
            val name_map = MS.enterLst(MS.empty_mapping:MS.mod_symbol MS.mapping,syms_and_new_syms)
            val all_props' = map (fn p => Prop.replaceFSymsByFsyms(p,name_map)) all_props
            fun makeBridgeAxiom1(pred_sym,pred_fun_sym,arity) = 
                   let val uvars = map (fn i => ATV.athTermVar("x"^(Int.toString(i)))) (Basic.fromI2N(1,arity))
                       val uvar_terms = map AT.makeVar uvars
                       val left_side = Prop.makeEquality(AT.makeApp(pred_fun_sym,uvar_terms),AT.true_term)
                       val right_side = Prop.makeAtom(AT.makeApp(pred_sym,uvar_terms))
                   in
                      Prop.makeUGen(uvars,Prop.makeBiConditional(left_side,right_side))
                   end
            fun makeBridgeAxiom2(pred_sym,pred_fun_sym,arity) = 
              let val uvars = map (fn i => ATV.athTermVar("x"^(Int.toString(i)))) (Basic.fromI2N(1,arity))
                  val uvar_terms = map AT.makeVar uvars
                  val left_side = Prop.makeEquality(AT.makeApp(pred_fun_sym,uvar_terms),AT.false_term)
                  val right_side = Prop.makeNegation(Prop.makeAtom(AT.makeApp(pred_sym,uvar_terms)))
              in
                 Prop.makeUGen(uvars,Prop.makeBiConditional(left_side,right_side))
               end
            val bridge_axioms = (map (fn (f,i,f') => makeBridgeAxiom1(f,f',i)) syms_arities_and_new_syms)@
                                (map (fn (f,i,f') => makeBridgeAxiom2(f,f',i)) syms_arities_and_new_syms)
            val res as ((fsym_string,fsym_strings,fsymbols),(pred_string,pred_strings),conc_and_hyp_strings,osorts) = 
                      if is_mono then 
                          let val _ = ()
                          in 
                             (case Prop.makeSpassPropList(all_props'@bridge_axioms,Basic.fsymRenamer) of
                                (f,p,c) => ((f,[],[]),(p,[]),c,[]))
                          end
                      else (Prop.makePolyPropList (all_props'@bridge_axioms,format,Basic.fsymRenamer))
        in 
          SOME(res,syms_and_new_syms)
        end
  end

fun spassProvePrimMethod([v,listVal(hyp_vals),listVal(option_pairs)],env,ab) = 
  let val options as {poly,subsorting,time,...} = getOptions(option_pairs,env)
      val is_mono =  not(poly)
      val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.spfPrimMethod_name,env)
      val (lp,rp,comma) = ("(",")",",")
      val _ = checkAbMembersNoPos(hyp_props,ab,N.spfPrimMethod_name) 
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val desired_conc = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.spfPrimMethod_name,1,propLCType,v)))
      fun error() = primError("Failed application of "^N.spfPrimMethod_name^":\nUnable to derive the conclusion "^
                               decide(pprint(0,desired_conc))^" from the given hypotheses")
  in
   (let  val all_props = desired_conc::hyp_props
         val all_free_vars = Prop.freeVarsLst(all_props)
         val res as ((fsym_string,fsym_strings,fsymbols),(pred_string,pred_strings),conc_and_hyp_strings,osorts) = 
                  if is_mono then 
                        (case Prop.makeSpassPropList(all_props,Basic.fsymRenamer) of
                                  (f,p,c) => ((f,[],[]),(p,[]),c,[]))
                  else Prop.makePolyPropList (all_props,"spass",Basic.fsymRenamer)
         val pred_str_ht: (string,bool) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (151,Basic.Never)
         val _ = List.app (fn str => HashTable.insert pred_str_ht (str,true)) pred_strings 
         val (res' as ((fsym_string',fsym_strings',fsymbols'),(pred_string',pred_strings'),conc_and_hyp_strings',osorts'),syms_and_new_syms) = 
                (case makeNewProblem(res,pred_str_ht,all_props,is_mono,"spass") of
                    NONE => (res,[])
                  | SOME(new_res) => new_res)
         val all_premises = if subsorting then (Prop.makeSubsortAxioms(fsymbols',osorts',all_free_vars,"spass"))@(tl conc_and_hyp_strings')
                            else (tl conc_and_hyp_strings')
         val goal = hd(conc_and_hyp_strings')
         val (output_string,bit) = spassProve(fsym_string',pred_string',all_premises,goal,time)
         val _ = List.app (fn (_,f') => Data.removeFSymByName(f')) syms_and_new_syms
    in
       if bit then propVal(desired_conc) else error() 
    end) handle _ => error()
  end
| spassProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
  let val is_mono =  false
      val max_seconds = "60"
      val subsorting = false 
      val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^ 
                      N.spfPrimMethod_name,env)
      val _ = checkAbMembersNoPos(hyp_props,ab,N.spfPrimMethod_name) 
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val desired_conc = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.spfPrimMethod_name,1,propLCType,v)))
      val all_props = desired_conc::hyp_props
      val res as ((fsym_string,fsym_strings,fsymbols),(pred_string,pred_strings),conc_and_hyp_strings,osorts) = 
             if is_mono then (case Prop.makeSpassPropList(desired_conc::hyp_props,Basic.fsymRenamer) of
                                 (f,p,s) => ((f,[],[]),(p,[]),s,[]))
             else Prop.makePolyPropList (desired_conc::hyp_props,"spass",Basic.fsymRenamer)
      val pred_str_ht: (string,bool) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (151,Basic.Never)
      val _ = List.app (fn str => HashTable.insert pred_str_ht (str,true)) pred_strings 
      val (res' as ((fsym_string',fsym_strings',fsymbols'),(pred_string',pred_strings'),conc_and_hyp_strings',osorts'),syms_and_new_syms) = 
             (case makeNewProblem(res,pred_str_ht,all_props,is_mono,"spass") of
                 NONE => (res,[])
               | SOME(new_res) => new_res)
      val (output_string,bit) = spassProve(fsym_string',pred_string',tl(conc_and_hyp_strings'),
					   hd(conc_and_hyp_strings'),max_seconds)
      val _ = List.app (fn (_,f') => Data.removeFSymByName(f')) syms_and_new_syms
  in
     if bit then propVal(desired_conc) else primError("Failed application of "^N.spfPrimMethod_name^
							":\nUnable to derive the conclusion "^
        decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 |  spassProvePrimMethod([v,_],_,_) = 
       primError(wrongArgKind(N.spfPrimMethod_name,2,"list of sentences",v))
 |  spassProvePrimMethod(args,_,_) = 
     primError(wrongArgNumber(N.spfPrimMethod_name,length(args),2))

fun unLimSpassProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
  let val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.spfPrimMethod_name,env)
      val _ = checkAbMembersNoPos(hyp_props,ab,N.spfPrimMethod_name) 
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val desired_conc = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.spfPrimMethod_name,1,propLCType,v)))
      val (fsym_string,pred_string,conc_and_hyp_strings) = Prop.makeSpassPropList(desired_conc::hyp_props,Basic.fsymRenamer)
      val (output_string,bit) = unLimSpassProve(fsym_string,pred_string,tl(conc_and_hyp_strings),
					   hd(conc_and_hyp_strings))
  in
     if bit then propVal(desired_conc) else primError("Failed application of "^N.spfPrimMethod_name^
							":\nUnable to derive the conclusion "^
        decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 |  unLimSpassProvePrimMethod(args,_,_) = primError(wrongArgNumber(N.spfPrimMethod_name,length(args),2))

fun vProve(goal_val, premise_vals,env,ab,max_seconds) = 
  let val vi = getVampIndex()
      val (vamp_in_fname,vamp_out_fname) = (Paths.vampireInName(vi),Paths.vampireOutName(vi))
      val hyp_props = getPropsOrListProps(premise_vals,"the list argument of "^N.vpfPrimMethod_name,env)
      val _ = checkAbMembersNoPos(hyp_props,ab,N.vpfPrimMethod_name)
      val desired_conc = (case coerceValIntoProp(goal_val) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.vpfPrimMethod_name,1,
						propLCType,goal_val))) 
      val ((fsym_string,fsym_strings,fsymbols),(pred_string,pred_strings),conc_and_hyp_strings,osorts) = 
          Prop.makePolySpassPropList (desired_conc::hyp_props)
      val (vamp_axioms,vamp_conjectures) = 
            Flotter_CNF_To_TTPP_CNF(fsym_string,pred_string,tl(conc_and_hyp_strings),
	 			     SOME(hd(conc_and_hyp_strings)))
      val vamp_problem_stream = TextIO.openOut(vamp_in_fname)
      fun write(str) = TextIO.output(vamp_problem_stream,str)
      val _ = (List.app write vamp_axioms;List.app write vamp_conjectures)
      val _ = TextIO.closeOut(vamp_problem_stream)
      val _ = OS.Process.system(Names.vampire_linux_binary ^ " --time_limit "^max_seconds^" "^vamp_in_fname^" > "^vamp_out_fname)
      val vamp_answer_stream = TextIO.openIn(vamp_out_fname)
      val answer_bit = findLine(vamp_answer_stream,vamp_proof_line)
      val _ = TextIO.closeIn(vamp_answer_stream)
      val _ = deleteFile(vamp_in_fname)
      val _ = deleteFile(vamp_out_fname)
  in
     (answer_bit,desired_conc)
  end
and 
 decide(str) = if Util.small(str,40) then str else "\n"^str
and
 vampireProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
  let val (answer_bit,desired_conc) = vProve(v,hyp_vals,env,ab,"50")
  in
     if answer_bit then propVal(desired_conc) 
     else primError("Failed application of "^N.vpfPrimMethod_name^
	          ":\nUnable to derive the conclusion "^
                  decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 | vampireProvePrimMethod([v,listVal(hyp_vals),seconds],env,ab) = 
     let val max_seconds = 
          (case isStringValConstructive(seconds) of
	     SOME(str) => 
               (case Int.fromString(str) of
	           SOME(n) => if (n > 0) then str 
                              else primError("Failed application of "^N.vpfPrimMethod_name^
       	   	                           ": invalid time limit: "^str)
		      | _ => primError("Failed application of "^N.vpfPrimMethod_name^
       	   	                           ": invalid time limit: "^str))
          | _ => primError(wrongArgKind(N.vpfPrimMethod_name,3,
				      stringLCType,seconds)))
         val (answer_bit,desired_conc) = vProve(v,hyp_vals,env,ab,max_seconds)
     in
        if answer_bit then propVal(desired_conc) 
        else primError("Failed application of "^N.vpfPrimMethod_name^
   	             ":\nUnable to derive the conclusion "^
                     decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 |  vampireProvePrimMethod(args,_,_) = 
	primError(wrongArgNumber(N.vpfPrimMethod_name,length(args),2))

fun unLimVampireProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
  let val vi = getVampIndex()
      val (vamp_in_fname,vamp_out_fname) = (Paths.vampireInName(vi),Paths.vampireOutName(vi))
      val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.vpfPrimMethod_name,env)
      val _ = checkAbMembersNoPos(hyp_props,ab,N.vpfPrimMethod_name) 
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val desired_conc = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.vpfPrimMethod_name,1,propLCType,v)))
						
      val (fsym_string,pred_string,conc_and_hyp_strings) = Prop.makeSpassPropList(desired_conc::hyp_props,Basic.fsymRenamer)
      val (vamp_axioms,vamp_conjectures) = Flotter_CNF_To_TTPP_CNF(fsym_string,pred_string,tl(conc_and_hyp_strings),
					   SOME(hd(conc_and_hyp_strings)))
      val vamp_problem_stream = TextIO.openOut(vamp_in_fname)
      fun write(str) = TextIO.output(vamp_problem_stream,str)
      val _ = (List.app write vamp_axioms;List.app write vamp_conjectures)
      val _ = TextIO.closeOut(vamp_problem_stream)
      val _ = OS.Process.system(Names.vampire_linux_binary ^ " " ^ vamp_in_fname ^ " > " ^ vamp_out_fname)
      val vamp_answer_stream = TextIO.openIn(vamp_out_fname)
      val answer_bit = findLine(vamp_answer_stream,vamp_proof_line)
      val _ = TextIO.closeIn(vamp_answer_stream)
      val _ = deleteFile(vamp_in_fname)
      val _ = deleteFile(vamp_out_fname)
  in
     if answer_bit then propVal(desired_conc) else primError("Failed application of "^N.vpfPrimMethod_name^
							":\nUnable to derive the conclusion "^
        decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 |  unLimVampireProvePrimMethod(args,_,_) = 
	primError(wrongArgNumber(N.vpfPrimMethod_name,length(args),2))

(******** Polymorphic Vampire interface : ********)

fun polyVProve(goal, premises,env,ab,max_seconds,mono:bool,subsorting:bool) = 
  let val vi = getVampIndex()
      val (vamp_in_fname,vamp_out_fname) = (Paths.vampireInName(vi),Paths.vampireOutName(vi))
      val ax_index = ref(0)
      val premise_array = Array.fromList(premises)
      fun getAxNum() = (Basic.inc(ax_index);"ax"^(Int.toString(!ax_index)))
      val _ = checkAbMembersNoPos(premises,ab,N.vpfPrimMethod_name)
      fun makeAxiom(hyp_str) = if hyp_str = "" then "" else "\nfof("^(getAxNum())^",axiom,("^hyp_str^")).\n"
      val all_props = goal::premises
      val all_free_vars = Prop.freeVarsLst(all_props)
      val res as ((fsym_string,fsym_strings,fsymbols),(pred_string,pred_strings),conc_and_hyp_strings,osorts) = 
                if mono then 
                   let val strings = Prop.makeTPTPPropList(all_props)
                   in 
                      (("",[],[]),("",[]),strings,[])
                   end
                else Prop.makePolyPropList(all_props,"vampire",Basic.fsymRenamer)
      val pred_str_ht: (string,bool) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (151,Basic.Never)
      val _ = List.app (fn str => HashTable.insert pred_str_ht (str,true)) pred_strings 
      val (res' as ((fsym_string',fsym_strings',fsymbols'),(pred_string',pred_strings'),conc_and_hyp_strings',osorts'),syms_and_new_syms) = 
                (case makeNewProblem(res,pred_str_ht,all_props,mono,"vampire") of
                    NONE => (res,[])
                  | SOME(new_res) => new_res)
      val conc_str = hd(conc_and_hyp_strings')
      val hyp_strings = tl(conc_and_hyp_strings')
      val hyp_strings' = if subsorting then (Prop.makeSubsortAxioms(fsymbols,osorts,all_free_vars,"vampire"))@hyp_strings  
                         else hyp_strings 
      val conc = "\nfof(c,conjecture,("^conc_str^")).\n"
      val hyps = Basic.mapSelect(makeAxiom,hyp_strings',fn str => not(str = ""))
      val vamp_problem_stream = TextIO.openOut(vamp_in_fname)
      fun write(str) = TextIO.output(vamp_problem_stream,str)
      val _ = (List.app write hyps;write conc)
      val _ = TextIO.closeOut(vamp_problem_stream)
      val cmd = Names.vampire_binary ^ " --proof tptp --show_skolemisations on --time_limit "^max_seconds^" --input_file "^vamp_in_fname^" > "^vamp_out_fname
      val _ = OS.Process.system(cmd)
      val vamp_answer_stream = TextIO.openIn(vamp_out_fname)
      val answer_bit = findLine(vamp_answer_stream,vamp_proof_line)
      val used_premise_indices = if not(answer_bit) then [] else findUsedPremises(vamp_answer_stream)
      val used_premises = let fun loop([],res) = res
                                | loop(i::more,res) = loop(more,(Array.sub(premise_array,i-1))::res)
                          in SOME(loop(used_premise_indices,[])) end handle _ => NONE
      val _ = TextIO.closeIn(vamp_answer_stream)
      val _ = deleteFile(vamp_in_fname)
      val _ = deleteFile(vamp_out_fname)
      val _ = List.app (fn (_,f') => Data.removeFSymByName(f')) syms_and_new_syms
  in
     (answer_bit,goal,used_premises)
  end
and 
 polyDecide(str) = if Util.small(str,40) then str else "\n"^str
and
 polyVampireProvePrimMethod([v,listVal(hyp_vals),listVal(option_pairs)],env,ab) = 
  let val options as {poly,subsorting,time,cell_option,...} = getOptions(option_pairs,env) 
      val is_mono =  not(poly)
      val (lp,rp,comma) = ("(",")",",")
      val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.vpfPrimMethod_name,env)
      val goal_prop = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.vpfPrimMethod_name,1,propLCType,v)))
      val (answer_bit,desired_conc,used_hyps) = polyVProve(goal_prop,hyp_props,env,ab,time,is_mono,subsorting)
  in
     if answer_bit then 
        let val _ = (case (cell_option,used_hyps) of
                        (SOME(c),SOME(props)) => (c := listVal(map propVal props))
                      | _ => ())
        in 
           propVal(desired_conc) 
        end
     else primError("Failed application of "^N.vpfPrimMethod_name^
	             ":\nUnable to derive the conclusion "^
                     polyDecide(pprint(0,desired_conc))^" from the given hypotheses")
                  
  end
 | polyVampireProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
     let val is_mono =  false
         val max_seconds = "60"
         val subsorting = false 
         val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.vpfPrimMethod_name,env)
         val goal_prop = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.vpfPrimMethod_name,1,
						propLCType,v)))
         val (answer_bit,desired_conc,used_hyps) = polyVProve(goal_prop,hyp_props,env,ab,max_seconds,false,false)
     in
        if answer_bit then propVal(desired_conc) 
        else primError("Failed application of "^N.vpfPrimMethod_name^
   	             ":\nUnable to derive the conclusion "^
                     polyDecide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 |  polyVampireProvePrimMethod(args,_,_) =  primError(wrongArgNumber(N.vpfPrimMethod_name,length(args),2))

fun EProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
  let val (ei,ax_index) = (getEIndex(),ref(0))
      val (e_in_fname,e_out_fname) = (Paths.eInName(ei),Paths.eOutName(ei))
      fun getAxNum() = (Basic.inc(ax_index);"A"^(Int.toString(!ax_index)))
      val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.epfPrimMethod_name,env)
      val _ = checkAbMembersNoPos(hyp_props,ab,N.epfPrimMethod_name)
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val desired_conc = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.epfPrimMethod_name,1,propLCType,v)))
      val TSTP_axioms = map (fn P => "\nfof("^(getAxNum())^",axiom,("^
				     (Prop.makeTSTPProp(P))^")).\n") hyp_props
      val TSTP_conjecture = "\n\nfof(C"^",conjecture,("^(Prop.makeTSTPProp(desired_conc))^")).\n" 
      val e_problem_stream = TextIO.openOut(e_in_fname)
      fun write(str) = TextIO.output(e_problem_stream,str)
      val _ = (List.app write TSTP_axioms; write(TSTP_conjecture))
      val _ = TextIO.closeOut(e_problem_stream)
      val cmd = "eprover --tstp-format --cpu-limit=60 "^e_in_fname^" > "^e_out_fname
      val st = OS.Process.system(cmd)
      val e_answer_stream = TextIO.openIn(e_out_fname)
      val answer_bit = findLine(e_answer_stream,e_proof_line)
      val _ = TextIO.closeIn(e_answer_stream)
      val _ = (deleteFile(e_in_fname);deleteFile(e_out_fname))
  in
     if answer_bit then propVal(desired_conc) else primError("Failed application of "^N.epfPrimMethod_name^
							     ":\nUnable to derive the conclusion "^
                                                             decide(pprint(0,desired_conc))^" from the given hypotheses")
  end

fun monoVampireProvePrimMethod([v,listVal(hyp_vals)],env,ab) = 
  let val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.mvpfPrimMethod_name,env)
      val goal_prop = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.mvpfPrimMethod_name,1,propLCType,v)))
      val (answer_bit,desired_conc,used_hyps) = polyVProve(goal_prop,hyp_props,env,ab,"50",true,false)
  in
     if answer_bit then propVal(desired_conc) 
     else primError("Failed application of "^N.vpfPrimMethod_name^
	            ":\nUnable to derive the conclusion "^
                    decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 | monoVampireProvePrimMethod([v,listVal(hyp_vals),seconds],env,ab) = 
     let val hyp_props = getPropsOrListProps(hyp_vals,"the list argument of "^N.mvpfPrimMethod_name,env)
      val goal_prop = (case coerceValIntoProp(v) of
                                   SOME(P) => P
				 | _ => primError(wrongArgKind(N.mvpfPrimMethod_name,1,propLCType,v)))
      val max_seconds = 
          (case isStringValConstructive(seconds) of
	     SOME(str) => 
               (case Int.fromString(str) of
	           SOME(n) => if (n > 0) then str 
                              else primError("Failed application of "^N.vpfPrimMethod_name^": invalid time limit: "^str)
		      | _ => primError("Failed application of "^N.vpfPrimMethod_name^": invalid time limit: "^str))
          | _ => primError(wrongArgKind(N.vpfPrimMethod_name,3,stringLCType,seconds)))
         val (answer_bit,desired_conc,used_hyps) = polyVProve(goal_prop,hyp_props,env,ab,max_seconds,true,false)
     in
        if answer_bit then propVal(desired_conc) 
        else primError("Failed application of "^N.vpfPrimMethod_name^
   	               ":\nUnable to derive the conclusion "^
                       decide(pprint(0,desired_conc))^" from the given hypotheses")
  end
 |  monoVampireProvePrimMethod(args,_,_) = primError(wrongArgNumber(N.vpfPrimMethod_name,length(args),2))
and  decide(str) = if Util.small(str,40) then str else "\n"^str 

fun getMultisortedModelPrimFun([listVal(vals),listVal(sort_names),listVal(sym_sig_pair_list)],env,ab) = 
  let val vi = getParadoxIndex()
      val ax_index = ref(0)
      val is_sort_names = map (fn v => case isStringValConstructive(v) of
					  SOME(str) => str 
				        | _ => "") sort_names
      fun getAxNum() = (Basic.inc(ax_index);"ax"^(Int.toString(!ax_index)))
      val (paradox_in_fname,paradox_out_fname) = (Paths.paradoxInName vi,Paths.paradoxOutName vi)
      val ptemp_file = (!Paths.tmp_dir) ^ "ptemp"
      val props = getPropsOrListProps(vals,"the list argument of "^N.paradoxPrimFun_name,env)
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val TPTP_prop_strings = map (fn P => "\nfof("^(getAxNum())^",axiom,("^
				       (Prop.makeTPTPProp(P))^")).\n") props

      val paradox_problem_stream = TextIO.openOut(paradox_in_fname)
      fun write(str) = TextIO.output(paradox_problem_stream,str)
      val _ = List.app write TPTP_prop_strings
      val _ = TextIO.closeOut(paradox_problem_stream)
      val cmd = "paradox  "^paradox_in_fname^" --model "^paradox_out_fname^" > "^ptemp_file
      val st = OS.Process.system(cmd)
      val paradox_model_stream_opt = SOME(TextIO.openIn(paradox_out_fname)) handle _ => NONE
      val _ = (case paradox_model_stream_opt of
		 SOME(pms) => (print("\nA model was found!\n");
			       printMSParadoxFile(pms,is_sort_names,sym_sig_pair_list);TextIO.closeIn(pms))
	       | _ => print("\nNo model was found.\n\n"))
      val _ = (deleteFile(paradox_in_fname);deleteFile(paradox_out_fname);deleteFile(ptemp_file))
  in
    unitVal
  end
 |  getMultisortedModelPrimFun(args,_,_) = 
      primError(wrongArgNumber(N.getMultisortedModelPrimFun_name,length(args),2))

fun paradoxProvePrimFun([listVal(vals)],env,ab) = 
  let val vi = getParadoxIndex()
      val ax_index = ref(0)
      fun getAxNum() = (Basic.inc(ax_index);"ax"^(Int.toString(!ax_index)))
      val (paradox_in_fname,paradox_out_fname) = (Paths.paradoxInName(vi),Paths.paradoxOutName(vi))
      val props = getPropsOrListProps(vals,"the list argument of "^N.paradoxPrimFun_name,env)
      fun decide(str) = if Util.small(str,40) then str else "\n"^str
      val TPTP_prop_strings = map (fn P => "\nfof("^(getAxNum())^",axiom,("^
				       (Prop.makeTPTPProp(P))^")).\n") props

      val paradox_problem_stream = TextIO.openOut(paradox_in_fname)
      fun write(str) = TextIO.output(paradox_problem_stream,str)
      val _ = List.app write TPTP_prop_strings
      val _ = TextIO.closeOut(paradox_problem_stream)

      val cmd = "paradox  "^paradox_in_fname^" --model "^paradox_out_fname^" > ccc "
      val st = OS.Process.system(cmd)
      val paradox_model_stream_opt = SOME(TextIO.openIn(paradox_out_fname)) handle _ => NONE
      val _ = (case paradox_model_stream_opt of
		 SOME(pms) => (print("\nA model was found! Here it is: \n\n");
			       printParadoxFile(pms);TextIO.closeIn(pms))
	       | _ => print("\nNo model was found.\n\n"))
  in
    unitVal
  end
 |  paradoxProvePrimFun(args,_,_) = primError(wrongArgNumber(N.paradoxPrimFun_name,length(args),2))

fun getABFun([],_,ab) = listVal(map propVal (ABase.getAll(ab)))

fun getBucketSizesFun([],_,ab) = listVal(map (fn i => termVal(AthTerm.makeNumTerm(A.int_num(i,ref "")))) (ABase.bucketSizes()))

fun showBucketStatisticsFun([],_,ab) = (print("\n"^(ABase.getBucketSizeStatistics())^"\n\n");unitVal)

fun getAllFSymsFun([],_,_) = listVal(map (fn x => termConVal(SV.regFSym(x))) (Data.allFSyms()))
  | getAllFSymsFun(vals,env,ab) = primError(wrongArgNumber(N.allFunSymsFun_name,length(vals),0))

fun funSymFun([v],env,_) = 
     (case isStringValConstructive(v) of
	SOME(str) => (case Data.isTermConstructorAsFSymOptionGeneral(A.makeMS(str,NONE)) of 
                         SOME(s) => termConVal(regFSym(s))
                       | _ => primError(wrongArgKind(N.funSymFun_name,1,termConLCType,v)))
      | _ => primError(wrongArgKind(N.funSymFun_name,1,termConLCType,v)))
  | funSymFun(args,env,_) = primError(wrongArgNumber(N.funSymFun_name,length(args),1))

val lookUpEnvBindingFun: prim_fun_type = 
 (fn ([v],env,_) => 
     (case isStringValConstructive(v) of
	SOME(str) => let val msym = A.makeMS(str,NONE)
                         val (mods,sym) = MS.split(msym)
                     in
                     (case Semantics.lookUp(!env,mods,sym) of
  			SOME(v) => v 
                      | _ => primError("No top-level binding for "^str))
                     end
      | _ => primError(wrongArgKind(N.lookUpEnvBindingFun_name,1,stringLCType,v)))
  | (args,_,_) => 
	primError(wrongArgNumber(N.lookUpEnvBindingFun_name,length(args),2)))

fun makePathPrimBFun(v1,v2,env,_) = 
     (case (isStringValConstructive(v1),isStringValConstructive(v2)) of
 	 (SOME(str1),SOME(str2)) => MLStringToAthString(Paths.makePath(str1,str2))
       | (SOME(_),NONE) => primError(wrongArgKind(N.makePathFun_name,2,stringLCType,v2))
       | _ => primError(wrongArgKind(N.makePathFun_name,1,stringLCType,v1)))

fun rcongPrimBMethod(v1,v2,env,ab) = 
       (case coercePositionlessValsIntoProps([v2,v1],N.rcongPrimMethod_name) of
           plst as [P1,P2] =>
            (case (P.isAtom(P1),P.isAtom(P2)) of 
                (SOME(atom1),SOME(atom2)) =>
                  (case (AthTerm.isApp(atom1),AthTerm.isApp(atom2)) of 
                      (SOME(f1,terms1),SOME(f2,terms2)) =>            
                          if MS.modSymEq(f1,f2) then
                             let val _ = checkOneAbMemberNoPos(P1,ab,N.rcongPrimMethod_name)
                                 val equalities = map Prop.makeEquality (ListPair.zip(terms1,terms2))
                                 fun g(p) = ABase.isMember(p,ab) orelse ABase.isMember(Prop.swapEquality(p),ab)
                                            orelse Prop.isRefEquality(p)
                                 val _ = checkAbMembersNoPosGeneral(equalities,g,N.rcongPrimMethod_name)
                                                               
                             in 
                                propVal(P2) 
                             end
                           else primError("Failed application of "^N.rcongPrimMethod_name^"---the two"^
                                          "\natoms are constructed by different function symbols")
                    | (SOME(_),_) => primError("Failed application of "^N.rcongPrimMethod_name^"---a variable cannot\n"^
                                               "appear as an argument to "^N.rcongPrimMethod_name)
                    | (_,SOME(_)) => primError("Failed application of "^N.rcongPrimMethod_name^"---a variable cannot\n"^
                                               "appear as an argument to "^N.rcongPrimMethod_name)
                    | (_,_) => primError("Failed application of "^N.rcongPrimMethod_name^"---a variable cannot\n"^
                                         "appear as an argument to "^N.rcongPrimMethod_name))
              | (SOME(_),_) => primError(wrongArgKind(N.rcongPrimMethod_name,2,atomLCType,v2))
              | (_,SOME(_)) => primError(wrongArgKind(N.rcongPrimMethod_name,1,atomLCType,v1))
              | (_,_) => primError(wrongArgKind(N.rcongPrimMethod_name,1,atomLCType,v1)))
         | _ => raise Basic.Never)

fun fcongPrimMethod(args as [v],env,ab) = 
       (case coercePositionlessValsIntoProps([v],N.fcongPrimMethod_name) of
           plst as [P] => 
            (case (P.isAtom(P)) of 
                SOME(at) =>
                   (case AthTerm.isApp(at) of 
                       SOME(f,terms) => 
                          if MS.modSymEq(f,N.mequal_logical_symbol) then
                             (case terms of 
                                 [t1,t2] => (case (AthTerm.isApp(t1),AthTerm.isApp(t2)) of 
                                                (SOME(f1,terms1),SOME(f2,terms2)) => 
                                                    if not(MS.modSymEq(f1,f2)) then
   			    	                       primError("Failed application of "^N.fcongPrimMethod_name^
                                                                 "---the two atoms are constructed\nby different "^
                                                                 "function symbols.")
                                                    else let val equalities = map Prop.makeEquality 
						    	                          (ListPair.zip(terms1,terms2))
                                                             fun g(p) = ABase.isMember(p,ab) orelse 
                                                                              ABase.isMember(Prop.swapEquality(p),ab) 
                                                                         orelse  Prop.isRefEquality(p)
                                                             val _ = checkAbMembersNoPosGeneral(equalities,g,N.fcongPrimMethod_name)
                                                          in 
							      propVal(P) 
                                                          end
                                               | _ => primError("Failed application of "^N.fcongPrimMethod_name^
                                                                "---a variable cannot\nappear as one of the two "^ 
                                                                "equated terms.")))
                          else primError("Failed application of "^N.fcongPrimMethod_name^"---an identity "^ 
                                         "was expected here.")
                    | _ => primError("Failed application of "^N.fcongPrimMethod_name^"---an identity "^ "was expected here"))
                                     
               | _ => primError("Failed application of "^N.fcongPrimMethod_name^"---an identity "^ 
                                "was expected here"))
         | _ => raise Basic.Never)
  | fcongPrimMethod(args as _::_,ea,pf) = fcongPrimMethod([List.last(args)],ea,pf)
  | fcongPrimMethod(args as vals,env,ab) = primError(wrongArgNumber(N.fcongPrimMethod_name,length(args),1))

fun evalPhrase((p,fids),env,ab) = let val env' = Semantics.makeEnv(fids,!env) 
                                      val v = Semantics.evalPhrase(p,env',ab)
                                       in
					   v 
                                       end

fun infixProcess(p:A.phrase,eval_env,fids) = 
  let 
      fun evaluatePhrase(e) = evalPhrase((e,fids),eval_env,!top_assum_base)
      val no_op_val = (~1,~1)
      fun debugPrint(str) = if !(Options.call_stack_size) < 201 then () else print(str)
      fun headInapplicable(proc) = A.inapplicable(proc) 
                                      orelse (case proc of
                                               A.exp(e as A.idExp(_)) => ((case Semantics.isApplicable(evaluatePhrase(A.exp e)) of
                                                                              (true,_) => false
                                                                            | (false,true) => false
                                                                            | _ => false)  handle _ => false)
                                             | _ => false)
      fun ipExp(e as A.appExp({proc,args,alt_exp=(mcell as ref(NONE)),pos}),op_table) = 
             let val proc' = ipPhrase(proc,op_table) 
                 val args' = map (fn p => ipPhrase(p,op_table)) args  
                 val infix_likely = headInapplicable(proc)  
             in
               if length(args) = 0 then e
               else 
                (case ((SOME(let val res = InfixParser.parse(e,evaluatePhrase,op_table) val _ = () in res end),"")
                             handle InfixParser.InfixParseError(msg) => (NONE,msg)
                                  | Semantics.EvalError(msg,_) => (NONE,msg)
                                  | _ => (NONE,"")) of
                       (NONE,msg) => (if infix_likely andalso not(msg = "") then 
                                         ((print "\nInfix parsing error...\n");raise Semantics.EvalError(msg,NONE))
                                      else ();e)
                     | (SOME(A.exp e'),_) => (mcell := SOME(e');e))
             end
        | ipExp(e as A.appExp({proc,args,alt_exp=(mcell as ref(SOME(e'))),pos,...}),_) = e
        | ipExp(A.opExp({op_exp=e',pos,...}),op_table) = A.opExp({op_exp=ipExp(e',op_table),pos=pos})
        | ipExp(A.whileExp({test,body,pos}),ot) = A.whileExp({test=ipPhrase(test,ot),body=ipPhrase(body,ot),pos=pos})
        | ipExp(A.beginExp({members,pos}),ot) = A.beginExp({members=map (fn p => ipPhrase(p,ot)) members,pos=pos})
        | ipExp(A.logicalAndExp({args,pos}),ot) = A.logicalAndExp({args=map (fn p => ipPhrase(p,ot)) args,pos=pos})
        | ipExp(A.logicalOrExp({args,pos}),ot) = A.logicalOrExp({args=map (fn p => ipPhrase(p,ot)) args,pos=pos})
        | ipExp(A.functionExp({body=b,params,pos}),ot) = 
                A.functionExp({params=params,body=ipExp(b,extendOpTabWithParams(ot,params)),pos=pos})
        | ipExp(A.listExp({members,pos,...}),ot) = A.listExp({members=map (fn p => ipPhrase(p,ot)) members,pos=pos})
        | ipExp(A.checkExp({clauses,pos}),ot) = A.checkExp({clauses=map (fn c => ipCheckClause(c,ot)) clauses,pos=pos})
        | ipExp(A.methodExp({params,body,pos,name}),ot) = A.methodExp({params=params,body=ipDed(body,extendOpTabWithParams(ot,params)),
                                                                            pos=pos,name=name})
        | ipExp(A.matchExp({discriminant,clauses,pos}),ot) = A.matchExp({discriminant=ipPhrase(discriminant,ot),
                                                                         clauses=map (fn c => ipMatchClause(c,ot)) clauses,pos=pos})
        | ipExp(A.tryExp({choices,pos,...}),ot) = A.tryExp({choices=map (fn e => ipExp(e,ot)) choices,pos=pos})
        | ipExp(A.cellExp({contents,pos}),ot) = A.cellExp({contents=ipPhrase(contents,ot),pos=pos})
        | ipExp(A.refExp({cell_exp,pos}),ot) = A.refExp({cell_exp=ipExp(cell_exp,ot),pos=pos})
        | ipExp(A.setCellExp({cell_exp,set_phrase,pos}),ot) = 
              A.setCellExp({cell_exp=ipExp(cell_exp,ot),set_phrase=ipPhrase(set_phrase,ot),pos=pos})
        | ipExp(A.vectorInitExp({length_exp,init_val,pos}),ot) = 
                  A.vectorInitExp({length_exp=ipExp(length_exp,ot),init_val=ipPhrase(init_val,ot),pos=pos})
        | ipExp(A.vectorSetExp({vector_exp,index_exp,new_val,pos}),ot) =  
                A.vectorSetExp({vector_exp=ipExp(vector_exp,ot),index_exp=ipExp(index_exp,ot),new_val=ipPhrase(new_val,ot),pos=pos})
        | ipExp(A.vectorSubExp({vector_exp,index_exp,pos}),ot) = 
               A.vectorSubExp({vector_exp=ipExp(vector_exp,ot),index_exp=ipExp(index_exp,ot),pos=pos})
        | ipExp(A.letExp({bindings,body,pos}),ot) = 
            A.letExp({bindings=ipBindings(bindings,ot,[]),
                      body=ipExp(body,extendOpTabWithBindings(ot,bindings)),pos=pos})
        | ipExp(A.letRecExp({bindings,body,pos}),ot) = 
             let val bindings' = ipBindings(bindings,ot,[])
                 val new_ot = extendOpTabWithBindings(ot,bindings)
                 val bindings'' = (map (fn (binding as {bpat,def,pos}) => {bpat=ipPat(bpat,new_ot),def=ipPhrase(def,new_ot),pos=pos}) bindings')
             in
                A.letRecExp({bindings=bindings'',body=ipExp(body,new_ot),pos=pos})
             end
        | ipExp(e,op_table) = e
      and ipCheckClause({test=A.boolCond p,result},ot) = {test=A.boolCond(ipPhrase(p,ot)),result=ipExp(result,ot)}
        | ipCheckClause({test=A.elseCond,result},ot) = {test=A.elseCond,result=ipExp(result,ot)}
      and ipDCheckClause({test=A.boolCond p,result},ot) = {test=A.boolCond(ipPhrase(p,ot)),result=ipDed(result,ot)}
        | ipDCheckClause({test=A.elseCond,result},ot) = {test=A.elseCond,result=ipDed(result,ot)}
      and ipDed(A.assumeDed({assumption,body,pos}),ot) = A.assumeDed({assumption=ipPhrase(assumption,ot),body=ipDed(body,ot),pos=pos}) 
        | ipDed(A.assumeLetDed({bindings,body,pos}),ot) = A.assumeLetDed({bindings=ipBindings(bindings,ot,[]),body=ipDed(body,ot),pos=pos})
        | ipDed(A.infixAssumeDed({bindings,body,pos}),ot) = A.infixAssumeDed({bindings=ipBindings(bindings,ot,[]),body=ipDed(body,ot),pos=pos})
        | ipDed(A.absurdDed({hyp,body,pos}),ot) = A.absurdDed({hyp=ipPhrase(hyp,ot),body=ipDed(body,ot),pos=pos})
        | ipDed(A.absurdLetDed({named_hyp,body,pos}),ot) = 
                A.absurdLetDed({named_hyp=hd(ipBindings([named_hyp],ot,[])),body=ipDed(body,ot),pos=pos})
        | ipDed(A.methodAppDed({method,args,pos}),ot) = 
                A.methodAppDed({method=ipExp(method,ot),args=map (fn p => ipPhrase(p,ot)) args,pos=pos})


        | ipDed(A.BMethAppDed({method,arg1,arg2,pos}),ot) = 
                A.BMethAppDed({method=ipExp(method,ot),arg1=ipPhrase(arg1,ot),arg2=ipPhrase(arg2,ot),pos=pos})

        | ipDed(A.UMethAppDed({method,arg,pos}),ot) = 
                A.UMethAppDed({method=ipExp(method,ot),arg=ipPhrase(arg,ot),pos=pos})

        | ipDed(A.matchDed({discriminant,clauses,pos}),ot) = 
                A.matchDed({discriminant=ipPhrase(discriminant,ot),clauses=map (fn c => ipDMatchClause(c,ot)) clauses,pos=pos})
        | ipDed(A.inductionDed({prop,clauses,pos}),ot) = 
                A.inductionDed({prop=ipPhrase(prop,ot),clauses = map (fn c => ipDMatchClause(c,ot)) clauses,pos=pos})
        | ipDed(A.structureCasesDed({prop,clauses,term,pos}),ot) = 
           (case term of
               NONE => A.structureCasesDed({prop=ipPhrase(prop,ot),term=NONE,clauses=map (fn c => ipDMatchClause(c,ot)) clauses,pos=pos})
             | SOME(dt_exp) => A.structureCasesDed({prop=ipPhrase(prop,ot),term=SOME(ipExp(dt_exp,ot)),clauses=map (fn c => ipDMatchClause(c,ot)) clauses,pos=pos}))
        | ipDed(A.tryDed({choices,pos}),ot) = A.tryDed({choices=map (fn d => ipDed(d,ot)) choices,pos=pos})
        | ipDed(A.letDed({bindings,body,pos}),ot) = 
               A.letDed({bindings=ipBindings(bindings,ot,[]),body=ipDed(body,extendOpTabWithBindings(ot,bindings)),pos=pos})

        | ipDed(A.letRecDed({bindings,body,pos}),ot) = 
               A.letRecDed({bindings=ipBindings(bindings,ot,[]),body=ipDed(body,extendOpTabWithBindings(ot,bindings)),pos=pos})

        | ipDed(A.beginDed({members,pos}),ot) = A.beginDed({members=map (fn d => ipDed(d,ot)) members,pos=pos})
        | ipDed(A.checkDed({clauses,pos}),ot) = A.checkDed({clauses=map (fn c => ipDCheckClause(c,ot)) clauses,pos=pos})
        | ipDed(A.byCasesDed({disj,from_exps=NONE,arms,pos}),ot) = 
                A.byCasesDed({disj=ipPhrase(disj,ot),from_exps=NONE,arms=map (fn c => ipCaseClause(c,ot)) arms,pos=pos})
        | ipDed(A.byDed({wanted_res,conc_name,body,pos}),ot) = 
                A.byDed({wanted_res=ipExp(wanted_res,ot),conc_name=conc_name,body=ipDed(body,ot),pos=pos})
        | ipDed(A.fromDed({conclusion,premises,pos}),ot) = 
                A.fromDed({conclusion=ipExp(conclusion,ot),premises=ipExp(premises,ot),pos=pos})
        | ipDed(A.byCasesDed({disj,from_exps=SOME(exps),arms,pos}),ot) = 
                A.byCasesDed({disj=ipPhrase(disj,ot),from_exps=SOME(map (fn e => ipExp(e,ot)) exps),
                              arms=map (fn c => ipCaseClause(c,ot)) arms,pos=pos})
        | ipDed(A.genOverDed({eigenvar_exp,body,pos}),ot) = 
                A.genOverDed({eigenvar_exp=ipExp(eigenvar_exp,ot),body=ipDed(body,ot),pos=pos})
        | ipDed(A.pickAnyDed({eigenvars,body,pos}),ot) = 
                A.pickAnyDed({eigenvars=eigenvars,body=ipDed(body,ot),pos=pos})
        | ipDed(A.withWitnessDed({eigenvar_exp,ex_gen,body,pos}),ot) = 
                A.withWitnessDed({eigenvar_exp=ipExp(eigenvar_exp,ot),ex_gen=ipPhrase(ex_gen,ot),body=ipDed(body,ot),pos=pos})
        | ipDed(A.pickWitnessDed({ex_gen,var_id,inst_id,body,pos}),ot) = 
                A.pickWitnessDed({ex_gen=ipPhrase(ex_gen,ot),var_id=var_id,inst_id=inst_id,body=ipDed(body,ot),pos=pos})
        | ipDed(A.pickWitnessesDed({ex_gen,var_ids,inst_id,body,pos}),ot) = 
                A.pickWitnessesDed({ex_gen=ipPhrase(ex_gen,ot),var_ids=var_ids,inst_id=inst_id,body=ipDed(body,ot),pos=pos})
      and ipPhrase(A.exp(e),op_table) = A.exp(ipExp(e,op_table))
        | ipPhrase(A.ded(d),op_table) = A.ded(ipDed(d,op_table))
      and ipCaseClause({case_name,alt,proof},ot) = {case_name=case_name,alt=ipExp(alt,ot),proof=ipDed(proof,ot)}
      and ipMatchClause({pat=p,exp=e},ot) = {pat=ipPat(p,ot),exp=ipExp(e,MS.augment(ot,A.mpatOps(p)))}
      and ipDMatchClause({pat=p,ded=d},ot) = {pat=ipPat(p,ot),ded=ipDed(d,MS.augment(ot,A.mpatOps(p)))}
      and extendOpTabWithParams(ot,[]) = ot
        | extendOpTabWithParams(ot,(A.someParam({name,op_tag as NONE,...}))::more) = 
              extendOpTabWithParams(MS.enter(ot,A.msym name,no_op_val),more)
        | extendOpTabWithParams(ot,(A.someParam({name,op_tag as SOME(i,j),...}))::more) = 
              extendOpTabWithParams(MS.enter(ot,A.msym name,(i,j)),more)
        | extendOpTabWithParams(ot,_::more) = extendOpTabWithParams(ot,more)
      and ipBindings([],_,res) = rev res
        | ipBindings((binding as {bpat,def,pos})::more,ot,res) = 
           let val b = {bpat=ipPat(bpat,ot),def=ipPhrase(def,ot),pos=pos}
           in
              ipBindings(more,MS.augment(ot,A.mpatOps(bpat)),b::res)
           end
      and extendOpTabWithBindings(ot,[]) = ot
        | extendOpTabWithBindings(ot,(binding as {bpat,def,pos})::more) =
           extendOpTabWithBindings(MS.augment(ot,A.mpatOps(bpat)),more)
      and ipPat(wp as A.wherePat({pat,guard,pos}),ot) = 
                 A.wherePat({pat=ipPat(pat,ot),guard=ipExp(guard,ot),pos=pos})
        | ipPat(A.listPats({member_pats,pos}),ot) = A.listPats({member_pats=(map (fn p => ipPat(p,ot)) member_pats),pos=pos})
        | ipPat(A.listPat({head_pat,tail_pat,pos}),ot) = A.listPat({head_pat=ipPat(head_pat,ot),tail_pat=ipPat(tail_pat,ot),pos=pos})
        | ipPat(A.cellPat({pat,pos}),ot) = A.cellPat({pat=ipPat(pat,ot),pos=pos})


        | ipPat(A.splitPat({pats,pos,re_form,code}),ot) = 
             A.splitPat({pats=(map (fn p => ipPat(p,ot)) pats),code=code,pos=pos,re_form=A.applyToRE(fn e => ipExpFinal(e,ot),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPat(A.reStarPat({pat,pos,re_form,code}),ot) = 
	     let val re_form' = A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form) 
             in
                A.reStarPat({pat=ipPat(pat,ot),code=code,pos=pos,re_form=re_form'})
             end 
        | ipPat(A.rePlusPat({pat,pos,re_form,code}),ot) = 
             A.rePlusPat({pat=ipPat(pat,ot),pos=pos,code=code,re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPat(A.reRangePat({from_pat,to_pat,lo,hi,pos}),ot) = 
             A.reRangePat({from_pat=ipPat(from_pat,ot),to_pat=ipPat(to_pat,ot),lo=lo,hi=hi,pos=pos})

        | ipPat(A.reOptPat({pat,pos,re_form,code}),ot) = 
             A.reOptPat({pat=ipPat(pat,ot),pos=pos,code=code,re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPat(A.reRepPat({pat,times,pos,code,re_form}),ot) = 
             A.reRepPat({pat=ipPat(pat,ot),pos=pos,code=code,times=times,
                         re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPat(A.namedPat({name,pat,pos}),ot) = A.namedPat({name=name,pat=ipPat(pat,ot),pos=pos})
        | ipPat(A.compoundPat({head_pat,rest_pats,pos}),ot) = A.compoundPat({head_pat=ipPat(head_pat,ot),rest_pats=(map (fn p => ipPat(p,ot)) rest_pats),pos=pos})
        | ipPat(A.disjPat({pats,pos}),ot) = A.disjPat({pats=(map (fn p => ipPat(p,ot)) pats),pos=pos})
        | ipPat(p,_) = p 
      and ipPatFinal(wp as A.wherePat({pat,guard,pos}),ot) = 
              let val _ = print("\nWorking-FINAL on this where pat: " ^ (AbstractSyntax.printPat wp))
              in
                 A.wherePat({pat=ipPatFinal(pat,ot),guard=ipExpFinal(guard,ot),pos=pos})
              end
        | ipPatFinal(A.listPats({member_pats,pos}),ot) = A.listPats({member_pats=(map (fn p => ipPatFinal(p,ot)) member_pats),pos=pos})
        | ipPatFinal(A.listPat({head_pat,tail_pat,pos}),ot) = A.listPat({head_pat=ipPatFinal(head_pat,ot),tail_pat=ipPatFinal(tail_pat,ot),pos=pos})
        | ipPatFinal(A.cellPat({pat,pos}),ot) = A.cellPat({pat=ipPatFinal(pat,ot),pos=pos})
        | ipPatFinal(A.splitPat({pats,pos,code,re_form}),ot) = 
             A.splitPat({pats=(map (fn p => ipPatFinal(p,ot)) pats),pos=pos,code=code,re_form=A.applyToRE(fn e => ipExpFinal(e,ot),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPatFinal(A.reStarPat({pat,code,pos,re_form}),ot) = 
             A.reStarPat({pat=ipPatFinal(pat,ot),code=code,pos=pos,re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPatFinal(A.rePlusPat({pat,pos,code,re_form}),ot) = 
             A.rePlusPat({pat=ipPatFinal(pat,ot),pos=pos,code=code,re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPatFinal(A.reRangePat({from_pat,to_pat,lo,hi,pos}),ot) = 
             A.reRangePat({from_pat=ipPatFinal(from_pat,ot),to_pat=ipPatFinal(to_pat,ot),lo=lo,hi=hi,pos=pos})

        | ipPatFinal(A.reOptPat({pat,pos,code,re_form}),ot) = 
             A.reOptPat({pat=ipPatFinal(pat,ot),code=code,pos=pos,re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPatFinal(A.reRepPat({pat,times,pos,code,re_form}),ot) = 
             A.reRepPat({pat=ipPatFinal(pat,ot),times=times,pos=pos,code=code,re_form=A.applyToRE((fn e => ipExpFinal(e,ot)),(fn p => ipPatFinal(p,ot)),re_form)})

        | ipPatFinal(A.namedPat({name,pat,pos}),ot) = A.namedPat({name=name,pat=ipPatFinal(pat,ot),pos=pos})
        | ipPatFinal(A.compoundPat({head_pat,rest_pats,pos}),ot) = A.compoundPat({head_pat=ipPatFinal(head_pat,ot),rest_pats=(map (fn p => ipPatFinal(p,ot)) rest_pats),pos=pos})
        | ipPatFinal(A.disjPat({pats,pos}),ot) = A.disjPat({pats=(map (fn p => ipPatFinal(p,ot)) pats),pos=pos})
        | ipPatFinal(p,_) = p 
      and ipExpFinal(e,ot) = A.phraseToExp(A.splitApps(A.exp(ipExp(e,ot))))
      and ipFinal(p) =      
              let val p':A.phrase = if !Options.infix_parsing_option then ipPhrase(p,MS.empty_mapping) else p 
                  val res = A.splitApps(p')  
              in
                 res
              end
  in
     ipFinal(p)
  end

fun processPhraseAndReturn(p,eval_env,fids) = 
              let val ip = infixProcess(p,top_val_env,fids) 
                  val v = evalPhrase((ip,fids),eval_env,!top_assum_base) 
              in
                v 
              end

val default_ufv_pa_for_procs = SemanticValues.default_ufv_pa_for_procs
val default_bfv_pa_for_procs = SemanticValues.default_bfv_pa_for_procs

local
open Semantics
in
fun processPhraseFromStringFun([v],env:SemanticValues.value_environment ref,_) = 
           (case Semantics.isStringValConstructive(v) of
               SOME(str) => let val stream = TextIO.openString (str)
                                val input  = hd(Parse.parse_from_stream(stream))
                                val res_val = (case input of
                                                  A.phraseInput(p) => let val mod_path = (case (!Paths.open_mod_paths) of
                                                                                             [] => []
                                                                                           | mp::_ => mp)
                                                                          val (new_phrase,vars,fids) = SV.preProcessPhrase(p,mod_path)
                                                                          val (vmap,mmap) = getValAndModMaps(!env)
                                                                          val env' = ref(augmentWithBothMaps(!top_val_env,mmap,vmap))

									  val _ = if (false andalso !Options.fundef_mlstyle_option) then
									           print("\nGiven env in which to evaluate " ^ str ^ "\nIS THIS:[[[[[[[[[[[\n" ^ 
										        SV.envToString(!env) ^ "\n]]]]]]]]]]]\n")
									          else ()
 							                  val _ = if (false andalso !Options.fundef_mlstyle_option) then
									          print("\nAnd here's the TOP_VAL_ENV:[[[[[[[[\n" 
									          ^ SV.envToString(!top_val_env) ^ "\n]]]]]]]]\n")
										  else ()
 							                  val _ = if (false andalso !Options.fundef_mlstyle_option) then
									          print("\nAnd here's the EXTENDED environment, env';:[[[[[[[[\n" 
									          ^ SV.envToString(!env') ^ "\n]]]]]]]]\n")
										  else ()
                                                                      in processPhraseAndReturn(new_phrase,env',fids) end
                                                | _ => primError("Incorrect application of "^(Names.evalFun_name)^".\nOnly phrases can be evaluated."))
                            in 
                               res_val
                            end
             | _ => primError(wrongArgKind(Names.evalFun_name,1,stringLCType,v)))
  | processPhraseFromStringFun(vals,_,_) = primError(wrongArgNumber(N.evalFun_name,length(vals),1))

fun processInputFromStringFun([v],env,_) = 
           (case Semantics.isStringValConstructive(v) of
               SOME(str) => let val doString = !processString
                                val _ = doString(str,(!Paths.current_mod_path),ref(!env),env)
                            in unitVal end
             | _ => primError(wrongArgKind(Names.processInputFun_name,1,stringLCType,v)))

(** Pass the value "true" as a second argument to process-input-from-string to silence the processing. **)

  | processInputFromStringFun([v,v'],env,_) = 
      let val silent_val = !Options.silent_mode
          val _ = (case Semantics.isStringValConstructive(v) of
                     SOME(str) => let val _ = (case coerceValIntoTerm(v') of
                                                 SOME(t) => if AthTerm.termEq(t,true_term) then Options.silent_mode := true else ()
                                                | _ => ())
                                      val doString = !processString
                                      val _ = doString(str,[],ref(!env),env)
                                  in 
                                     ()
                                  end
                   | _ => primError(wrongArgKind(Names.processInputFun_name,1,stringLCType,v))) 
         val _ = Options.silent_mode := silent_val
       in
          unitVal          
       end
  | processInputFromStringFun(vals,_,_) = primError(wrongArgNumber(N.processInputFun_name,length(vals),1))

end

val (athena_home_option,athena_home) = (Paths.athena_home_option,Paths.athena_home)

val init_val_bindings_ref: (symbol * value) list ref = ref([])

val restartAthena_ref = (ref (fn () => ()))

fun restartAthenaFun([],_,_) = (((!restartAthena_ref)());unitVal)
  | restartAthenaFun(vals,_,_) = primError(wrongArgNumber("restart-athena",length(vals),0))

exception unCoveredTerm of AT.term

local open SV in 

val isPrimFSym = 
let val ht = MS.makeHTableWithInitialSize(37)
    val _ = MS.insert(ht,N.mequal_logical_symbol,primBFunVal(valEqPrimBFun,default_bfv_pa_for_procs N.eq_name))
    val _ = MS.insert(ht,N.mformal_less_symbol,primBFunVal(lessPrimBFun,default_bfv_pa_for_procs N.lessFun_name))
    val _ = MS.insert(ht,N.mformal_greater_symbol,primBFunVal(greaterPrimBFun,default_bfv_pa_for_procs N.greaterFun_name))
    val _ = MS.insert(ht,N.mformal_leq_symbol,primBFunVal(leqPrimBFun,default_bfv_pa_for_procs "leq?"))
    val _ = MS.insert(ht,N.mformal_geq_symbol,primBFunVal(geqPrimBFun,default_bfv_pa_for_procs "geq?"))
    val _ = MS.insert(ht,N.maddition_symbol,primBFunVal(plusPrimBFun,default_bfv_pa_for_procs N.plusFun_name))
    val _ = MS.insert(ht,N.msubtraction_symbol,primBFunVal(minusPrimBFun,default_bfv_pa_for_procs N.minusFun_name))
    val _ = MS.insert(ht,N.mmultiplication_symbol,primBFunVal(timesPrimBFun,default_bfv_pa_for_procs N.timesFun_name))
    val _ = MS.insert(ht,N.mdivision_symbol,primBFunVal(divPrimBFun,default_bfv_pa_for_procs N.divFun_name))
    val _ = MS.insert(ht,N.mmodulo_symbol,primBFunVal(modPrimBFun,default_bfv_pa_for_procs N.modFun_name))
  in
    fn fsym => MS.find(ht,fsym)
  end

fun evalPropCanonical(p,request) = 
  let val ab = (!(ABase.top_assum_base))
      val env = top_val_env
      val mAnd_code = MS.code(N.mAnd_symbol)
      val mOr_code = MS.code(N.mOr_symbol)
      val mIf_code = MS.code(N.mIf_symbol)
      val mIff_code = MS.code(N.mIff_symbol)
      val mNot_code = MS.code(N.mNot_symbol)
      val mite_code = MS.code(N.mite_symbol)
      val ht : (AT.term,AT.term) HashTable.hash_table = HashTable.mkTable(AT.hashTerm, AT.termEq) (251,Basic.Never)
      fun addIdentity(p) = (case Prop.isEquality(p) of
                                SOME(t1,t2) => (HashTable.insert ht (t1,t2)))
      val _ = List.app addIdentity (Prop.getConjuncts request)
      fun doTerm(t) = 
             (case AT.isApp(t) of
                SOME(fsym,args) => (case isPrimFSym(fsym) of
                                       SOME(primBFunVal(f,_)) => 
                                             let val a1 = doTerm(hd(args))
                                                 val a2 = doTerm(hd(tl(args)))
                                             in
                                                f(a1,a2,env,ab)
                                             end
                                     | SOME(funVal(f,_,_)) => f(map doTerm args,env,ab)
                                     | _ => if null(args) then  termVal(t)
                                            else (case getBoolFun(MS.code(fsym)) of
                                                     SOME(f) => f(args)
                                                   | _ => (case (HashTable.find ht t) of
                                                             SOME(t') => termVal(t')
                                                           | _ => raise unCoveredTerm(t))))
              | _ => (case AT.isNumConstantOpt(t) of
                         SOME(_) => termVal(t)
                       | _ => (case AT.isIdeConstant(t) of
                                 SOME(_) => termVal(t)
                               | _ => raise unCoveredTerm(t))))
    and doProp(p) =
       (case Prop.isAtom(p) of
            SOME(t) => doTerm(t)
          | _ => (case Prop.isConj(p) of
                     SOME(props) => doAndProps(props)
                    | _ => (case Prop.isDisj(p) of
                              SOME(props) => doOrProps(props)
                            | _ => (case Prop.isNeg(p) of
                                       SOME(q) => (case doProp(q) of
                                                     termVal(t) => if AT.isFalseTerm(t) then true_val else false_val)
                                     | _ => (case Prop.isCond(p) of
                                                 SOME(p1,p2) => doIfProps([p1,p2])
                                               | _ => (case Prop.isBiCond(p) of
                                                          SOME(p1,p2) => doAndProps([Prop.makeConditional(p1,p2),Prop.makeConditional(p2,p1)])
                                                        | _ => (print("\nHERE NOW!!!!\n");raise Basic.Never)))))))
    and doAndProps([]) = true_val
      | doAndProps(p::more) = (case doProp(p) of
                                  termVal(t) => if AT.isFalseTerm(t) then false_val else doAndProps(more))
    and doOrProps([]) = false_val
      | doOrProps(p::more) = (case doProp(p) of
                                termVal(t) => if AT.isTrueTerm(t) then true_val else doOrProps(more))
    and doIfProps([]) = false_val
      | doIfProps(p::more) = (case doProp(p) of
                                termVal(t) => if AT.isFalseTerm(t) then true_val else doOrProps(more))
    and doIteTerms([t1,t2,t3]) = (case doTerm(t1) of
                                     termVal(t) => if AT.isTrueTerm(t) then doTerm(t2) else doTerm(t3))
    and doNotTerms([t]) = (case doTerm(t) of
                              termVal(t') => if AT.isFalseTerm(t') then true_val else false_val)
    and doAndTerms([t1,t2]) = (case doTerm(t1) of
                                  termVal(t) => if AT.isFalseTerm(t) then false_val else doTerm(t2))
    and doOrTerms([t1,t2]) = (case doTerm(t1) of
                                termVal(t) => if AT.isTrueTerm(t) then true_val else doTerm(t2))
    and doIfTerms([t1,t2]) = (case doTerm(t1) of 
                                 termVal(t) => if AT.isFalseTerm(t) then true_val else doTerm(t2))
    and doIffTerms([t1,t2]) = (case doIfTerms([t1,t2]) of
                                 termVal(t) => if AT.isTrueTerm(t) then doIfTerms([t2,t1]) else false_val)
    and getBoolFun(code) = if code = mite_code then SOME(doIteTerms) else
                           if code = mAnd_code then SOME(doAndTerms) else if code = mOr_code then SOME(doOrTerms) 
                           else if code = mNot_code then SOME(doNotTerms) else if code = mIf_code then SOME(doIfTerms)                
                           else if code = mIff_code then SOME(doIffTerms) else NONE
  in
    doProp(p)
  end
             
end

fun evalPropCanonicalPrimBFun(v1,v2,env,_) = 
       (case coerceValIntoProp(v1) of
          SOME(p) => (case coerceValIntoProp(v2) of
                        SOME(request) => ((evalPropCanonical(p,request)) 
                                             handle unCoveredTerm(t) => (print("\nCanonical evaluation error: the following term\n"^
                                                                               "is not covered by the given request: " ^ (AT.toStringDefault(t)) ^"\n");unitVal))));

val init_val_bindings = [(N.not_symbol,propConVal(A.notCon)),(N.and_symbol,propConVal(A.andCon)),
                         (N.lookUpEnvBindingFun_symbol,funVal(lookUpEnvBindingFun,N.lookUpEnvBindingFun_name,default_fv_pa_for_procs 1)),
			 (Symbol.symbol("excl-constructors"),
			  primBFunVal(constructorExclPrimBFun,default_bfv_pa_for_procs "excl-constructors")),
			 (Symbol.symbol("make-spass-prop-string"),
			  funVal(makeSpassPropStringFun,"make-spass-prop-string",default_fv_pa_for_procs 1)),
			 (Symbol.symbol("make-server"),
			  funVal(Server.makeServerFun,"make-server",default_fv_pa_for_procs 2)),
			 (Symbol.symbol("make-poly-spass-term-string"),
			  funVal(makePolySpassTermStringFun,"make-poly-spass-term-string",default_fv_pa_for_procs 1)),
			 (Symbol.symbol("make-poly-spass-prop-string"),
			  funVal(makePolySpassPropStringFun,"make-poly-spass-prop-string",default_fv_pa_for_procs 1)),
			 (Symbol.symbol("make-e-prop-string"),
			  funVal(makeEPropStringFun,"make-e-prop-string",default_fv_pa_for_procs 1)),
                         (N.spfPrimMethod_symbol,methodVal(spassProvePrimMethod,N.spfPrimMethod_symbol)),
                         (N.uspfPrimMethod_symbol,methodVal(unLimSpassProvePrimMethod,N.uspfPrimMethod_symbol)),
                         (N.vpfPrimMethod_symbol,methodVal(polyVampireProvePrimMethod,N.vpfPrimMethod_symbol)),
                         (N.mvpfPrimMethod_symbol,methodVal(monoVampireProvePrimMethod,N.mvpfPrimMethod_symbol)),
                         (N.epfPrimMethod_symbol,methodVal(EProvePrimMethod,N.epfPrimMethod_symbol)),
                         (N.uvpfPrimMethod_symbol,methodVal(unLimVampireProvePrimMethod,N.uvpfPrimMethod_symbol)),
                         (N.paradoxPrimFun_symbol,funVal(paradoxProvePrimFun,N.paradoxPrimFun_name,default_fv_pa_for_procs 1)),
                         (N.getMultisortedModelPrimFun_symbol,funVal(getMultisortedModelPrimFun,
								     N.getMultisortedModelPrimFun_name,default_fv_pa_for_procs 3)),    
                         (N.or_symbol,propConVal(A.orCon)),(N.if_symbol,propConVal(A.ifCon)),
                         (N.iff_symbol,propConVal(A.iffCon)),(N.forall_symbol,propConVal(A.forallCon)),
                         (N.exists_symbol,propConVal(A.existsCon)),
                         (N.exists_unique_symbol,propConVal(A.existsUniqueCon)), 
                         (N.equal_logical_symbol,termConVal(regFSym(declared(StructureAnalysis.equality_symbol)))),
                         (N.consFun_symbol,primBFunVal(consPrimBFun,default_bfv_pa_for_procs N.consFun_name)),
                         (N.allFunSymsFun_symbol,funVal(getAllFSymsFun,N.allFunSymsFun_name,default_fv_pa_for_procs 0)),
                         (N.carFun_symbol,primUFunVal(carPrimUFun,default_ufv_pa_for_procs N.carFun_name)),
                         (N.cdrFun_symbol,primUFunVal(cdrPrimUFun,default_ufv_pa_for_procs N.cdrFun_name)),
                         (N.getSymDef_symbol,primUFunVal(getSymDefPrimUFun,default_ufv_pa_for_procs N.getSymDef_name)),
	                 (N.holdsFun_symbol,primUFunVal(holdsPrimUFun,default_ufv_pa_for_procs N.holdsFun_name)),
	                 (N.dependenciesFun_symbol,primUFunVal(dependenciesPrimUFun,default_ufv_pa_for_procs N.dependenciesFun_name)),
	                 (N.dependenciesTranFun_symbol,primUFunVal(dependenciesTranPrimUFun,default_ufv_pa_for_procs N.dependenciesTranFun_name)),
	                 (N.sortVarsFun_symbol,primUFunVal(sortVarsPrimUFun,default_ufv_pa_for_procs N.sortVarsFun_name)),
	                 (N.monoInstanceFun_symbol,primUFunVal(makeMonomorphicInstancePrimUFun,default_ufv_pa_for_procs N.monoInstanceFun_name)),
	                 (N.symCodeFun_symbol,primUFunVal(symCodePrimUFun,default_ufv_pa_for_procs N.symCodeFun_name)),
	                 (N.fetchFun_symbol,primUFunVal(fetchPrimUFun,default_ufv_pa_for_procs N.fetchFun_name)),
	                 (N.fetchAllFun_symbol,primUFunVal(fetchAllPrimUFun,default_ufv_pa_for_procs N.fetchAllFun_name)),
	                 (N.freshSymbolFun_symbol,primBFunVal(makeFreshSymbolsPrimBFun,default_bfv_pa_for_procs N.freshSymbolFun_name)),
                         (N.fresh_var_symbol,funVal(freshVarFun,N.fresh_var_name,default_fv_pa_for_procs 0)),
                         (S.symbol("show-tccs"),funVal(showTCCsFun,"show-tccs",default_fv_pa_for_procs 0)),
                         (S.symbol("clear-tccs"),funVal(clearTCCsFun,"clear-tccs",default_fv_pa_for_procs 0)),
                         (S.symbol("restart-athena"),funVal(restartAthenaFun,"restart-athena",default_fv_pa_for_procs 0)),
                         (N.catchFun_symbol,primBFunVal(catchPrimBFun,default_bfv_pa_for_procs N.catchFun_name)),
                         (N.catchMethod_symbol,primBMethodVal(catchPrimBMethod,N.catchMethod_symbol)),
                         (Symbol.symbol("lub"),primBFunVal(lubPrimBFun,default_bfv_pa_for_procs "lub")),
                         (Symbol.symbol("glb"),primBFunVal(glbPrimBFun,default_bfv_pa_for_procs "glb")),
                         (Symbol.symbol("prop-count"),funVal(propCountFun,"prop-count",default_fv_pa_for_procs 0)),
                         (Symbol.symbol("look-ups"),funVal(lookupCountFun,"look-ups",default_fv_pa_for_procs 0)),
                         (N.makePathFun_symbol,primBFunVal(makePathPrimBFun,default_bfv_pa_for_procs N.makePathFun_name)),
                         (Symbol.symbol("insertions"),funVal(insertCountFun,"insertions",default_fv_pa_for_procs 0)),
                         (S.symbol("poly?"),primUFunVal(isPolyPrimUFun,default_ufv_pa_for_procs "poly?")),
                         (S.symbol("has-vars?"),primUFunVal(hasVarsPrimUFun,default_ufv_pa_for_procs "has-vars?")),
                         (N.valToString_symbol,primUFunVal(valToStringPrimUFun,default_ufv_pa_for_procs N.valToString_name)),
                         (N.valToStringUnlim_symbol,primUFunVal(valToStringUnlimPrimUFun,default_ufv_pa_for_procs N.valToStringUnlim_name)),
                         (N.valToString_symbol',primUFunVal(valToStringPrimUFun',default_ufv_pa_for_procs N.valToString_name')),
                         (N.write_symbol,primUFunVal(writePrimUFun,default_ufv_pa_for_procs N.write_name)),
                         (N.writeVal_symbol,primUFunVal(writeValPrimUFun,default_ufv_pa_for_procs N.writeVal_name)),
                         (N.transOntologyFun_symbol,primUFunVal(translateOntologyPrimUFun,default_ufv_pa_for_procs N.transOntologyFun_name)),
                         (N.print_symbol,funVal(printFun,N.print_name,default_fv_pa_for_procs 1001)),
                         (N.isPrintableFun_symbol,primUFunVal(isPrintablePrimUFun,default_ufv_pa_for_procs(N.isPrintableFun_name))),
                         (N.readOneChar_symbol,funVal(readOneCharFun,N.readOneChar_name,default_fv_pa_for_procs 0)),
                         (N.readFile_symbol,primUFunVal(readFilePrimUFun,default_ufv_pa_for_procs N.readFile_name)),
                         (N.readFileLines_symbol,primUFunVal(readFileLinesPrimUFun,default_ufv_pa_for_procs N.readFileLines_name)),
                         (N.writeFile_symbol,primBFunVal(writeFilePrimBFun,default_bfv_pa_for_procs N.writeFile_name)),
                         (N.varToStringFun_symbol,primUFunVal(varToStringPrimUFun,default_ufv_pa_for_procs N.varToStringFun_name)),
                         (N.compareCharsFun_symbol,primBFunVal(compareCharsPrimBFun,default_bfv_pa_for_procs N.compareCharsFun_name)),
                         (N.compareStringsFun_symbol,primBFunVal(compareStringsPrimBFun,default_bfv_pa_for_procs N.compareStringsFun_name)),
                         (N.charOrdFun_symbol,primUFunVal(charOrdPrimUFun,default_ufv_pa_for_procs N.charOrdFun_name)),
                         (N.makeCharFun_symbol,primUFunVal(makeCharPrimUFun,default_ufv_pa_for_procs N.makeCharFun_name)),
                         (N.metaIdToStringFun_symbol,primUFunVal(metaIdToStringPrimUFun,default_ufv_pa_for_procs N.metaIdToStringFun_name)),
                         (N.plusFun_symbol,SV.primBFunVal(plusPrimBFun,default_bfv_pa_for_procs N.plusFun_name)),
                         (N.sqrtFun_symbol,SV.primUFunVal(sqrtPrimUFun,default_ufv_pa_for_procs N.sqrtFun_name)),
                         (N.log10Fun_symbol,SV.primUFunVal(log10PrimUFun,default_ufv_pa_for_procs N.log10Fun_name)),
                         (N.lnFun_symbol,SV.primUFunVal(lnPrimUFun,default_ufv_pa_for_procs N.lnFun_name)),
                         (Symbol.symbol "prim-plus",SV.primBFunVal(PrimPlusFun,{name="prim-plus",prec=ref(Options.defaultPrec(2)),assoc=ref(NONE)})),
                         (N.lessFun_symbol,primBFunVal(lessPrimBFun,default_bfv_pa_for_procs N.lessFun_name)),
                         (Names.greaterFun_symbol,SV.primBFunVal(greaterPrimBFun,default_bfv_pa_for_procs N.greaterFun_name)),
                         (Symbol.symbol "prim-greater?",SV.primBFunVal(PrimGreaterFun,{name="prim-greater?",prec=ref(Options.defaultPrec(2)),assoc=ref(NONE)})),
                         (N.numEqualFun_symbol,primBFunVal(numEqualPrimBFun,default_bfv_pa_for_procs N.numEqualFun_name)),
                         (N.timesFun_symbol,primBFunVal(timesPrimBFun,default_bfv_pa_for_procs N.timesFun_name)),
                         (N.divFun_symbol,primBFunVal(divPrimBFun,default_bfv_pa_for_procs N.divFun_name)),
                         (N.modFun_symbol,primBFunVal(modPrimBFun,default_bfv_pa_for_procs N.modFun_name)),
                         (N.fresh_var_symbol,funVal(freshVarFun,N.fresh_var_name,default_fv_pa_for_procs 0)),
                         (N.stringToVarFun_symbol,funVal(stringToVarFun,N.stringToVarFun_name,default_fv_pa_for_procs 1)),
                         (N.stringToMetaIdFun_symbol,primUFunVal(stringToMetaIdPrimUFun,default_ufv_pa_for_procs N.stringToMetaIdFun_name)),
                         (N.symbolToStringFun_symbol,primUFunVal(symbolToStringPrimUFun,default_ufv_pa_for_procs N.symbolToStringFun_name)),
                         (N.getSigFun_symbol,primUFunVal(getSigPrimUFun,default_ufv_pa_for_procs N.getSigFun_name)),
                         (S.symbol("get-signature-unified"),primBFunVal(getSigUnifiedPrimBFun,default_bfv_pa_for_procs "get-signature-unified")),
                         (N.stringToNumFun_symbol,primUFunVal(stringToNumPrimUFun,default_ufv_pa_for_procs N.stringToNumFun_name)),
                         (N.stringToSymbolFun_symbol,primUFunVal(stringToSymbolPrimUFun,default_ufv_pa_for_procs N.stringToSymbolFun_name)),
                         (N.execCommandFun_symbol,primUFunVal(execCommandPrimUFun,default_ufv_pa_for_procs N.execCommandFun_name)),
                         (N.deleteFileFun_symbol,primUFunVal(deleteFilePrimUFun,default_ufv_pa_for_procs N.deleteFileFun_name)),
                         (N.deleteFile1Fun_symbol,primUFunVal(deleteFile1PrimUFun,default_ufv_pa_for_procs N.deleteFile1Fun_name)),
                         (N.nullFun_symbol,primUFunVal(isNullPrimUFun,default_ufv_pa_for_procs N.nullFun_name)),
                         (N.funSymFun_symbol,funVal(funSymFun,N.funSymFun_name,default_fv_pa_for_procs 1)),
                         (N.revFun_symbol,primUFunVal(reversePrimUFun,default_ufv_pa_for_procs N.revFun_name)),
                         (naive_rev_sym,primUFunVal(naiveRevPrimUFun,default_ufv_pa_for_procs "naive-rev")),
                         (Symbol.symbol("naive-rev2"),primUFunVal(naiveRevPrimUFun2,default_ufv_pa_for_procs "naive-rev2")),
                         (Symbol.symbol("naive-rev3"),primUFunVal(naiveRevPrimUFun3,default_ufv_pa_for_procs "naive-rev3")),
                         (Symbol.symbol("cappend"),primBFunVal(naiveAppendPrimBFun,default_bfv_pa_for_procs "cappend")),
                         (Symbol.symbol "prim-rev",primUFunVal(reversePrimUFun,{name="rev",prec=ref(Options.defaultPrec(1))})),
                         (N.eq_symbol,primBFunVal(valEqPrimBFun,default_bfv_pa_for_procs N.eq_name)),
                         (N.struc_eq_symbol,primBFunVal(strucValEqPrimBFun,default_bfv_pa_for_procs N.struc_eq_name)),
                         (N.empty_sub_symbol,subVal(AthTerm.empty_sub)),
                         (N.extendSubFun_symbol,funVal(extendSubFun,N.extendSubFun_name,default_fv_pa_for_procs 2)),
                         (N.suppFun_symbol,primUFunVal(suppPrimUFun,default_ufv_pa_for_procs N.suppFun_name)),
                         (N.ranVarFun_symbol,primUFunVal(ranVarPrimUFun,default_ufv_pa_for_procs N.ranVarFun_name)),
                         (N.random_int_symbol,primUFunVal(randomIntPrimUFun,default_ufv_pa_for_procs N.random_int_name)),
                         (S.symbol("write-into-vec"),funVal(wivFun,"write-into-vec",default_fv_pa_for_procs 3)),
                         (N.subComposeFun_symbol,primBFunVal(subComposePrimBFun,default_bfv_pa_for_procs N.subComposeFun_name)),
                         (N.unifyFun_symbol,funVal(unifyFun,N.unifyFun_name,default_fv_pa_for_procs 2)),
                         (N.matchFun_symbol,funVal(matchFun,N.matchFun_name,default_fv_pa_for_procs 2)),
                         (N.isSortInstanceFun_symbol,primBFunVal(isSortInstancePrimBFun,default_bfv_pa_for_procs N.isSortInstanceFun_name)),
                         (N.matchPropsFun_symbol,primBFunVal(matchPropsPrimBFun,default_bfv_pa_for_procs N.matchPropsFun_name)),
                         (N.renameSortVarsFun_symbol,primUFunVal(renameSortVarsPrimUFun,
						               default_ufv_pa_for_procs N.renameSortVarsFun_name)),
                         (N.renameSortVarsLstFun_symbol,primUFunVal(renameSortVarsLstPrimUFun,
						               default_ufv_pa_for_procs N.renameSortVarsLstFun_name)),
                         (N.matchProps3Fun_symbol,funVal(matchProps3Fun,N.matchProps3Fun_name,default_fv_pa_for_procs 3)),
                         (N.rewriteSearchFun_symbol,funVal(rewriteSearchFun,N.rewriteSearchFun_name,default_fv_pa_for_procs 6)),
                         (N.getRewritesFun_symbol,primBFunVal(getRewritesPrimBFun,default_bfv_pa_for_procs N.getRewritesFun_name)),
                         (N.getSelectorsFun_symbol,primUFunVal(getSelectorsPrimUFun,default_ufv_pa_for_procs N.getSelectorsFun_name)),
                         (N.sort_of_symbol,primUFunVal(sortOfPrimUFun,default_ufv_pa_for_procs N.sort_of_name)),
                         (N.sort_of_var_in_term_symbol,primBFunVal(sortOfVarInTermPrimBFun,default_bfv_pa_for_procs N.sort_of_var_in_term_name)),
                         (N.sort_of_var_in_prop_symbol,primBFunVal(sortOfVarInPropPrimBFun,default_bfv_pa_for_procs N.sort_of_var_in_prop_name)),
                         (N.propFun_symbol,primUFunVal(propPrimUFun,default_ufv_pa_for_procs N.propFun_name)),
                         (N.is_atom_symbol,primUFunVal(isAtomPrimUFun,default_ufv_pa_for_procs N.is_atom_name)),
                         (N.makeAthenaListFun_symbol,funVal(makeAthenaListFun,N.makeAthenaListFun_name,default_fv_pa_for_procs 1001)),
                         (N.replaceVar_symbol,funVal(replaceVarFun,N.replaceVar_name,default_fv_pa_for_procs 3)),
                         (N.timeFun_symbol,funVal(timeFun,N.timeFun_name,default_fv_pa_for_procs 0)),
                         (N.renameFun_symbol,primUFunVal(renamePrimUFun,default_ufv_pa_for_procs N.renameFun_name)),
                         (N.sizeFun_symbol,primUFunVal(sizePrimUFun,default_ufv_pa_for_procs N.sizeFun_name)),
                         (N.alEqFun_symbol,primBFunVal(alphaEquivPrimBFun,default_bfv_pa_for_procs N.alEqFun_name)),
                         (N.root_symbol,primUFunVal(rootPrimUFun,default_ufv_pa_for_procs N.root_name)),     
                         (N.getPrecedence_symbol,primUFunVal(precedenceOfPrimUFun,default_ufv_pa_for_procs N.getPrecedence_name)),
                         (N.getAssoc_symbol,primUFunVal(assocOfPrimUFun,default_ufv_pa_for_procs N.getAssoc_name)),
                         (N.arityOf_symbol,primUFunVal(arityOfPrimUFun,default_ufv_pa_for_procs N.arityOf_name)),     
                         (N.children_symbol,primUFunVal(childrenPrimUFun,default_ufv_pa_for_procs N.children_name)),     
                         (N.varsFun_symbol,primUFunVal(varsPrimUFun,default_ufv_pa_for_procs N.varsFun_name)),     
                         (Symbol.symbol("hash"),primUFunVal(hashPrimUFun,default_ufv_pa_for_procs "hash")),     
                         (Symbol.symbol("sent-code"),primUFunVal(codePrimUFun,default_ufv_pa_for_procs "sent-code")),
                         (Symbol.symbol("ab-code"),primUFunVal(abCodePrimUFun,default_ufv_pa_for_procs "ab-code")),
                         (Symbol.symbol("canon?"),primUFunVal(isCanonicalPrimUFun,default_ufv_pa_for_procs "canon?")),
                         (Symbol.symbol("fsd"),primUFunVal(getFunDefInfoPrimUFun,default_ufv_pa_for_procs "fsd")),
                         (Symbol.symbol("tc"),primUFunVal(tcPrimUFun,default_ufv_pa_for_procs "tc")),
                         (Symbol.symbol("get-eval-proc-name"),primUFunVal(evalProcNamePrimUFun,default_ufv_pa_for_procs "get-eval-proc-name")),
                         (Symbol.symbol("get-eval-proc-name-1"),primUFunVal(evalProcName1PrimUFun,default_ufv_pa_for_procs "get-eval-proc-name-1")),
                         (Names.evalFun_symbol,SV.funVal(processPhraseFromStringFun,Names.evalFun_name,SV.default_fv_pa_for_procs 1)),
                         (Names.processInputFun_symbol,SV.funVal(processInputFromStringFun,Names.processInputFun_name,SV.default_fv_pa_for_procs 1)),
                         (Symbol.symbol("display"),primUFunVal(displayPrimUFun,default_ufv_pa_for_procs "display")),
                         (N.freeVarsFun_symbol,primUFunVal(freeVarsPrimUFun,default_ufv_pa_for_procs N.freeVarsFun_name)),     
                         (Symbol.symbol("tsat"),funVal(satSolve,"tsat",default_fv_pa_for_procs 1)),
                         (Symbol.symbol("tsat0"),funVal(satSolve0,"tsat0",default_fv_pa_for_procs 1)),
                         (N.fastSatFun_symbol,funVal(fastSatFun,N.fastSatFun_name,default_fv_pa_for_procs 2)),
                         (N.getABFun_symbol,funVal(getABFun,N.getABFun_name,default_fv_pa_for_procs 0)),     
                         (Symbol.symbol "get-bucket-sizes",funVal(getBucketSizesFun,"get-bucket-sizes",default_fv_pa_for_procs 0)),
                         (Symbol.symbol "show-bucket-stats",funVal(showBucketStatisticsFun,"show-bucket-stats",default_fv_pa_for_procs 0)),
                         (N.concatFun_symbol,funVal(concatFun,N.concatFun_name,default_fv_pa_for_procs 2)),
                         (N.minusFun_symbol,funVal(minusFun,N.minusFun_name,default_fv_pa_for_procs 2)),
                         (N.fresh_var_with_prefix_symbol,primBFunVal(freshVarWithPrefixPrimBFun,default_bfv_pa_for_procs N.fresh_var_with_prefix_name)),         
                         (N.isFunctionFun_symbol,primUFunVal(isFunctionPrimUFun,default_ufv_pa_for_procs N.isFunctionFun_name)),
                         (N.vector_len_symbol,primUFunVal(vectorLenPrimUFun,default_ufv_pa_for_procs N.vector_len_name)),
                         (N.isMethodFun_symbol,primUFunVal(isMethodPrimUFun,default_ufv_pa_for_procs N.isMethodFun_name)),
                         (N.isSubFun_symbol,primUFunVal(isSubPrimUFun,default_ufv_pa_for_procs N.isSubFun_name)),
                         (N.isTermFun_symbol,primUFunVal(isTermPrimUFun,default_ufv_pa_for_procs N.isTermFun_name)),
                         (N.isMetaIdFun_symbol,primUFunVal(isMetaIdPrimUFun,default_ufv_pa_for_procs N.isMetaIdFun_name)),
                         (N.isPropFun_symbol,primUFunVal(isPropPrimUFun,default_ufv_pa_for_procs N.isPropFun_name)),
                         (N.yicesSolveFun_symbol,primUFunVal(yicesSolvePrimUFun,default_ufv_pa_for_procs N.yicesSolveFun_name)),
                         (N.cvcSolveFun_symbol,primUFunVal(cvcSolvePrimUFun,default_ufv_pa_for_procs N.cvcSolveFun_name)),
                         (N.yicesSolveFun_symbol',primBFunVal(yicesSolvePrimBFun,default_bfv_pa_for_procs N.yicesSolveFun_name')),
                         (N.smtSolveFun_symbol,primBFunVal(smtGeneralSolvePrimBFun,default_bfv_pa_for_procs N.smtSolveFun_name)),
                         (S.symbol "yices-write-defs",funVal(yicesWriteDefsFun,"yices-write-defs",default_fv_pa_for_procs 3)),
                         (N.procNameFun_symbol,primUFunVal(procNamePrimUFun,default_ufv_pa_for_procs N.procNameFun_name)),
                         (N.isListFun_symbol,primUFunVal(isListPrimUFun,default_ufv_pa_for_procs N.isListFun_name)),
                         (N.isCharFun_symbol,primUFunVal(isCharPrimUFun,default_ufv_pa_for_procs N.isCharFun_name)),
                         (N.isTermConFun_symbol,primUFunVal(isTermConPrimUFun,default_ufv_pa_for_procs N.isTermConFun_name)),
                         (N.isUnitFun_symbol,primUFunVal(isUnitPrimUFun,default_ufv_pa_for_procs N.isUnitFun_name)),
                         (N.isCellFun_symbol,primUFunVal(isCellPrimUFun,default_ufv_pa_for_procs N.isCellFun_name)),
                         (N.makeTermFun_symbol,primBFunVal(makeTermPrimBFun,default_bfv_pa_for_procs N.makeTermFun_name)),          
                         (N.getDebugModeFun_symbol,funVal(getDebugModeFun,N.getDebugModeFun_name,default_fv_pa_for_procs 0)),
                         (N.setDebugModeFun_symbol,primUFunVal(setDebugModePrimUFun,default_ufv_pa_for_procs N.setDebugModeFun_name)),
			 (N.getTraceLevelFun_symbol,funVal(getTraceLevelFun,N.getTraceLevelFun_name,default_fv_pa_for_procs 0)),
                         (N.indentPrintFun_symbol,primBFunVal(indentPrintPrimBFun,default_bfv_pa_for_procs N.indentPrintFun_name)),
                         (N.moduleToStringFun_symbol,primUFunVal(moduleToStringPrimUFun,default_ufv_pa_for_procs N.moduleToStringFun_name)),
                         (N.moduleToHtFun_symbol,primUFunVal(moduleToHTPrimUFun,default_ufv_pa_for_procs N.moduleToHtFun_name)),
                         (N.moduleSizeFun_symbol,primUFunVal(moduleSizePrimUFun,default_ufv_pa_for_procs N.moduleSizeFun_name)),
                         (N.moduleSizeFun1_symbol,primUFunVal(moduleSize1PrimUFun,default_ufv_pa_for_procs N.moduleSizeFun1_name)),
                         (N.submodulesFun_symbol,primUFunVal(submodulesPrimUFun,default_ufv_pa_for_procs N.submodulesFun_name)),
                         (N.moduleAbFun_symbol,primUFunVal(moduleAbPrimUFun,default_ufv_pa_for_procs N.moduleAbFun_name)),
                         (N.moduleDomFun_symbol,primUFunVal(moduleDomPrimUFun,default_ufv_pa_for_procs N.moduleDomFun_name)),
                         (N.moduleAppFun_symbol,primBFunVal(moduleAppPrimBFun,default_bfv_pa_for_procs N.moduleAppFun_name)),
                         (N.getAllStructures_symbol,funVal(allStructuresFun,N.getAllStructures_name,default_fv_pa_for_procs 0)),
                         (N.fsymsInFunDefTableFun_symbol,funVal(fsymsInFunDefTableFun,N.fsymsInFunDefTableFun_name,default_fv_pa_for_procs 0)),
                         (N.haltFun_symbol,funVal(haltFun,N.haltFun_name,default_fv_pa_for_procs 0)),
                         (S.symbol("standard-reduce-proc-name-suffix"),funVal(getStandardReduceProcNameSuffixFun,"standard-reduce-proc-name-suffix",default_fv_pa_for_procs 0)),
                         (N.currentModPathFun_symbol,funVal(getCurrentModPathFun,N.currentModPathFun_name,default_fv_pa_for_procs 0)),
                         (N.makeMapFun_symbol,funVal(makeMapFun,N.makeMapFun_name,default_fv_pa_for_procs 0)),
                         (N.applyExtractedSortSubFun_symbol,funVal(applyExtractedSortSubFun,N.applyExtractedSortSubFun_name,default_fv_pa_for_procs 3)),
                         (Symbol.symbol("ab-tag"),funVal(getABTagFun,"ab-tag",default_fv_pa_for_procs 0)),
                         (Symbol.symbol("rrepeat"),primBFunVal(repeatPrimBFun,default_bfv_pa_for_procs "rrepeat")),
                         (N.lenFun_symbol,primUFunVal(lenPrimUFun,default_ufv_pa_for_procs N.lenFun_name)),
                         (N.last_proof_symbol,init_last_proof_val),
                         (N.isNumeralFun_symbol,primUFunVal(isNumeralPrimUFun,default_ufv_pa_for_procs N.isNumeralFun_name)),
                         (N.getFlagFun_symbol,primUFunVal(getFlagPrimUFun,default_ufv_pa_for_procs N.getFlagFun_name)),
                         (N.getBoolFlagFun_symbol,primUFunVal(getBoolFlagPrimUFun,default_ufv_pa_for_procs N.getBoolFlagFun_name)),
                         (N.last_value_symbol,unitVal),
                         (N.max_int_symbol,max_int_val),
                         (N.mpPrimMethod_symbol,SV.primBMethodVal(mpPrimBMethod,N.mpPrimMethod_symbol)),
                         (N.claimPrimMethod_symbol,SV.primUMethodVal(claimPrimUMethod,N.claimPrimMethod_symbol)),
                         (N.absurdPrimMethod_symbol,primBMethodVal(absurdPrimBMethod,N.absurdPrimMethod_symbol)),
                         (N.bothPrimMethod_symbol,SV.primBMethodVal(bothPrimBMethod,N.bothPrimMethod_symbol)),
                         (N.leftAndPrimMethod_symbol,primUMethodVal(leftAndPrimUMethod,N.leftAndPrimMethod_symbol)),
                         (N.rightAndPrimMethod_symbol,primUMethodVal(rightAndPrimUMethod,N.rightAndPrimMethod_symbol)),
                         (N.conjIntroPrimMethod_symbol,primUMethodVal(conjIntroPrimUMethod,N.conjIntroPrimMethod_symbol)),
                         (N.dnPrimMethod_symbol,primUMethodVal(dnPrimUMethod,N.dnPrimMethod_symbol)),
                         (N.eitherPrimMethod_symbol,methodVal(eitherPrimMethod,N.eitherPrimMethod_symbol)),
                         (N.leftEitherPrimMethod_symbol,primBMethodVal(leftEitherPrimBMethod,N.leftEitherPrimMethod_symbol)),
                         (N.rightEitherPrimMethod_symbol,primBMethodVal(rightEitherPrimBMethod,N.rightEitherPrimMethod_symbol)),
                         (N.equivPrimMethod_symbol,primBMethodVal(equivPrimBMethod,N.equivPrimMethod_symbol)),
                         (N.leftIffPrimMethod_symbol,primUMethodVal(leftIffPrimUMethod,N.leftIffPrimMethod_symbol)),
                         (N.rightIffPrimMethod_symbol,primUMethodVal(rightIffPrimUMethod,N.rightIffPrimMethod_symbol)),
                         (N.force_symbol,primUMethodVal(forcePrimUMethod,N.force_symbol)),
                         (N.cdPrimMethod_symbol,methodVal(cdPrimMethod,N.cdPrimMethod_symbol)),
                         (N.sortInstancePrimMethod_symbol,methodVal(sortInstancePrimMethod,N.sortInstancePrimMethod_symbol)),
                         (N.fail_method_symbol,methodVal(failPrimMethod,N.fail_method_symbol)),
                         (N.appMethod_method_symbol,methodVal(appMethodMethod,N.appMethod_method_symbol)),
                         (N.appProc_proc_symbol,primBFunVal(appProcPrimBFun,default_bfv_pa_for_procs N.appProc_proc_name)),
                         (N.unifiable_sort_fun_symbol,primBFunVal(unifiableSortsPrimBFun,default_bfv_pa_for_procs N.unifiable_sort_fun_name)),
                         (N.built_in_merge_sort_symbol',primBFunVal(mergeSortPrimBFun,default_bfv_pa_for_procs N.built_in_merge_sort_name')),
                         (N.built_in_merge_sort_symbol,primBFunVal(mergeSortPrimBFun',default_bfv_pa_for_procs N.built_in_merge_sort_name)),
                         (N.uspecPrimMethod_symbol,SV.primBMethodVal(uSpecPrimBMethod,N.uspecPrimMethod_symbol)),
                         (N.proofErrorMethod_symbol,SV.primUMethodVal(proofErrorPrimUMethod,N.proofErrorMethod_symbol)),
                         (N.compErrorFun_symbol,primUFunVal(compErrorPrimUFun,default_ufv_pa_for_procs N.compErrorFun_name)),
                         (N.egenPrimMethod_symbol,methodVal(eGenPrimMethod,N.egenPrimMethod_symbol)),
                         (N.egenUniquePrimMethod_symbol,methodVal(eGenUniquePrimMethod,N.egenUniquePrimMethod_symbol)),
                         (N.constructor_inj_symbol,SV.primUMethodVal(constructorInjPrimUMethod,N.constructor_inj_symbol)),
                         (Symbol.symbol("cons-injectivity"), primUFunVal(constructorInjPrimUFun,default_ufv_pa_for_procs "cons-injectivity")),
                         (N.constructor_excl_symbol,SV.primBMethodVal(constructorExclPrimBMethod,N.constructor_excl_symbol)),
                         (N.constructor_exhaust_symbol,
                          SV.primUMethodVal(constructorExhaustPrimUMethod,N.constructor_exhaust_symbol)),
                         (N.structureConstructorsFun_symbol,
                          primUFunVal(structureConstructorsPrimUFun,default_ufv_pa_for_procs N.structureConstructorsFun_name)),
                         (Symbol.symbol("qualify-sort-name"),
                          primUFunVal(qualifySortNamePrimUFun,default_ufv_pa_for_procs "qualify-sort-name")),
                         (N.satFun_symbol,primUFunVal(satPrimUFun,default_ufv_pa_for_procs N.satFun_name)),
                         (N.unparseFun_symbol,primUFunVal(unparsePrimUFun,default_ufv_pa_for_procs N.unparseFun_name)),
                         (N.true_intro_PrimMethod_symbol,methodVal(trueIntroPrimMethod,
			  N.true_intro_PrimMethod_symbol)),                         
                         (N.is_assertion_symbol,primUFunVal(isAssertionPrimUFun,default_ufv_pa_for_procs N.is_assertion_name)),
                         (N.is_constructor_symbol,primUFunVal(isConstructorPrimUFun,default_ufv_pa_for_procs N.is_constructor_name)),
                         (N.is_free_constructor_symbol,primUFunVal(isFreeConstructorPrimUFun,default_ufv_pa_for_procs N.is_free_constructor_name)),
                         (N.isStructureWithoptionValuedSelectorsFun_symbol,primUFunVal(isStructureWithoptionValuedSelectorsFun,
                                                                                       default_ufv_pa_for_procs N.isStructureWithoptionValuedSelectorsFun_name)),
                         (N.makeHTFun_symbol,primUFunVal(makeHTPrimUFun,default_ufv_pa_for_procs N.makeHTFun_name)),
                         (N.makeTermHTFun_symbol,primUFunVal(makeTermHTPrimUFun,default_ufv_pa_for_procs N.makeTermHTFun_name)),
                         (N.fcongPrimMethod_symbol,methodVal(fcongPrimMethod,N.fcongPrimMethod_symbol)),
                         (N.rcongPrimMethod_symbol,SV.primBMethodVal(rcongPrimBMethod,N.rcongPrimMethod_symbol)),
                         (N.defEqnsFun_symbol,primUFunVal(defEqnsPrimUFun,default_ufv_pa_for_procs N.defEqnsFun_name)),
                         (N.makeTableFun_symbol,funVal(makeTableFun,N.makeTableFun_name,default_fv_pa_for_procs 1)),
                         (N.addTableFun_symbol,primBFunVal(addTablePrimBFun,default_bfv_pa_for_procs N.addTableFun_name)),
                         (N.addMapFun_symbol,primBFunVal(addMapPrimBFun,default_bfv_pa_for_procs N.addMapFun_name)),
                         (N.mapApplyFun_symbol,primBFunVal(mapApplyPrimBFun,default_bfv_pa_for_procs N.mapApplyFun_name)),
                         (N.removeMapFun_symbol,primBFunVal(removeMapPrimBFun,default_bfv_pa_for_procs N.removeMapFun_name)),
                         (N.mapSizeFun_symbol,primUFunVal(mapSizePrimUFun,default_ufv_pa_for_procs N.mapSizeFun_name)),
                         (N.mapKeysFun_symbol,primUFunVal(mapKeysPrimUFun,default_ufv_pa_for_procs N.mapKeysFun_name)),
                         (N.mapValuesFun_symbol,primUFunVal(mapValuesPrimUFun,default_ufv_pa_for_procs N.mapValuesFun_name)),
                         (N.mapKeyValuesFun_symbol,primUFunVal(mapKeyValuesPrimUFun,default_ufv_pa_for_procs N.mapKeyValuesFun_name)),
                         (N.sentSubtermsFun_symbol,primUFunVal(sentSubtermsPrimUFun,default_ufv_pa_for_procs N.sentSubtermsFun_name)),
                         (N.subtermsFun_symbol,primUFunVal(subtermsPrimUFun,default_ufv_pa_for_procs N.subtermsFun_name)),
                         (N.mapToValuesFun_symbol,primBFunVal(mapToValuesPrimBFun,default_bfv_pa_for_procs N.mapToValuesFun_name)),
                         (N.mapToKeyValuesFun_symbol,primBFunVal(mapToKeyValuesPrimBFun,default_bfv_pa_for_procs N.mapToKeyValuesFun_name)),
                         (N.applyToKeyValuesFun_symbol,primBFunVal(applyToKeyValuesPrimBFun,default_bfv_pa_for_procs N.applyToKeyValuesFun_name)),
                         (N.mapFoldlFun_symbol,funVal(mapFoldlFun,N.mapFoldlFun_name,default_fv_pa_for_procs 3)),
                         (N.makeMapFromListFun_symbol,primUFunVal(makeMapFromListPrimUFun,default_ufv_pa_for_procs N.makeMapFromListFun_name)),
                         (N.removeTableFun_symbol,primBFunVal(removeTablePrimBFun,default_bfv_pa_for_procs N.removeTableFun_name)),
                         (N.findTableFun_symbol,primBFunVal(findTablePrimBFun,default_bfv_pa_for_procs N.findTableFun_name)),
                         (N.findMapFun_symbol,primBFunVal(findMapPrimBFun,default_bfv_pa_for_procs N.findMapFun_name)),
                         (N.tableSizeFun_symbol,primUFunVal(tableSizePrimUFun,default_ufv_pa_for_procs N.tableSizeFun_name)),
                         (N.tableClearFun_symbol,primUFunVal(tableClearPrimUFun,default_ufv_pa_for_procs N.tableClearFun_name)),
                         (N.tableToStringFun_symbol,primUFunVal(tableToStringPrimUFun,default_ufv_pa_for_procs N.tableToStringFun_name)),
                         (N.tableToListFun_symbol,primUFunVal(tableToListPrimUFun,default_ufv_pa_for_procs N.tableToListFun_name)),
                         (N.nnf_fun_symbol,primUFunVal(nnfFun,default_ufv_pa_for_procs N.nnf_fun_name)),
                         (N.cnfFun_symbol,primBFunVal(cnfPrimBFun,default_bfv_pa_for_procs N.cnfFun_name)),
                         (N.hasMonoSortFun_symbol,primUFunVal(hasMonoSortPrimUFun,default_ufv_pa_for_procs N.hasMonoSortFun_name)),
                         (N.escapeStringFun_symbol,primUFunVal(escapeStringPrimUFun,default_ufv_pa_for_procs N.escapeStringFun_name)),
                         (Symbol.symbol("make-private"),primUFunVal(makePrivatePrimUFun,default_ufv_pa_for_procs "make-private")),
 			 (N.eqTranPrimMethod_symbol,SV.primBMethodVal(eqTranPrimBMethod,N.eqTranPrimMethod_symbol)),
 			 (N.eqSymPrimMethod_symbol,SV.primUMethodVal(eqSymPrimUMethod,N.eqSymPrimMethod_symbol)),
 			 (N.eqReflexPrimMethod_symbol,SV.primUMethodVal(eqReflexPrimUMethod,N.eqReflexPrimMethod_symbol)),
                         (N.athena_home_symbol,MLStringToAthString(Paths.athena_home)),
                         (N.empty_mapping_symbol,mapVal(Maps.makeMap(SV.compare))),
			 (Symbol.symbol("eval-prop-canonically"),
			  primBFunVal(evalPropCanonicalPrimBFun,default_bfv_pa_for_procs "eval-prop-canonically")),
			 (N.compareFun_symbol,
			  primBFunVal(comparePrimBFun,default_bfv_pa_for_procs N.compareFun_name)),
                         (N.root_dir_symbol,MLStringToAthString(Paths.root))]

val _ = init_val_bindings_ref := init_val_bindings

val _ = updateTopValEnvLstOldAndFast(init_val_bindings) 

fun updateTopValEnvWithNewPrimUFun(sym,f) = 
  let val name = S.name(sym)
  in
    updateTopValEnvLstOldAndFast([(sym,primUFunVal(f,default_ufv_pa_for_procs name))])
  end

fun updateTopValEnvWithNewPrimBFun(sym,f) = 
  let val name = S.name(sym)
  in
    updateTopValEnvLstOldAndFast([(sym,primBFunVal(f,default_bfv_pa_for_procs name))])
  end

end (** of structure TopEnv **)
