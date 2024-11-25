(*=================================================================================

Proof evaluation with type-alpha certificate production. 

=======================================================================*)

structure Alpha = 

struct

structure S = Symbol
structure A = AbstractSyntax
type prop = Prop.prop
type symbol = S.symbol
type variable = AthTerm.variable 

open Semantics

datatype hypothesis = hyp of symbol option * prop 
datatype alpha_val = term of AthTerm.term | sent of prop 

datatype certificate = ruleApp of {rule:symbol, args: alpha_val list}
                     | assumeProof of {hyp: hypothesis, body: certificate}
                     | supAbProof of {hyp: hypothesis, body: certificate}
                     | composition of {left: certificate, right: certificate}
                     | pickAny of {eigen_var: symbol, actual_fresh: variable, body: certificate}
                     | conclude of {expected_conc: prop, body: certificate}

type alpha_ded_info = {proof: certificate, conc: Prop.prop, fa: Prop.prop list} 

fun makeAlphaDed() = let val res: alpha_ded_info = {proof=ruleApp({rule=S.symbol("foo"),args=[]}),conc=Prop.true_prop, fa = []}
                     in
                       res
                     end

fun getProp(v) = (case coerceValIntoProp(v) of SOME(p) => p)

fun getFA(method_sym,vals: value list,ab) = 
  let val method_name = S.name(method_sym)
      val props = Basic.mapSelect(getProp,vals,fn _ => true)
  in  
     case method_name of 
        "left-either"  => [(Basic.first props)]
      | "right-either" => [(Basic.second props)]
      | "either" => let val [p1,p2] = props
                        val fas = ref([])
                        val _ = if not(ABase.isMember(p1,ab)) then fas := [p1] else ()
                        val _ = if not(ABase.isMember(p2,ab)) then fas := p1::(!fas) else ()
                    in
                      !fas
                    end
      | _ => props        
  end

fun propUnion(prop_list_1,prop_list_2) = Basic.listUnion(prop_list_1,prop_list_2,Prop.alEq)
fun propDiff(prop_list_1,prop_list_2) = Basic.listDiff(prop_list_1,prop_list_2,Prop.alEq)
          

val evalDedAlpha = 
let val iarm_stack:iarm_type LStack.stack ref = ref(LStack.empty)
    fun initIndStack() = iarm_stack := LStack.empty
    fun initCallStack() = call_stack := LStack.empty     
    fun getAlphaVal(v) = (case coerceValIntoTerm(v) of 
                             SOME(t) => term(t)
			   | _ => (case coerceValIntoProp(v) of
                                      SOME(p) => sent(p)))
    fun evDed(method_app as A.BMethAppDed({method,arg1,arg2,pos}),env,ab) = 
    ((let val head_val = evalExp(method,env,ab) 
      in
        (case head_val of
           primBMethodVal(M,method_sym) => 
                (let 
                     val (v1,ded_1_info_opt) = (case arg1 of 
                                                  A.ded(d1) => (case evDed(d1,env,ab) of (a,b) => (a,SOME(b)))
					        | A.exp(e1) => (evalExp(e1,env,ab),NONE))
                     val (v2,ded_2_info_opt) = (case arg2 of 
                                                  A.ded(d2) => (case evDed(d2,env,ab) of (a,b) => (a,SOME(b)))
					        | A.exp(e2) => (evalExp(e2,env,ab),NONE))
                     val ab' = if A.isDeduction(arg1) then putValIntoAB(v1,ab) else ab 
                     val ab'' = if A.isDeduction(arg2) then putValIntoAB(v2,ab') else ab' 
                     val res_val = M(v1,v2,env,ab'')
                     val (av1, av2) = (getAlphaVal(v1), getAlphaVal(v2))                      
                     val ded_info = (case (ded_1_info_opt,ded_2_info_opt) of
                                       (SOME({conc=conc1,fa=fa1,proof=proof1,...}),NONE) => 
				          let val final_fas = propUnion(fa1,propDiff(getFA(method_sym,[v1,v2],ab''),[conc1]))
                                          in
                                            {conc=getProp(res_val),
					     fa=final_fas,
					     proof=composition({left=proof1,right=ruleApp({rule=method_sym,args=[av1,av2]})})}
					  end
                                     | (NONE,SOME({conc=conc2,fa=fa2,proof=proof2,...})) => 
				          let val final_fas = propUnion(fa2,propDiff(getFA(method_sym,[v1,v2],ab''),[conc2]))
                                          in
                                            {conc=getProp(res_val),
					     fa=final_fas,
					     proof=composition({left=proof2,right=ruleApp({rule=method_sym,args=[av1,av2]})})}
					  end
				     | (SOME({conc=conc1,fa=fa1,proof=proof1,...}), 
					SOME({conc=conc2,fa=fa2,proof=proof2,...})) => 
				          let val final_fas = propUnion(fa1,propUnion(fa2,propDiff(getFA(method_sym,[v1,v2],ab''),[conc1,conc2])))
                                          in
                                            {conc=getProp(res_val),
					     fa=final_fas,
					     proof=composition({left=proof1,
								right=composition({left=proof2,
										  right=ruleApp({rule=method_sym,args=[av1,av2]})})})}
					  end
                                     | (NONE,NONE) => {conc=getProp(res_val),
						       fa=getFA(method_sym,[v1,v2],ab''),
						       proof=ruleApp({rule=method_sym,args=[av1,av2]})})
                 in
                    (res_val,ded_info)
                 end handle PrimError(msg) => evError(msg,SOME(pos))
                          | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()
                                                in
                                                  evError(msg,SOME(right_pos))
                                                end)
         | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) => 
                  let val v1 = evalPhrase(arg1,env,ab)
                      val v2 = evalPhrase(arg2,env,ab) 
                      val ab' = if A.isDeduction(arg1) then putValIntoAB(v1,ab) else ab
                      val ab'' = if A.isDeduction(arg2) then putValIntoAB(v2,ab') else ab'
                      val vm = Symbol.enter(Symbol.enter(val_map,s1,v1),s2,v2)
                      val _ = addPos(!name,pos)
                  in
                     evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab'')
                  end
        | _ =>  evalMethodApp(method,[arg1,arg2],env,ab,pos))
      end))
  | evDed(A.UMethAppDed({method,arg,pos}),env,ab) = 
     ((let val head_val = evalExp(method,env,ab)
       in
         (case head_val of
              primUMethodVal(f,method_sym) => 
                                     (let val arg_val = evalPhrase(arg,env,ab)
                                          val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
                                          val conclusion_val = f(arg_val,env,ab')
                                          val ded_info = {conc=getProp(conclusion_val),
							  fa=getFA(method_sym,[arg_val],ab'),
							  proof=ruleApp({rule=method_sym,args=[getAlphaVal(arg_val)]})}
                                      in
                                         (conclusion_val,ded_info)
                                      end handle PrimError(msg) => evError(msg,SOME(pos))                                      
                                               | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()
                                                                     in
                                                                        evError(msg,SOME(right_pos))
                                                                     end)
            | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),clos_name) => 
                   let val arg_val = evalPhrase(arg,env,ab)
                       val vm = Symbol.enter(val_map,s,arg_val)
                       val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
                       val _ = addPos(!clos_name,pos)
                   in
                      evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab')
                   end)
       end))
  | evDed(method_app as A.methodAppDed({method,args,pos=app_pos}),env,ab) = evalMethodApp(method,args,env,ab,app_pos)
(*******************************************************************************************************************************************************************************
  | evDed(A.letDed({bindings,body,pos}),env,ab) = 
       let fun doLetDed([]:A.binding list,env1,ab1) = evDed(body,env1,ab1)
             | doLetDed({bpat,def=A.ded(d),pos}::more,env1,ab1) = 
                  let val dval = evDed(d,env1,ab1)
                  in
                     (case matchPat(dval,bpat,makeEvalExpFunction (env1,ab)) of 
                        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                         val new_ab = (case dval of
                                                          propVal(p) => ABaseAugment(ab1,Prop.decomposeConjunctions p)
                                                        | _ => ab1)
                                     in
                                       doLetDed(more,new_env,new_ab)
                                     end 
                      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                                     (valLCTypeAndStringNoColon dval),
                                     SOME(A.posOfPat(bpat))))
                  end
             | doLetDed({bpat,def=A.exp(e),pos}::more,env1,ab1) = 
                  let val eval = evalExp(e,env1,ab1)
                  in
                     (case matchPat(eval,bpat,makeEvalExpFunction (env1,ab)) of 
                        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                     in
                                       doLetDed(more,new_env,ab1)
                                     end 
                      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                                      (valLCTypeAndStringNoColon eval),
                                     SOME(A.posOfPat(bpat))))
                  end
           in
              doLetDed(bindings,env,ab)
       end
  | evDed(A.matchDed({discriminant,clauses,pos}),env,ab) =
      let val discrim_value = evalPhrase(discriminant,env,ab)
          val e_fun = makeEvalExpFunction (env,ab)
          val new_ab = if A.isDeduction(discriminant) then
                          (case coerceValIntoProp(discrim_value) of
                              SOME(P) => ABase.insert(P,ab)
                            | _ => evError("Impossible error encountered in dmatch"^
                                      "---the discriminant is a deduction and yet it "^
                                      "did not produce a sentence",
                                      SOME(A.posOfPhrase(discriminant))))
                       else ab
          fun tryClauses([]:A.dmatch_clause list) =  
                  evError("dmatch failed---the "^valLCTypeAndStringNoColon(discrim_value)^
                          "\ndid not match any of the given patterns",SOME(pos))
            | tryClauses({pat,ded}::more) = 
               (case matchPat(discrim_value,pat,e_fun) of
                   SOME(map,_) => 
                      let val new_env = ref(augmentWithMap(!env,map))
                          in
                            evDed(ded,new_env,new_ab)
                      end
                 | _ => tryClauses(more))
          in
            tryClauses(clauses)
      end                         
  | evDed(A.assumeDed({assumption,body,pos}),env,ab) = 
            let val aval = evalPhrase(assumption,env,ab)
            in
               (case coerceValIntoProp(aval) of
                   SOME(p1) => let val asms = Prop.decomposeConjunctions(p1)
                                   val ab' = ABase.augment(ab,asms)
                               in 
                                 (case coerceValIntoProp(evDed(body,env,ab')) of 
                                    SOME(p2) => propVal(P.makeConditional(p1,p2))
                                  | _ => evError("Impossible error encountered in assume deduction: the body of "^
                                                  "the deduction did not produce a sentence",
			  		  SOME(A.posOfDed(body))))
                               end
                 | _ => evError("In a deduction of the form (assume F D), the value of F"^ 
                                " must\nbe a sentence, but here it was a "^valLCTypeAndString(aval),
                                SOME(A.posOfPhrase(assumption))))
            end
  | evDed(A.assumeLetDed({bindings,body,pos}),env,ab) = 
           let fun getProp(F,is_ded,env,ab) = 
                  let val Fval = evalPhrase(F,env,ab)
                  in
                     (case coerceValIntoProp(Fval) of
                         SOME(P) => P
                       | _ => let val Fkind = if is_ded then "body" else "hypothesis" 
                         in
                            evError("assume-let "^Fkind^" failed to result in a sentence. Instead, it "^
                                    "produced a "^valLCTypeAndString(Fval),SOME(A.posOfPhrase(F)))
                         end)
                  end
               fun doBindings([]:A.binding list,assumptions,env1) = 
                     let val asms' = Basic.flatten(map Prop.decomposeConjunctions assumptions)
                     in
                       propVal(Prop.foldConditionals(rev(assumptions),
                               getProp(A.ded(body),true,env1,ABaseAugment(ab,asms'))))
                     end
                  | doBindings({bpat,def,...}::more,assumptions,env1) = 
                       let val new_assumption = getProp(def,false,env1,ab)
                       in
                          (case matchPat(propVal(new_assumption),bpat,makeEvalExpFunction (env1,ab)) of 
                              SOME(map,_) => let val (vmap,mmap) = getValAndModMaps(!env1)
                                               val env1' = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                           in
                                             doBindings(more,new_assumption::assumptions,env1')
                                           end
                            | _ => evError("Assume pattern failed to match the corresponding value, the\n "^
                                            (valLCTypeAndStringNoColon (propVal new_assumption)),
                                            SOME(A.posOfPat(bpat))))
                       end
           in
              doBindings(bindings,[],env)
           end
  | evDed(A.absurdDed({hyp,body,pos}),env,ab) = doSupposeAbsurd(hyp,NONE,body,pos,env,ab)
  | evDed(A.absurdLetDed({named_hyp,body,pos}),env,ab) = 
          let val (hyp_name_pat,hyp) = (#bpat(named_hyp),#def(named_hyp))
              in
                doSupposeAbsurd(hyp,SOME(hyp_name_pat),body,pos,env,ab)
          end
  | evDed(A.inductionDed({prop,clauses,pos}),env:value_environment ref,ab) = 
      let val (uvar,body,goal) = let val pval = evalPhrase(prop,env,ab)
                                 in
                                   (case (coerceValIntoProp(pval)) of
	    	  	   	     SOME(P) => (case P.isUGen(P) of 
                                                    SOME(v,body) => (v,body,P)
				    	           | _ => evError((prefix ())^(msg3 pval),
					  	    	           SOME(A.posOfPhrase(prop))))
                                    | _ => evError((prefix ())^(msg3 pval),SOME(A.posOfPhrase(prop))))
  			         end
          val uvar_sort = ATV.getSort(uvar)
          val _ = if StructureAnalysis.isStructureType(uvar_sort) then () else 
                  evError(msg1(2,ATV.toStringWithSort(uvar),P.toString(body,makeVarSortPrinter()),
			  F.toStringDefault(uvar_sort)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evalExp(e',env',ab)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,uvar_sort,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,uvar_sort) of
                      SOME(t) => evError(msg2(F.toStringDefault(uvar_sort),
                                              AT.toStringDefault(t)),SOME(pos))
                    | _ => ()) 
          fun property(t) = P.replace(uvar,t,body)
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),previous_clauses,ab) = 
               let fun emsg(req,gotten) = "One of the given cases of this inductive deduction failed "^
                                          "to establish the right conlusion.\nWanted: "^
                                           Util.decide(pprintProp(req),50)^
                                          "\nGotten: "^Util.decide(pprintProp(gotten),50)^"\n"
                   val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val new_iarm = {uvar=uvar,uvar_sort=uvar_sort,uprop=body,
                                   uv_pattern=pat_as_ath_term}
                   val _ = iarm_stack := LStack.push(new_iarm,!iarm_stack)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                 else new_env_0
                   val real_current_goal = property(pat_as_ath_term)
                   fun getReflexiveFreshvars(vars,res) = 
                         (case vars of
                             [] => (rev res)
                           | fv::more => let val fresh_var_sort = ATV.getSort(fv)
                                         in
                                            (case F.isVarOpt(fresh_var_sort) of
                                                SOME(_) => getReflexiveFreshvars(more,res)
                                              | _ => (case F.unify(fresh_var_sort,F.rename(uvar_sort)) of
                                                         SOME(sub) => let val new = ATV.applySortSub(sub,fv)
                                                                      in
                                                                        getReflexiveFreshvars(more,new::res)
                                                                      end
                                                       | _ =>  getReflexiveFreshvars(more,res)))
                                         end)

                  val reflexive_fresh_vars = getReflexiveFreshvars(fresh_vars,[])
                  val reflexive_vars_as_terms = map AT.makeVar reflexive_fresh_vars
                  val current_ind_hyps = map property reflexive_vars_as_terms
                  fun sameRootSymbol(t1,t2) = 
                         (case (AT.isApp(t1),AT.isApp(t2)) of
                             (SOME(f,_),SOME(g,_)) => MS.modSymEq(f,g)
                           | _ => false)
                  val diff_facts:P.prop list = 
                          if not(!(Options.fundef_mlstyle_option)) orelse null(previous_clauses) then [] 
                          else (let val previous_pats_as_terms:AT.term list = map (fn (_,y,_,_,_) => y) previous_clauses
                                    val previous_pats_as_terms = List.filter (fn t => sameRootSymbol(t,pat_as_ath_term)) previous_pats_as_terms
                                    val previous_pat_string = Basic.printSExpListStr(previous_pats_as_terms,fn t => (valToString (termVal t)))
                                    val pstr = getSafeName("diff*")
                                    val str = "("^pstr^" "^(valToString (termVal pat_as_ath_term))^" ["^previous_pat_string^"])"
                                    val evalString = !evaluateString
                                    val lv = evalString(str)
                                in 
                                   case coerceValIntoProp(lv) of
                                       SOME(p) => let val res = Prop.decomposeConjunctions(p)
                                                  in
                                                    res
                                                  end
                                end) handle _ => [] 
                   val ind_hyps = (current_ind_hyps@
                                  (if (AT.height(pat_as_ath_term) = 0) then [] 
                                   else getInductiveHypotheses(!iarm_stack,fresh_vars,real_current_goal,pat_as_ath_term)))
				  handle Basic.FailLst(msgs) => evError("Error in generating inductive "^
									"hypotheses..."^Basic.failMsgsToStr(msgs),
									SOME(pos))
                   val new_ab = ABaseAugment(ab,diff_facts@ind_hyps)
                   val res_prop = (case evDed(ded,new_env,new_ab) of
                                      propVal(P) => P
                                    | _ => raise Basic.Never)
               in
                  (case provesTheRightInductiveCase(res_prop,uvar,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"inductive") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => (iarm_stack := LStack.pop(!iarm_stack);
                            let val conjunction = P.makeConjunction(ind_hyps)
                                val body = if null(ind_hyps) then res_prop else P.makeConditional(conjunction,res_prop)
                                val res = P.makeUGen(fresh_vars,body)
                            in res
                            end))
               end
          fun doNewClauses([],_,_) = propVal(P.makeUGen([uvar],body))
            | doNewClauses(clause::more_clauses,previous_clauses,ab) = 
                  let val res = doNewClause(clause,previous_clauses,ab) 
                  in
                     doNewClauses(more_clauses,clause::previous_clauses,ab) 
                  end
      in
         doNewClauses(new_clauses,[],ab)
      end
  | evDed(A.structureCasesDed({prop,clauses,pos,term}),env:value_environment ref,ab) = 
    (case term of 
     SOME(dt_exp) =>  
      let fun prefix(n) = let val str = "first"
                          in
                             "Invalid argument given to the datatype-cases form.\n"^
                             "In every deduction of the form (datatype-cases E v D), the "^
                             "value of E must\nbe a sentence P and v must be (or denote) a variable"  
                          end
          fun msg1(n,var_str,P_str,obtype) = prefix(n)^". In addition, the\nsort of v in P must be a datatype."^ 
                                   " But here "^"v and P are "^var_str^" and\n"^P_str^
                                   "\nrespectively, where "^var_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a datatype"
          fun msg2(str1,str2) = "Ill-formed datatype-cases deduction---the given patterns do not exhaust\nthe "^
                                "datatype "^str1^". Here is a counter-example: "^str2
          fun msg3(n,v) = prefix(n)^".\nBut here E was a "^valLCTypeAndString(v)
          fun msg4(e) = "A variable was expected here"
          val dt_exp_pos = A.posOfExp(dt_exp)
          val var = (case evalExp(dt_exp,env,ab) of
                        termVal(t) => (case AT.isVarOpt(t) of
                                          SOME(v) => v
                                        | _ => evError(msg4(dt_exp),SOME(dt_exp_pos)))
                      | _ => evError(msg4(dt_exp),SOME(dt_exp_pos)))
          val var_term = AthTerm.makeVar(var)
          val body = let val pval = evalPhrase(prop,env,ab)
                            in
                              (case coerceValIntoProp(pval) of
                                  SOME(P) => P
                                 | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                            end 
          val var_type = ATV.getSort(var)
          val _ = if StructureAnalysis.isStructureType(var_type) then () else 
                  evError(msg1(2,Terms.printAthTermVar(var),prettyValToString(propVal(body)),Terms.printFTermSExp(var_type)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evalExp(e',env',ab)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,var_type,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,var_type) of
                      SOME(t) => evError(msg2(Terms.printFTermSExp(var_type),
                                              Terms.printAthTermSExp(t)),SOME(pos))
                    | _ => ())
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),ab) = 
               let val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
		                   let 
                                   in
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                   end
                                 else 
				    let
                                    in
                                      new_env_0
                                    end
                   val new_ab = ABaseAugment(ab,[Prop.makeEquality(var_term,pat_as_ath_term),Prop.makeEquality(pat_as_ath_term,var_term)])
                   val res_prop = (case evDed(ded,new_env,new_ab) of
                                      propVal(P) => P)
               in
                  (case provesTheRightInductiveCase(res_prop,var,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"structure-cases") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => P.makeUGen(fresh_vars,res_prop))
               end
          fun doNewClauses([],_) = propVal(body)
            | doNewClauses(clause::more_clauses,ab) = 
                  let val res = doNewClause(clause,ab) 
                  in
                     doNewClauses(more_clauses,ABaseInsert(res,ab))
                  end
      in
         doNewClauses(new_clauses,ab)
      end
    | NONE =>   
      let fun prefix(n) = let val str = "first"
                          in
                             "Invalid "^str^" argument given to the structure-cases form. "^
                             "In every deduction\nof the form (structure-cases E D), the "^
                             "value of E must be a sentence P of the form (forall v Q)"  
                          end
          fun msg1(n,var_str,P_str,obtype) = prefix(n)^".\nIn addition, the sort of v in Q must be a structure."^ 
                                   " But here\n"^"v and P are "^var_str^" and "^P_str^
                                   ", respectively, where "^var_str^" in "^P_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a structure"
          fun msg2(str1,str2) = "Ill-formed structure-cases deduction---the given patterns do not exhaust\nthe "^
                                "structure "^str1^". Here is a counter-example: "^str2
          fun msg3(n,v) = prefix(n)^".\nBut here E was a "^valLCTypeAndString(v)
          val (uvar,body) = let val pval = evalPhrase(prop,env,ab)
                            in
                              (case coerceValIntoProp(pval) of
				  SOME(P) => (case P.isUGen(P) of 
		                                 SOME(uv,ub) => (uv,ub)
					       | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                                 | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                            end 
          val uvar_sort = ATV.getSort(uvar)
          val _ = if StructureAnalysis.isStructureType(uvar_sort) then () else 
                  evError(msg1(2,ATV.toStringDefault(uvar),P.toString(body,makeVarSortPrinter()),
			  F.toStringDefault(uvar_sort)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evalExp(e',env',ab)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,uvar_sort,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,uvar_sort) of
                      SOME(t) => evError(msg2(F.toStringDefault(uvar_sort),
                                              AT.toStringDefault(t)),SOME(pos))
                    | _ => ())
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),ab) = 
               let val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
		                   let
                                   in
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                   end
                                 else 
				    let
                                    in
                                      new_env_0
                                    end
                   val new_ab = ab
                   val res_prop = (case evDed(ded,new_env,new_ab) of
                                      propVal(P) => P
                                    | _ => raise Basic.Never)
               in
                  (case provesTheRightInductiveCase(res_prop,uvar,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"structure-cases") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => P.makeUGen(fresh_vars,res_prop))
               end
          fun doNewClauses([],_) = propVal(P.makeUGen([uvar],body))
            | doNewClauses(clause::more_clauses,ab) = 
                  let val res = doNewClause(clause,ab) 
                  in
                     doNewClauses(more_clauses,ABaseInsert(res,ab))
                  end
      in
         doNewClauses(new_clauses,ab)
      end)
  | evDed(A.byCasesDed({disj,from_exps,arms,pos}),env,ab) = 
	let val disj_val = evalPhrase(disj,env,ab)
	    val disj_prop = (case coerceValIntoProp(disj_val) of
           			SOME(P) => P
			      | _ => evError("A sentence (disjunction) was expected here. Instead, a\n"^
					     "value of type "^valLCTypeAndString(disj_val)^" was found.",
                	                      SOME(A.posOfPhrase(disj))))
	    val disj_holds = if ABase.isMember(disj_prop,ab) orelse A.isDeduction(disj) then true
			     else
				(case from_exps of 
				   NONE => evError("By-cases disjunction doesn't hold",
					           SOME(A.posOfPhrase(disj)))
			          | SOME(exps) => 
				 let fun er() = evError("Error in cases proof: unable to "^
					         "automatically derive the disjunction "^
						  prettyValToStringNoTypes(disj_val),SOME(pos))
				    val atp_call = A.methodAppDed({
							method=A.idExp({msym=msym N.vpfPrimMethod_symbol,no_mods=true,mods=[],sym=N.vpfPrimMethod_symbol,pos=pos}),
					    args=[disj,A.exp(A.listExp({members=(map A.exp exps),
							pos=A.dum_pos}))],pos=pos})
				     val atp_val = evDed(atp_call,env,ab) handle EvalError(str,_) => 
						 (print(str);raise Basic.Never)
				 in
				   (case coerceValIntoProp(atp_val) of
				       SOME(dp) => if P.alEq(dp,disj_prop) then true else er()
				     | _ => er())
				 end)
	    val alts = P.getDisjuncts(disj_prop)
	    fun getAltProp(v,pos) = (case coerceValIntoProp(v) of 
				        SOME(P) => P
				      | _ => evError("A sentence was expected here. Instead, a\n"^
					             "value of type "^valLCTypeAndString(v)^" was found.",
                	                             SOME(pos)))
	    fun casesLeftUntreated(P) = evError("Non-exhaustive cases proof.\nThis case was not "^
				                "considered:\n"^P.toPrettyString(0,P,makeVarSortPrinter()),
					        SOME(pos))
	    fun gratuitousCase(P,pos) = evError("Gratuitous case considered in proof by cases:\n"^
						 P.toPrettyString(0,P,makeVarSortPrinter()),
						SOME(pos))
	    val {case_name,alt=first_case,proof=first_ded}:A.case_clause = hd arms
	    val (first_case_considered,conclusion,cases_left) = 
		  let val first_prop = getAltProp(evalExp(first_case,env,ab),A.posOfExp(first_case)) 
                      val (vmap,mmap) = getValAndModMaps(!env)
   		      val env' = (case case_name of
			             SOME({name,...}) => ref(valEnv({val_map=Symbol.enter(vmap,name,propVal(first_prop)),mod_map=mmap}))
				   | _ => env)
		      val first_concl = (case coerceValIntoProp(evDed(first_ded,env',
						ABaseInsert(first_prop,ab))) of
					   SOME(P) => P | _ => raise Basic.Never)
		      val (cases_left,is_mem) = Basic.removeAndCheckMemEq(first_prop,alts,P.alEq)
		  in
		     (first_prop,first_concl,cases_left) 
		  end
	    fun checkConclusion(d,case_considered, new_env) = 
              let val conc = evDed(d,new_env,ABaseInsert(case_considered,ab))
              in
		 (case coerceValIntoProp(conc) of
		     SOME(P) => if P.alEq(P,conclusion) then ()
				else let val varSortPrinter = makeVarSortPrinter()
				     in
					evError("The sentence "^
					     P.toPrettyString(0,conclusion,varSortPrinter)^
					     " was expected here.\n"^
					     "Instead, the following sentence was produced: "^
					     P.toPrettyString(0,P,varSortPrinter),
					     SOME(A.posOfDed(d)))
				     end
		   | _ => raise Basic.Never)
	      end 
	    fun doArms([],cases_considered,cases_left) = if Basic.subsetEq(cases_left,cases_considered,P.alEq)
							 then propVal(conclusion)
							 else casesLeftUntreated(hd cases_left)
	      | doArms((cc:A.case_clause as {case_name,alt,proof})::rest,
			cases_considered,cases_left) =
		  let val new_case_val = evalExp(alt,env,ab)
					 handle EvalError(str,_) => 
						 (print(str);raise Basic.Never)
					      |   ObTypeCheckFailure => 
						    (print("\nSort failure\n");raise Basic.Never)
                                              | _ => (print("\n Unknown error.\n"); raise Basic.Never)
		      val new_case = getAltProp(new_case_val,A.posOfExp(alt)) 
                      val (vmap,mmap) = getValAndModMaps(!env)
   		      val new_env = (case case_name of
			             SOME({name,...}) => ref(valEnv({val_map=Symbol.enter(vmap,name,propVal(new_case)),mod_map=mmap}))
				   | _ => env)
		      val (cases_left',is_mem) = Basic.removeAndCheckMemEq(new_case,cases_left,P.alEq)
		      val _ = checkConclusion(proof,new_case,new_env)
		  in
		      doArms(rest,new_case::cases_considered,cases_left') 
		  end
	in
	   doArms(tl arms,[first_case_considered],cases_left)
	end
  | evDed(A.checkDed({clauses,pos}),env,ab) = 
       (case evalDCheckClauses(clauses,env,ab) of
           SOME(d) => evDed(d,env,ab)
         | _ => evError("dcheck failed: no alternative holds",SOME(pos)))

  | evDed(A.beginDed({members,pos}),env,ab) = 
     let fun doAll([d],ab') = evDed(d,env,ab')
           | doAll(d1::(rest as (d2::more)),ab') = 
               (case evDed(d1,env,ab') of
                   propVal(p) => doAll(rest,ABaseInsert(p,ab'))
                 | _ => evError("Impossible error---a component deduction of a dbegin "^
                                "failed to produce a sentence",SOME(A.posOfDed(d1))))
         in  
           doAll(members,ab)
     end           
  | evDed(A.byDed({wanted_res,body,pos,conc_name}),env,ab) =  
      let fun msg(P,Q) = "Failed conclusion annotation.\nThe expected conclusion was:\n"^ 
                          P.toPrettyString(0,P,makeVarSortPrinter())^"\nbut the obtained result was:\n"^
                          P.toPrettyString(0,Q,makeVarSortPrinter())
          fun msg2(v) = "In a deduction of the form (E BY D), the value of E must be a sentence,\n"^
                        "but here it was a "^valLCTypeAndString(v)
          fun indent(level, s) = if level = 0 then () else (print(s); indent(level - 1, s))
	  fun tracemsg1(level) = (A.posToString pos)^":Proving at level "^Int.toString(level)^":\n"
	  fun tracemsg2(level) = "Done at level "^Int.toString(level)^".\n"
	  fun pprint(n, P) = P.toPrettyString(n,P,makeVarSortPrinter())
          fun openTracing(P,level) = if (!Options.conclude_trace) then
                                     (level := !level + 1; 
                                      print((A.posToString pos)^":Proving at level "^Int.toString(!level)^":\n");
                                      indent(!level,"    "); 
                                      print("  "^pprint(4*(!level)+2,P)^"\n"))
                                     else ()
          fun closeTracing(level,success) = if (!Options.conclude_trace) then 
                                                 (level := !level - 1;
                                                   indent(!level+1,"    ");
                                                   if success then print("Done at level "^Int.toString(!level+1)^".\n")
                                                         else print("Failed at level "^Int.toString(!level+1)^".\n"
                                                                    ^"in dtry clause at "^(A.posToString pos)^".\n"))
                                              else ()
          val wv = evalExp(wanted_res,env,ab)
          val env' = (case conc_name of 
                         SOME({name,...}) => let val (vmap,mmap) = getValAndModMaps(!env)
                                             in
                                                ref(valEnv({val_map=Symbol.enter(vmap,name,wv),mod_map=mmap}))
                                              end
                       | _ => env)
      in
         (case coerceValIntoProp(wv) of 
             SOME(P) => (openTracing(P,level);
                         case (evDed(body,env',ab) 
                               handle ex => (closeTracing(level,false);raise ex)) of
                            res as propVal(Q) => if Prop.alEq(P,Q)
					         then (closeTracing(level,true);propVal(P))
                                                 else (closeTracing(level,false);
                                                       evError(msg(P,Q),SOME(pos))))
           | _ => evError(msg2(wv),SOME(A.posOfExp(wanted_res))))
      end
  | evDed(A.pickAnyDed({eigenvars,body,pos}),env,ab) = 
        let val names = map #name eigenvars
	    fun makeFreshVar({name,pos,sort_as_sym_term=NONE,sort_as_fterm=NONE,...}:A.possibly_typed_param) = 
	    	ATV.freshWithPrefix(Symbol.name(name)^"_")
	      | makeFreshVar({name,pos,sort_as_sym_term=SOME(sym_term),sort_as_fterm=NONE,sort_as_exp=SOME(se),...}) = 
	      	   let val sort_string = AthStringToMLString(evalExp(se,env,ab))
                       fun isVar(str) = let val str_lst = explode str
		       	   	        in not(null(str_lst)) andalso 
					   hd(str_lst) = Names.sort_variable_prefix_as_char
					end
                   in
                       (case Terms.parseSymTerm(sort_string,isVar) of 
                           SOME(sort_as_sym_term) => let val fsort = Terms.carbonSymTermToFTerm(sort_as_sym_term)
                                                     in ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",fsort)
                                                     end)
                   end
              | makeFreshVar({name,pos,sort_as_sym_term,sort_as_fterm=SOME(sort),...}) = 
		  (let val res = ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",sort)
		   in 
		      res
		   end)
	    val fresh_vars = map makeFreshVar eigenvars 
            val (vmap,mmap) = getValAndModMaps(!env)
            val new_env = ref(valEnv({val_map=enterLst(vmap,names,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
            val res = evDed(body,new_env,ab)
        in        
               case res of
                  propVal(p) => let val P_safe = P.makeUGen(fresh_vars,p)
				    val P_preferable = SOME(P.renameQProp(List.map Symbol.name names,P_safe))
						       handle _ => NONE
			        in
				   (case P_preferable of
				       SOME(Q) => if P.alEq(P_safe,Q) then propVal(Q) 
						  else propVal(P_safe)
				     | _ => propVal(P_safe))
				end
        end
  | evDed(A.pickWitnessDed({ex_gen,var_id,inst_id,body=main_body,pos}),env,ab) =
        let val egv = evalPhrase(ex_gen,env,ab)
	    fun showError() = evError("In a deduction of the form (pick-witness I F D), the value "^
		                      "of F must be an exisentially\nquantified sentence---but here "^
                                      "it was a "^valLCTypeAndString(egv),SOME(A.posOfPhrase(ex_gen)))
            val (ex_gen_val,ex_gen_var,ex_gen_body,new_ab) = 
                   (case coerceValIntoPropVal(egv) of 
                       SOME(v as propVal(egp)) => 
			 (case P.isEGen(egp) of 
			   SOME(ev,ebody) => 
			       (v,ev,ebody,(case ex_gen of 
   					     A.ded(_) => ABaseInsert(egp,ab)
                                           | _ => ab))
                           | _ => (case P.isEGenUnique(egp) of
				      SOME(ev,ebody) => 
					(v,ev,ebody,(case ex_gen of 
                                                       A.ded(_) => ABaseInsert(egp,ab)
                                                     | _ => ab))
                                    | _ => showError()))
                     | _ => showError())
            val ex_gen_var_sort = ATV.getSort(ex_gen_var)
            val unique_name = Symbol.symbol("!1")
            val fresh_var_v = AthTermVar.freshWithSortAndPrefix(Symbol.name(var_id)^"_",ex_gen_var_sort)
            val fresh_var = AT.makeVar(fresh_var_v)
            val (vmap,mmap) = getValAndModMaps(!env)
            val vmap' = enterLst(vmap,[unique_name,var_id],[ex_gen_val,termVal(fresh_var)])
            val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
            val id_prop = P.replaceVarByVar(ex_gen_var,fresh_var_v,ex_gen_body)
            val new_env' = (case inst_id of
		               SOME(id) => ref(valEnv({val_map=enterLst(vmap',[id],[propVal(id_prop)]),mod_map=mmap}))
                             | _ => new_env)
            val new_ded = A.withWitnessDed({eigenvar_exp=A.idExp({msym=msym var_id,mods=[],no_mods=true,sym=var_id,pos=A.posOfPhrase(ex_gen)}),
                                            ex_gen=A.exp(A.idExp({msym=msym unique_name,mods=[],no_mods=true,sym=unique_name,pos=A.posOfPhrase(ex_gen)})),
                                            body=main_body,pos=pos})
        in
           evDed(new_ded,new_env',new_ab)
        end    
  | evDed(A.tryDed({choices,pos}),env,ab) =
       let fun tryDeds([]) = NONE
             | tryDeds(d::more) = 
                   (case (SOME(evDed(d,env,ab)) handle _ => NONE) of 
                       NONE => tryDeds(more)
                     | r =>  r)
           in
             (case tryDeds(choices) of
                NONE => evError("Try deduction error; all "^ 
                                " alternatives failed.\n",SOME(pos))
               | (SOME v) => v)
       end
  | evDed(d as A.pickWitnessesDed({ex_gen,var_ids,...}),env,ab) = 
        let val egv = evalPhrase(ex_gen,env,ab)
	    fun showError() = evError("In a deduction of the form (pick-witnesses I1 ... In F D), "^
			 	      "the value of F must be an exisentially\nquantified "^
				      "sentence---but here it was a "^
                                      valLCTypeAndString(egv),SOME(A.posOfPhrase(ex_gen)))
            val (ex_gen_val,ex_gen_vars,ex_gen_body,new_ab) = 
                   (case coerceValIntoPropVal(egv) of 
                       SOME(v as propVal(egp)) =>
			 (case P.isEGen(egp) of 
			    SOME(ev,ebody) => 
	                         let val evars = getFrontQuantVars(egp)
				 in 
	                           (v,evars,ebody,(case ex_gen of 
        	                                     A.ded(_) => ABaseInsert(egp,ab)
                	                           | _ => ab))
				 end
		         | _ => (case P.isEGenUnique(egp) of
				    SOME(ev,ebody) => 
		                         let val evars = getFrontQuantVars(egp)
					 in 
		                           (v,evars,ebody,(case ex_gen of 
                	                             A.ded(_) => ABaseInsert(egp,ab)
                        	                   | _ => ab))
					 end
		                     | _ => showError()))
		    | _ => showError())
	  val (wit_count,evar_count) = (length(var_ids),length(ex_gen_vars))
          val _ = if wit_count >  evar_count then
		      evError("More witnesses ("^(Int.toString(wit_count))^") requested than\n"^
			      "could be obtained from the sentence:\n "^(prettyValToString(ex_gen_val))^
			      "\nThe above is existentially quantified over only "^(Int.toString(evar_count))^
			      (if evar_count = 1 then " variable" else " variables"),
			      SOME(A.posOfPhrase(ex_gen)))
		  else ()
       in
  	 evDed(desugarPW(d,env,ab,evalPhrase),env,new_ab)
       end
  | evDed(A.genOverDed({eigenvar_exp,body,pos,...}),env,ab) =  
      let fun msg(vstr) = "Failed universal generalization.\nThe eigenvariable "^vstr^
                          " occurs free in the current assumption base"
          fun emsg1(v) = "In a deduction of the form (generalize-over E D), the value of E must be "^
                         "a variable---but here it was a "^valLCTypeAndString(v)
          fun emsg2(v) = "In a deduction of the form (generalize-over E D), the value of E must be "^
                         "a variable---but here it was the non-variable term "^valToString(v)
          fun printVar(v) = Names.variable_prefix^(ATV.toStringDefault(v))
          val ev = evalExp(eigenvar_exp,env,ab)
      in
         case coerceValIntoTermVal(ev) of 
            SOME(termVal(t)) => 
                 (case AT.isVarOpt(t) of
                     SOME(v) => 
                         if Ab.occursFreeUpToSubsorting(v,ab) then
                            evError(msg(printVar(v)),SOME(A.posOfExp(eigenvar_exp)))
                         else 
                            let val res = evDed(body,env,ab)
                                val res_prop = (case coerceValIntoPropVal(res) of 
                                                   SOME(propVal(P)) => let val res = propVal(P.makeUGen([v],P))
 						                                       handle Basic.FailLst(msgs) => 
                                                                                              evError(Basic.failMsgsToStr(msgs),
                                                                                                      SOME(pos))
                                                                       in 
                                                                          res
                                                                       end                                     
                                                 | _ => evError("Impossible error encountered in universal "^
                                                                "generalization---the body of the deduction "^
                                                                "failed to produce a sentence",
                                                                SOME(A.posOfDed(body))))
                            in
                               res_prop
                            end
                   | _ => evError(emsg2(ev),SOME(A.posOfExp(eigenvar_exp))))
           | _ => evError(emsg1(ev),SOME(A.posOfExp(eigenvar_exp)))
      end 
  | evDed(A.withWitnessDed({eigenvar_exp,ex_gen,body,pos}),env,ab) = 
     let fun msg(vstr) = "Failed existential instantiation---the witness variable "^
                         "\noccurs free in the current assumption base"
         fun emsg1(v) = "In a deduction of the form (with-witness E F D), the value of E must "^
                        "be a variable---but here it was a "^valLCTypeAndString(v)
         fun emsg2(v) = "In a deduction of the form (with-witness E F D), the value of E must "^
                        "be a variable---but here it was the non-variable term "^valToString(v)
         val ev = evalExp(eigenvar_exp,env,ab)
     in
       case coerceValIntoTerm(ev) of
        SOME(t) => 
         (case AT.isVarOpt(t) of
            SOME(fresh_var) => 
              if Ab.occursFree(fresh_var,ab) then
                 evError(msg(AthTermVar.name(fresh_var)),SOME(A.posOfExp(eigenvar_exp)))
              else 
               let val egenv = evalPhrase(ex_gen,env,ab)
               in
                (case coerceValIntoProp(egenv) of  
                    SOME(specP) => 
		     (case P.isEGen(specP) of 
	               SOME(v,pbody) =>
                         if A.isDeduction(ex_gen) orelse ABase.isMember(specP,ab) then
                            let val pbody' = P.replace(v,AT.makeVar(fresh_var),pbody)
                                val pbody_components = Prop.decomposeConjunctions(pbody')
                                val new_ab = ABaseAugment(ab,pbody_components)
                                val final_res = evDed(body,env,new_ab)
                            in
                                (case final_res of 
                                   v as propVal(p') => 
                                     if P.occursFree(fresh_var,p') then 
                                         evError("Failed existential instantiation---the witness variable "^
                                                  "\noccurs free in the resulting sentence",SOME(pos))
                                     else v
                                 | _ => evError("Impossible error encountered in existential instantiation"^
                                                "the deduction body did not produce a sentence",
                                                SOME(A.posOfDed(body))))
                            end
                         else
			   let val specP_str = P.toPrettyString(0,specP,makeVarSortPrinter())
			   in
                             evError("Existential sentence to be instantiated is not in\nthe assumption base: "^
                                     (Util.decide(specP_str,16)),SOME(A.posOfPhrase(ex_gen)))
			   end
                       | _ => 
                        (case P.isEGenUnique(specP) of 
		         SOME(v,pbody) =>
                         if A.isDeduction(ex_gen) orelse ABase.isMember(specP,ab) then
                            let val fresh_term = AT.makeVar(fresh_var)
                                val instantiated_ex_prop = P.replace(v,fresh_term,pbody)
                                val new_var = ATV.freshWithSort(ATV.getSort(fresh_var))
                                val new_term = AT.makeVar(new_var)
                                val new_prop = P.replace(v,new_term,pbody)
                                val eq_prop1 = P.makeEquality(new_term,fresh_term)
                                val eq_prop2 = P.makeEquality(fresh_term,new_term)
                                val uniqueness_prop1 = P.makeUGen([new_var],P.makeConditional(new_prop,eq_prop1))
                                val uniqueness_prop2 = P.makeUGen([new_var],P.makeConditional(new_prop,eq_prop2))
                                val new_ab = ABaseAugment(ab,[uniqueness_prop1,uniqueness_prop2])
                                val final_res = evDed(body,env,new_ab)
                            in        
                                  (case final_res of 
                                      v as propVal(p') => 
                                        if P.occursFree(fresh_var,p') then
                                           evError("Failed existential instantiation---the witness variable "^
                                                  "\noccurs free in the resulting "^
                                                  "sentence",SOME(pos))
                                        else v
                                    | _ => evError("Impossible error encountered in existential instantiation"^
                                                   "---the deduction body did not produce a sentence",
                                                   SOME(A.posOfDed(body))))
                            end
                         else
                             evError("Existential sentence to be instantiated is not in the assumption base: "^
                                      P.toPrettyString(0,specP,makeVarSortPrinter()),
						       SOME(A.posOfPhrase(ex_gen)))))
                  | _ => evError("In a deduction of the form (with-witness E F D) or (pick-witness E F D), the "^
                                 "value of F must be an existentially quantified\nsentence---but here"^
                                 " it was a "^valLCTypeAndString(egenv),SOME(A.posOfPhrase(ex_gen))))
               end
          | _ => evError(emsg2(ev),SOME(A.posOfExp(eigenvar_exp))))
      | _ => evError(emsg1(ev),SOME(A.posOfExp(eigenvar_exp)))
     end
  | evDed(A.letRecDed({bindings,body,pos}),env,ab) = 
       let val rec_env = ref(!env)
           fun getVals([],map) = map 
             | getVals((b:A.binding as {bpat,def,pos})::more,map) = 
                let val mv = evalPhrase(def,rec_env,ab)
                in
                  (case matchPat(mv,bpat,makeEvalExpFunction (rec_env,ab)) of 
                      SOME(map',_) => getVals(more,Symbol.augment(map,map'))
                    | _ => evError("dletrec pattern failed to match the corresponding value, the\n "^
                                   (valLCTypeAndStringNoColon mv),
                                   SOME(A.posOfPat(bpat))))
                end
           val pmap = getVals(bindings,S.empty_mapping)

           val (vmap,mod_map) = getValAndModMaps(!env)
           val new_env = valEnv({val_map=Symbol.augment(vmap,pmap),mod_map=mod_map})

           val _ = rec_env := new_env
           in
              evDed(body,ref(new_env),ab)
       end
  | evDed(A.fromDed({conclusion,premises,pos}),env,ab) = 
       let fun getProps(val_lst,list_name,pos,env) = 
                 let fun msg(v,i) = "Wrong kind of value found in the "^ordinal(i)^
				     " position of "^list_name^"---"^expectInOneLine(propLCType,v)
                     fun getProps([],results,i) = rev results
                       | getProps(v::rest,results,i) = 
                           (case coerceValIntoProp(v) of 
                              SOME(P) => getProps(rest,P::results,i+1)
                       | _ => evError(msg(v,i),SOME(pos)))
                  in
                     getProps(val_lst,[],1)
                  end
       in
         (case coerceValIntoProp(evalExp(conclusion,env,ab)) of 
             SOME(P) => (case evalExp(premises,env,ab) of
                          listVal(pvals) => 
                            let val premise_props = getProps(pvals,"the list argument of "
                                                                  ^" FROM deduction ",
							     A.posOfExp(premises),env)
                            in 
			       unitVal
                            end)
            | _ => raise Basic.Never)
       end
  | evDed(A.infixAssumeDed({bindings,body,pos}),env,ab) = 
	let fun getPropsAndEnv([],props,env) = (props,env)
	      | getPropsAndEnv((b:A.binding as {bpat,pos,def,...})::rest,props,env) = 
	                let val pval = evalPhrase(def,env,ab)
			in
			  (case coerceValIntoProp(pval) of
	                      SOME(p) => 
                                 (case matchPat(pval,bpat,makeEvalExpFunction (env,ab)) of 
                                     SOME(map,_) => let val (vmap,mmap) = getValAndModMaps(!env)
                                                      val env' = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                                  in
                                                     getPropsAndEnv(rest,p::props,env')
                                                  end
                                   | _ => evError("Assume pattern failed to match the corresponding value, the\n "^
                                                  (valLCTypeAndStringNoColon pval),
                                                  SOME(A.posOfPat(bpat))))
	                    | _ => evError("A sentence (hypothesis) was expected here. Instead, a\n"^
					   "value of type "^valLCTypeAndString(pval)^" was found.",
                	                   SOME(A.posOfPhrase(def))))
			end
            val (props,new_env) = getPropsAndEnv(bindings,[],env)
	    val hyps = rev(props)
            val hyps' = Basic.flatten (map Prop.decomposeConjunctions hyps)
	    val res_val = evDed(body,new_env,ABase.augment(ab,hyps'))
            in
	      (case coerceValIntoProp(res_val) of
	         SOME(q) => let val conj = (case hyps of
					      [P] => P
					    |  _  => Prop.makeConjunction(hyps))
			    in
			       propVal(Prop.makeConditional(conj,q))
			    end
               | _ => evError("Impossible error encountered in assume deduction: the body of "^
                              "the deduction did not produce a sentence",SOME(A.posOfDed(body))))
	   end
*******************************************************************************************************************************************************************************)
and 
    evalMethodApp(method,args:A.phrase list,env:SemanticValues.value_environment ref,ab:ABase.assum_base,pos:A.position) = 
     (let val app_pos = pos 
           fun getArgVals([],arg_vals,ded_vals) = (rev(arg_vals),ded_vals)
             | getArgVals(A.exp(e)::rest,arg_vals,ded_vals) = 
                        getArgVals(rest,evalExp(e,env,ab)::arg_vals,ded_vals)
             | getArgVals(A.ded(d)::rest,arg_vals,ded_vals) = 
                       (case evDed(d,env,ab) of
                           (propVal(dprop),{proof,conc,fa,...}) => 
                              getArgVals(rest,propVal(dprop)::arg_vals,dprop::ded_vals)
                         | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                        "argument of a method application---the deduction did not "^
                                        "produce a sentence!",SOME(A.posOfDed(d))))
           fun getArgValsAndPositions() = 
                let val pos_ar = Array.array(length(args)+2,A.dum_pos)
                    val _ = Array.update(pos_ar,0,app_pos)
                    val _ = Array.update(pos_ar,1,A.posOfExp(method))
                    fun doArgs([],arg_vals,ded_vals,i) = (rev(arg_vals),ded_vals,pos_ar)
                      | doArgs(A.exp(e)::rest,arg_vals,ded_vals,i) = 
                          (Array.update(pos_ar,i,A.posOfExp(e));
                           doArgs(rest,evalExp(e,env,ab)::arg_vals,ded_vals,i+1))
                      | doArgs(A.ded(d)::rest,arg_vals,ded_vals,i) = 
                          (Array.update(pos_ar,i,A.posOfDed(d));
                           (case evDed(d,env,ab) of
                               (propVal(dprop),{proof,conc,fa,...}) => 
                                 doArgs(rest,propVal(dprop)::arg_vals,dprop::ded_vals,i+1)
                             | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                             "argument of a method application---the deduction did not "^
                                             "produce a sentence",SOME(A.posOfDed(d)))))
                in
                   doArgs(args,[],[],2)
                end
       in
          (case evalExp(method,env,ab) of 
               closMethodVal(A.methodExp({params,body,pos=mexp_pos,name=rname,...}),clos_env) =>
                       let val (arg_vals,ded_vals) = getArgVals(args,[],[])
                           val str_msg = if (!rname) = "" then "in method call" else "to "^(!rname)
                           val (vmap,mmap) = getValAndModMaps(!clos_env)
                           val new_env = ref(valEnv({val_map=enterParamValLstWithPositionalErrorChecking(vmap,params,arg_vals,str_msg,app_pos),mod_map=mmap}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
                           val _ = if !Options.stack_trace then  
                                       addFrame(frame({call_pos=app_pos,call_file="",
                                                       lambda=MethClos({clos_name=(!rname),
                                                                        def_pos=mexp_pos,
                                                                        def_file=""})}))
                                   else
                                       if !Options.detailed_stack_trace then  
                                          addFrame(detailedFrame({call_pos=app_pos,call_file="",
                                                                 lambda=MethClos({clos_name=(!rname),
                                                                                  def_pos=mexp_pos,
                                                                                  def_file=""}),
                                                                 arg_vals=arg_vals}))
                                       else ()
                           val _ = addPos(!rname,app_pos)
                       in
                         evDed(body,new_env,new_ab)
                       end  
               | methodVal(f,string) => 
                    (let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                          val new_ab = ABaseAugment(ab,ded_vals) 
                          val _ = if !Options.stack_trace then 
                                     addFrame(frame({call_pos=app_pos,call_file="",
                                                     lambda=MethVal({name=""})}))
                                  else
                                     if !Options.detailed_stack_trace then 
                                        addFrame(detailedFrame({call_pos=app_pos,call_file="",
                                                                lambda=MethVal({name=""}),
                                                                arg_vals=arg_vals}))
                                     else ()
                      in 
                         (f(arg_vals,env,new_ab),makeAlphaDed())
                      end handle PrimError(msg) => evError(msg,SOME(app_pos)))
               | primUMethodVal(f,code) => 
                                      let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                                      in 
                                        if not(length(arg_vals)  = 1) then 
                                           evError(wrongArgNumber(S.name(code),length(arg_vals),1),getPosOpt(pos_array,0))
                                        else ((f(hd(arg_vals),env,ab),makeAlphaDed()) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | primBMethodVal(f,code) => 
                                      let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                                      in 
                                        if not(length(arg_vals)  = 2) then 
                                           evError(wrongArgNumber((S.name code),length(arg_vals),2),getPosOpt(pos_array,0))
                                        else ((f(hd(arg_vals),hd(tl(arg_vals)),env,ab),makeAlphaDed()) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                           val _ =  if not(length(arg_vals)  = 2) then 
                                       evError(wrongArgNumber(!name,length(arg_vals),2),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s1,hd(arg_vals))
                           val vm' = Symbol.enter(vm,s2,hd(tl(arg_vals)))
                           val new_env = ref(valEnv({val_map=vm',mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
                       in
                          evDed(d,new_env,new_ab)
                       end  
               | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                           val _ =  if not(length(arg_vals)  = 1) then 
                                       evError(wrongArgNumber(!name,length(arg_vals),1),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s,hd(arg_vals))
                           val new_env = ref(valEnv({val_map=vm,mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
                       in
                          evDed(d,new_env,new_ab)
                       end  
               | v => evError("The leftmost expression of a method application "^
                              "must produce a method---here it produced a "^valLCTypeAndString(v),
                              SOME(A.posOfExp(method))))
       end)
in
    fn (d,env,ab) => (evDed(d,env,ab))
end
 
end (* of structure Alpha *) 



