(*=================================================================================

Proof evaluation with type-alpha certificate production. 

=======================================================================*)

structure Alpha = 

struct

structure S = Symbol
structure A = AbstractSyntax
structure AT = AthTerm
type prop = Prop.prop
type symbol = S.symbol
type variable = AthTerm.variable 

open Semantics

datatype hypothesis = hypothesis of symbol option * prop 
datatype alpha_val = term of AthTerm.term | sent of prop | alpha_list of alpha_val list 

datatype certificate = ruleApp of {rule:symbol, args: alpha_val list}
                     | assumeProof of {hyp: hypothesis, body: certificate}
                     | supAbProof of {hyp: hypothesis, body: certificate}
                     | composition of {left: certificate, right: certificate}
                     | pickAny of {eigen_var: symbol, actual_fresh: variable, body: certificate}
                     | conclude of {expected_conc: prop, body: certificate}
                     | block of certificate list 

val trivial_cert = ruleApp({rule=S.symbol("TRIVIAL_RULE"),args=[]})

fun isRuleApp(rule_name,ruleApp({rule,...})) = rule_name = (S.name rule)
  | isRuleApp(_) = false 

fun simpleCert(ruleApp(_)) = true
  | simpleCert(_) = false 

fun compsToBlocks(D) = 
  let fun B(composition({left,right})) = (B left)@(B right)
	| B(D) = [D] 
      fun c2b(D as composition(_)) = block(map c2b (B D))
	| c2b(assumeProof({hyp,body})) = assumeProof({hyp=hyp,body=c2b(body)})
	| c2b(supAbProof({hyp,body})) = supAbProof({hyp=hyp,body=c2b(body)})
	| c2b(pickAny({eigen_var,actual_fresh,body})) = pickAny({eigen_var=eigen_var,actual_fresh=actual_fresh,body=c2b(body)})
	| c2b(conclude({expected_conc,body})) = conclude({expected_conc=expected_conc,body=c2b(body)})
	| c2b(block(Ds)) = block(map c2b Ds)
	| c2b(D) = D
  in
     c2b(D)
  end

fun certToStringNaive(D) = 
  let fun argToString(term(t)) = AT.toStringDefault(t)
        | argToString(sent(p)) = Prop.makeTPTPPropSimple(p)
        | argToString(alpha_list(vals)) = Basic.printListStr(vals,argToString,", ")
      fun argsToString(args) = Basic.printListStr(args,argToString,", ")
      fun f(ruleApp({rule,args,...})) = "[" ^ (S.name rule) ^ " on " ^ (argsToString args) ^ "]"
	| f(assumeProof({hyp as hypothesis(name_opt,p),body})) = "assume " ^ (Prop.makeTPTPPropSimple p) ^ " { " ^ (f body) ^ " } "
        | f(supAbProof({hyp as hypothesis(name_opt,p),body})) = "suppose-absurd " ^ (Prop.makeTPTPPropSimple p) ^ " { " ^ (f body) ^ " } "
        | f(block(proofs)) = " BLOCK_START " ^ Basic.printListStr(proofs,f," || ") ^ " BLOCK_END "
	| f(composition({left,right})) = (f left) ^ " ;; " ^ (f right)
        | f(D) = "NOT IMPLEMENTED YET"
  in
     f(D)
  end

fun hasSubproof(D,pred) = 
   let fun find(D) = 
             if pred(D) then let val _ = print("\nFOUND TARGET PROOF: " ^ (certToStringNaive D) ^ "\n") in true end else 
             (case D of 
                 composition({left,right}) => find(left) orelse find(right)
  	       | assumeProof({body,...}) => find(body)
  	       | supAbProof({body,...}) => find(body)
  	       | pickAny({body,...}) => find(body)
  	       | conclude({body,...}) => find(body)
               | block(certs) => Basic.exists(certs,find)
	       | _ => false)
   in 
      find D 
   end
  
fun compFree(D) = 
     if hasSubproof(D,fn D' => (case D' of composition(_) => true | _ => false))
     then false else true 

fun getRuleName(rule_sym_name) = 
  if S.symEq(rule_sym_name,Names.true_intro_PrimMethod_symbol) then "true-introduction" else (S.name rule_sym_name)

fun certToString(D) = 
  let val spaces = Basic.spaces
      fun argToString(term(t)) = AT.toStringDefault(t)
        | argToString(sent(p)) = (P.toStringInfix p)
        | argToString(alpha_list(vals)) = Basic.printListStr(vals,argToString,", ")
      fun argsToString(args) = Basic.printListStr(args,argToString,", ")
      fun c2s(ruleApp({rule,args,...}),offset) = (spaces offset) ^ (getRuleName rule) ^ (if null(args) then "" else (" on " ^ (argsToString args)))
	| c2s(assumeProof({hyp as hypothesis(name_opt,p),body}),offset) = 
	      (spaces offset) ^ "assume " ^ (P.toStringInfix p) ^ " {\n" ^ (c2s(body,offset+2)) ^ "\n" ^ (spaces (offset + 1)) ^"}"
	| c2s(supAbProof({hyp as hypothesis(name_opt,p),body}),offset) =
	      (spaces offset) ^ "suppose-absurd " ^ (P.toStringInfix p) ^ " {\n" ^ (c2s(body,offset+2)) ^ "\n" ^ (spaces (offset + 1)) ^"}"
	| c2s(composition({left,right}),offset) = (c2s(left,offset+2)) ^ ";\n" ^ (c2s(right,offset+2)) 
	| c2s(block([D]),offset) = c2s(D,offset) 
	| c2s(block(D1::(more as (_::_))),offset) = c2s(D1,offset) ^ ";\n" ^ (c2s(block(more),offset))
	| c2s(conclude({expected_conc,body}),offset) = 
             (spaces offset) ^ (P.toStringInfix expected_conc) ^ " BY " ^ (if simpleCert(body) then c2s(body,0) else ("\n" ^ c2s(body,offset + 2)))
      val D' = compsToBlocks(D)
  in
    (case D' of 
        block(_)  => "\n{\n" ^ (c2s(D',2)) ^ "\n}"
      | _ => (c2s(D',0)))
  end              

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
      | "either" => let val disjuncts = (case props of 
                                           [disjunction] => Prop.getDisjunctsWithoutDups(disjunction) 
					 | _ => props)
                        val fas = Basic.filter(disjuncts,fn d => not(ABase.isMember(d,ab)))
                     in
                        fas
        	     end
      | _ => props        
  end

fun extractHypothesisName(map,pval,hypothesis_name) = 
  let val symbol_and_value_pairs = Symbol.listSymbolsAndImages(map)
  in
     (case Basic.constructiveExists(symbol_and_value_pairs,fn (symbol,value) => valEq(value,pval)) of
         SOME((symbol,_)) => hypothesis_name := S.name(symbol)
       | _ => ())
  end 

fun propUnion(prop_list_1,prop_list_2) = Basic.listUnion(prop_list_1,prop_list_2,Prop.alEq)
fun propDiff(prop_list_1,prop_list_2) = Basic.listDiff(prop_list_1,prop_list_2,Prop.alEq)
          
fun reconcile(tail_ded_info,[]) = tail_ded_info
  | reconcile(tail_ded_info,(ded_info_1 as {conc=conc1,fa=fa1,proof=proof1}:alpha_ded_info)::more) = 
        let val tail_res as {conc=tail_conc,fa=tail_fa,proof=tail_proof}:alpha_ded_info = reconcile(tail_ded_info,more)
        in
            if not(isRuleApp("claim",proof1)) andalso not(isRuleApp("true-intro",proof1)) then 
               let val final_fas = propUnion(fa1,propDiff(tail_fa,[conc1]))
                   val final_conc = tail_conc
                   val final_proof = composition({left=proof1,right=tail_proof})
               in
                  {conc=tail_conc,fa=final_fas,proof=final_proof}
               end 
           else
               tail_res
        end 

fun getNewEnvAndAb(dval,bpat,env1,ab1,ab) = 
    (case matchPat(dval,bpat,makeEvalExpFunction (env1,ab)) of 
        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                           val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                           val new_ab = (case dval of
                                            propVal(p) => ABaseAugment(ab1,Prop.decomposeConjunctions p)
                                          | _ => ab1)
                       in
                         (new_env,new_ab)
                       end 
      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                    (valLCTypeAndStringNoColon dval),
                    SOME(A.posOfPat(bpat))))
                   
val evalDedAlpha = 
let val iarm_stack:iarm_type LStack.stack ref = ref(LStack.empty)
    fun initIndStack() = iarm_stack := LStack.empty
    fun initCallStack() = call_stack := LStack.empty     
    fun getAlphaVal(v,method_name) = 
                        (case coerceValIntoTerm(v) of 
                             SOME(t) => term(t)
			   | _ => (case coerceValIntoProp(v) of
                                      SOME(p) => sent(p)
		  	            | _ => (case v of 
                                              listVal(vals) => alpha_list(map (fn v => getAlphaVal(v,method_name)) vals)
					     | _ => let val _ = print("\nUnexpected value type found as an argument to a call of this method: " ^ method_name ^ "; " ^ 
								      "a term or sentence was expected, but this was found instead:\n" ^ (valLCTypeAndStringNoColon v) ^ "\n")
                                                    in
                                                       Basic.fail("")
                                                    end)))
    fun evPhrase(phr,env,ab) = 
            (case phr of 
                A.ded(d) => (case evDed(d,env,ab) of (x,y) => (x,SOME(y)))
	      | A.exp(e) => (evalExp(e,env,ab),NONE))
and evDed(method_app as A.BMethAppDed({method,arg1,arg2,pos}),env,ab) = 
    ((let val head_val = evalExp(method,env,ab) 
      in
        (case head_val of
           primBMethodVal(M,method_sym) => 
                (let val method_name = S.name method_sym                     
                     val (v1,ded_1_info_opt) = evPhrase(arg1,env,ab)
                     val (v2,ded_2_info_opt) = evPhrase(arg2,env,ab)
(***
                     val _ = print("\nprimBMethodVal application of: " ^ method_name ^"\n")
***)
                     val arg_ded_infos = Basic.mapSelect(fn SOME(ded_info) => ded_info,[ded_1_info_opt,ded_2_info_opt],fn _ => true)
                     val ab' = if A.isDeduction(arg1) then putValIntoAB(v1,ab) else ab 
                     val ab'' = if A.isDeduction(arg2) then putValIntoAB(v2,ab') else ab' 
                     val res_val = M(v1,v2,env,ab'')
                     val (av1, av2) = (getAlphaVal(v1,method_name), getAlphaVal(v2,method_name))                      
                     val tail_ded_info = {conc=getProp(res_val),
					  fa=getFA(method_sym,[v1,v2],ab''),
					  proof=ruleApp({rule=method_sym,args=[av1,av2]})}
                     val ded_info = reconcile(tail_ded_info,arg_ded_infos)
                 in
                    (res_val,ded_info)
                 end handle PrimError(msg) => evError(msg,SOME(pos))
                          | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()
                                                in
                                                  evError(msg,SOME(right_pos))
                                                end)
	  | _ => evalMethodApp(method,[arg1,arg2],env,ab,pos))
      end))
  | evDed(A.UMethAppDed({method,arg,pos}),env,ab) = 
     ((let val head_val = evalExp(method,env,ab)
       in
         (case head_val of
              primUMethodVal(f,method_sym) => 
                                     (let val method_name = S.name method_sym                                          
                                          val (arg_val,ded_1_info_opt) = evPhrase(arg,env,ab)
(***
                                          val _ = print("\nprimUMethodVal application of: " ^ method_name ^"\n")
***)
                                          val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
                                          val conclusion_val = f(arg_val,env,ab')
                                          val ded_info = (case ded_1_info_opt of
                                                             NONE => {conc=getProp(conclusion_val),
 								      fa=getFA(method_sym,[arg_val],ab'),
								      proof=ruleApp({rule=method_sym,args=[getAlphaVal(arg_val,method_name)]})}
						           | SOME({conc=conc1,fa=fa1,proof=proof1,...}) =>
                           				       let val final_fas = propUnion(fa1,propDiff(getFA(method_sym,[arg_val],ab'),[conc1]))
							       in
								   {conc=getProp(conclusion_val),
								    fa=final_fas,
								    proof=composition({left=proof1,right=ruleApp({rule=method_sym,args=[getAlphaVal(arg_val,method_name)]})})}
							       end)
                                      in
                                         (conclusion_val,ded_info)
                                      end handle PrimError(msg) => evError(msg,SOME(pos))                                      
                                               | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()
                                                                     in
                                                                        evError(msg,SOME(right_pos))
                                                                     end)
            | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),clos_name) => 
                   let val (arg_val,ded_1_info_opt) = evPhrase(arg,env,ab)
                       (** val _ = print("\nAbout to execute a unary closure named " ^ (!clos_name) ^ " with this body:\n" ^ (A.unparseDed(d)) ^ "\nto this arg: " ^ (valToString arg_val) ^ "\n") **)
                       val vm = Symbol.enter(val_map,s,arg_val)
                       val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
                       val _ = addPos(!clos_name,pos)
                       (* val _ = print("\nclos_name: " ^ (!clos_name) ^ "\n") *)				     
                       val body_res as (body_conclusion_val,{conc=body_conc,fa=body_fa,proof=body_proof}) = evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab')
                   in
                     (case ded_1_info_opt of 
                        NONE => body_res
		      | SOME({conc=lemma_conc,fa=lemma_fa,proof=lemma_proof}) => 
                           (body_conclusion_val,{conc=body_conc,
						 fa=propUnion(lemma_fa,propDiff(body_fa,[lemma_conc])),
						 proof=composition({left=lemma_proof,right=body_proof})}))
                   end
	    | _ => evalMethodApp(method,[arg],env,ab,pos))
       end))
  | evDed(method_app as A.methodAppDed({method,args,pos=app_pos}),env,ab) = 
          evalMethodApp(method,args,env,ab,app_pos)
  | evDed(A.matchDed({discriminant,clauses,pos}),env,ab) =
      let val (discrim_value,ded_info_opt) = evPhrase(discriminant,env,ab)
          val disc_ded_infos = Basic.mapSelect(fn SOME(ded_info) => ded_info,
					       [ded_info_opt],
					       fn _ => true)
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
                          val result as (res_val,body_ded_info) = evDed(ded,new_env,new_ab)                          
                          val final_ded_info = reconcile(body_ded_info,disc_ded_infos)
                          (** val _ = print("\nFINAL MATCH RESULT OBTAINED: " ^ (valToString res_val) ^ "\n") **)
                      in
                         (res_val,final_ded_info)
                      end
                 | _ => tryClauses(more))
          in
            tryClauses(clauses)
      end                         
  | evDed(A.beginDed({members,pos}),env,ab) = 
     let fun doAll([d],ab) = evDed(d,env,ab)
           | doAll(d1::rest,ab) = 
               (case evDed(d1,env,ab) of
                   (propVal(p),{proof=proof1,conc=conc1,fa=fa1})  =>
                      (case doAll(rest,ABaseInsert(p,ab)) of 
                         (res_val,{proof=proof_rest,conc=conc_rest,fa=fa_rest}) => 
                           (res_val,{proof=composition({left=proof1,right=proof_rest}),
				     fa=propUnion(fa1,propDiff(fa_rest,[conc1])),
				     conc=conc_rest})))
         in  
           doAll(members,ab)
     end           
  | evDed(A.checkDed({clauses,pos}),env,ab) = 
       (case evalDCheckClauses(clauses,env,ab) of
           SOME(d) => evDed(d,env,ab)
         | _ => evError("dcheck failed: no alternative holds",SOME(pos)))
  | evDed(D as A.letDed({bindings,body,pos}),env,ab) =
       let fun doBindings([],env1,ab1,ded_infos) = 
                   let val result as (res_val,body_ded_info) = evDed(body,env1,ab1)
                       val final_ded_info = reconcile(body_ded_info,rev(ded_infos))
                   in
                       (res_val,final_ded_info)
                   end
	     | doBindings({bpat,def=A.ded(d),pos}::more,env1,ab1,ded_infos) = 
                  let val (ded_val,ded_info as {proof,conc,fa}) = evDed(d,env1,ab1)
                      val (env2,ab2) = getNewEnvAndAb(ded_val,bpat,env1,ab1,ab)                   
                  in
                     doBindings(more,env2,ab2,ded_info::ded_infos)
                  end 
	     | doBindings({bpat,def=A.exp(e),pos}::more,env1,ab1,ded_infos) = 
                 let val exp_val = evalExp(e,env1,ab1)
                     val (env2,_) = getNewEnvAndAb(exp_val,bpat,env1,ab1,ab)
                 in
                    doBindings(more,env2,ab1,ded_infos) 
                 end 
       in
          doBindings(bindings,env,ab,[])
       end
  | evDed(D as A.assumeDed({assumption,body,pos}),env,ab) = 
            let val (aval,_) = evPhrase(assumption,env,ab)
            in
               (case coerceValIntoProp(aval) of
                   SOME(antecedent) => 
                     let val asms = Prop.decomposeConjunctions(antecedent)
                         val ab' = ABase.augment(ab,asms)
                     in 
                       (case evDed(body,env,ab') of 
                         (body_val,body_ded_info as {proof=body_proof,conc=body_conc,fa=body_fa})  => 
                           (case coerceValIntoProp(body_val) of 
                              SOME(consequent) => let val conditional_conclusion = Prop.makeConditional(antecedent,consequent)
                                                      val final_ded_info = {proof=assumeProof({hyp=hypothesis(NONE,antecedent), body=body_proof}),
			 					            conc=conditional_conclusion,
									    fa=propDiff(body_fa,[antecedent])}
                                                  in
                                                    (propVal(conditional_conclusion),final_ded_info)
                                                  end
                             | _ => evError("In a deduction of the form (assume F D), the value of F"^ 
                                             " must\nbe a sentence, but here it was a "^valLCTypeAndString(aval),
                                             SOME(A.posOfPhrase(assumption)))))
                     end)
            end
  | evDed(A.absurdDed({hyp,body,pos}),env,ab) = 
         doSupposeAbsurd(hyp,NONE,body,pos,env,ab)
  | evDed(A.absurdLetDed({named_hyp,body,pos}),env,ab) = 
          let val (hyp_name_pat,hyp) = (#bpat(named_hyp),#def(named_hyp))
          in
                doSupposeAbsurd(hyp,SOME(hyp_name_pat),body,pos,env,ab)
          end
  | evDed(A.letRecDed({bindings,body,pos}),env,ab) = 
       let val rec_env = ref(!env)
           fun getVals([],map) = map 
             | getVals((b:A.binding as {bpat,def,pos})::more,map) = 
                let val (mv,_) = evPhrase(def,rec_env,ab)
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
  | evDed(A.assumeLetDed({bindings,body,pos}),env,ab) = 
           let fun getProp(F,is_ded,env,ab) = 
                  let val (Fval,_) = evPhrase(F,env,ab)
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
                         val new_ab = ABaseAugment(ab,asms')
                     in
                        evDed(body,env1,new_ab)
                     end
                  | doBindings({bpat,def,...}::more,assumptions,env1) = 
                        let val new_assumption = getProp(def,false,env1,ab)
                            val hyp_name = ref("")
                            val res as (pval,ded_info as {conc=rest_conc,proof=rest_proof,fa=rest_fa}) = 
                                  (case matchPat(propVal(new_assumption),bpat,makeEvalExpFunction (env1,ab)) of 
                                      SOME(map,_) => let val (vmap,mmap) = getValAndModMaps(!env1)
                                                         val env1' = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                                         val _ = extractHypothesisName(map,propVal(new_assumption),hyp_name)
                                                     in
                                                        doBindings(more,new_assumption::assumptions,env1')
                                                     end
                                    | _ => evError("Assume pattern failed to match the corresponding value, the\n "^
                                                   (valLCTypeAndStringNoColon (propVal new_assumption)),
                                                   SOME(A.posOfPat(bpat))))
                            val (new_conclusion,body_conclusion) = 
                                  (case coerceValIntoProp(pval) of
                                      SOME(p) => (Prop.makeConditional(new_assumption,p),p))
                            val hyp_name_opt = if (!hyp_name) = "" then NONE else SOME(S.symbol(!hyp_name))
                        in
                           (propVal(new_conclusion),{conc=new_conclusion,
   				                     proof=assumeProof({hyp=hypothesis(hyp_name_opt,new_assumption), body=rest_proof}),
						     fa=propDiff(rest_fa,new_assumption::(Prop.decomposeConjunctions new_assumption))})
                        end 
           in
              doBindings(bindings,[],env)
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
                            res as (body_val,body_ded_info)  => 
                              (case coerceValIntoProp(body_val) of
                                 SOME(Q) => if Prop.alEq(P,Q) then (closeTracing(level,true);res)
                                            else (closeTracing(level,false);evError(msg(P,Q),SOME(pos)))))
           | _ => evError(msg2(wv),SOME(A.posOfExp(wanted_res))))
      end
  | evDed(A.infixAssumeDed({bindings,body,pos}),env,ab) = 
	let fun getPropsAndEnv([],props,env) = (props,env)
	      | getPropsAndEnv((b:A.binding as {bpat,pos,def,...})::rest,props,env) = 
	                let val (pval,_) = evPhrase(def,env,ab)
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
	    val body_res as (body_val,body_ded_info as {proof=body_proof,conc=body_conc,fa=body_fa}) = evDed(body,new_env,ABase.augment(ab,hyps'))
            in
	      (case coerceValIntoProp(body_val) of
	         SOME(q) => let val conj = (case hyps of
					      [P] => P
					    |  _  => Prop.makeConjunction(hyps))
                                val conditional_conclusion = Prop.makeConditional(conj,q)
                                val final_ded_info = {proof=assumeProof({hyp=hypothesis(NONE,conj), body=body_proof}),
       				                      conc=conditional_conclusion,
			                              fa=propDiff(body_fa,[conj])}
			    in
			       (propVal(conditional_conclusion),final_ded_info)
			    end
               | _ => evError("Impossible error encountered in assume deduction: the body of "^
                              "the deduction did not produce a sentence",SOME(A.posOfDed(body))))
	   end
  | evDed(D,env,ab) = 
          let val _ = print("\n***************************************** UNHANDLED CERT CASE: " ^ (A.unparseDed(D)) ^ "\n")
          in
             (evalDed(D,env,ab),{proof=trivial_cert,conc=Prop.true_prop,fa=[]})
          end
and
   doSupposeAbsurd(hyp:A.phrase,hyp_name_pat:A.pattern option,body:A.deduction,pos:A.position,env,ab) = 
    let val (hypv,_) = evPhrase(hyp,env,ab)
    in
      (case coerceValIntoPropVal(hypv) of
          SOME(pval as propVal(antecedent)) => 
              let val hypothesis_name = ref("")
                  val asms = Prop.decomposeConjunctions(antecedent)
                  val new_ab = ABase.augment(ab,asms)
                  val new_env = 
                         (case hyp_name_pat of
                             SOME(bpat) => (case matchPat(pval,bpat,makeEvalExpFunction (env,ab)) of 
                                              SOME(map,_) => let val _ = extractHypothesisName(map,pval,hypothesis_name)
                                                             in
                                                                ref(augmentWithMap(!env,map))
                                                             end
                                            | _ => evError("Suppose-absurd pattern failed to match "^ 
                                                           "the corresponding value, the\n"^
                                                           (valLCTypeAndStringNoColon pval),
                                                           SOME(A.posOfPat(bpat))))
                          | _ => env)
                  val body_res = evDed(body,new_env,new_ab)
              in
                (case body_res of
                   (body_val,body_ded_info as {proof=body_proof,conc=body_conc,fa=body_fa}) =>
                      (case coerceValIntoProp(body_val) of
                         SOME(p') => if Prop.isBooleanFalse(p') then 
                                        let val negated_conclusion = Prop.makeNegation(antecedent)
                                            val hyp_name_option = if (!hypothesis_name) = "" then NONE else SOME(S.symbol(!hypothesis_name))
                                            val final_ded_info = {proof=supAbProof({hyp=hypothesis(hyp_name_option,antecedent), body=body_proof}),
	 					                  conc=negated_conclusion,
							          fa=propDiff(body_fa,[antecedent])}
                                        in
                                           (propVal(negated_conclusion),final_ded_info)
                                        end 
                                     else evError("The body of a suppose-absurd deduction"
                                                 ^" must derive the sentence false---but here the " 
                                                 ^"result was the sentence\n"^pprintProp(p'),
                                                  SOME(A.posOfDed(body)))))
              end
        | _ => evError("The hypothesis of a suppose-absurd deduction must be a sentence---"^
                       "but here it is a "^valLCTypeAndString(hypv),SOME(A.posOfPhrase(hyp))))
    end
and evalDCheckClauses(clauses,env,ab) = 
     let fun f([]) = NONE
           | f({test=A.boolCond(phr),result}::more) =
                  (case evPhrase(phr,env,ab) of
                                 (propVal(P),_) =>
				   (case P.isAtom(P) of
				       SOME(t) => if AT.isTrueTerm(t) then SOME(result) else f(more)
				     | _ => f(more))
                                 | (termVal(t),_) => if AT.isTrueTerm(t) then SOME(result)
	 					     else f(more)
	      		         | _ => f(more))
           | f({test=A.elseCond,result}::more) = SOME(result)
     in
        f(clauses)
     end
and 
    evalMethodApp(method,args:A.phrase list,env:SemanticValues.value_environment ref,ab:ABase.assum_base,pos:A.position) =       
     (let val app_pos = pos
           fun getArgVals([],arg_vals,ded_vals,ded_infos) = (rev(arg_vals),ded_vals,rev(ded_infos))
             | getArgVals(A.exp(e)::rest,arg_vals,ded_vals,ded_infos) =
                        getArgVals(rest,evalExp(e,env,ab)::arg_vals,ded_vals,ded_infos)
             | getArgVals(A.ded(d)::rest,arg_vals,ded_vals,ded_infos) =
                       (case evDed(d,env,ab) of
                           (propVal(dprop),ded_info as {proof,conc,fa,...}) =>
                              getArgVals(rest,propVal(dprop)::arg_vals,dprop::ded_vals,ded_info::ded_infos)
                         | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                        "argument of a method application---the deduction did not "^
                                        "produce a sentence!",SOME(A.posOfDed(d))))
           fun getArgValsAndPositions() =
                let val pos_ar = Array.array(length(args)+2,A.dum_pos)
                    val _ = Array.update(pos_ar,0,app_pos)
                    val _ = Array.update(pos_ar,1,A.posOfExp(method))
                    fun doArgs([],arg_vals,ded_vals,ded_infos,i) = (rev(arg_vals),ded_vals,rev(ded_infos),pos_ar)
                      | doArgs(A.exp(e)::rest,arg_vals,ded_vals,ded_infos,i) =
                          (Array.update(pos_ar,i,A.posOfExp(e));
                           doArgs(rest,evalExp(e,env,ab)::arg_vals,ded_vals,ded_infos,i+1))
                      | doArgs(A.ded(d)::rest,arg_vals,ded_vals,ded_infos,i) =
                          (Array.update(pos_ar,i,A.posOfDed(d));
                           (case evDed(d,env,ab) of
                               (propVal(dprop),ded_info as {proof,conc,fa,...}) =>
                                 doArgs(rest,propVal(dprop)::arg_vals,dprop::ded_vals,ded_info::ded_infos,i+1)
                             | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                             "argument of a method application---the deduction did not "^
                                             "produce a sentence",SOME(A.posOfDed(d)))))
                in
                   doArgs(args,[],[],[],2)
                end
       in
          (case evalExp(method,env,ab) of
               closMethodVal(A.methodExp({params,body,pos=mexp_pos,name=rname,...}),clos_env) =>
                       let (** val _ = print("\nAbout to execute a general closure named " ^ (!rname) ^ ", of " ^ (Int.toString (length params)) ^ " arguments...\n")  **)
                           val (arg_vals,ded_vals,arg_ded_infos) = getArgVals(args,[],[],[])
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
                           val result as (res_val,body_ded_info as {proof,conc,fa,...}) = evDed(body,new_env,new_ab)
                           val final_ded_info = reconcile(body_ded_info,arg_ded_infos)
                       in
                          (res_val,final_ded_info)
                       end
               | methodVal(f,method_code) =>
                     (let val method_name = S.name method_code
                          val (arg_vals,ded_vals,arg_ded_infos,pos_array) = getArgValsAndPositions()
                        (* val _ = print("\nApplication of " ^ method_name ^ " to " ^ (Int.toString (length arg_vals)) ^ " arguments: " ^ (Basic.printListStr(arg_vals,valToString,"  || ")) ^ "\n")  *)
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
                          val res_val = f(arg_vals,env,new_ab)
                          val avs = map (fn v => getAlphaVal(v,method_name)) arg_vals
                          val tail_ded_info = {conc=getProp(res_val),
					       fa=getFA(method_code,arg_vals,new_ab),
					       proof=ruleApp({rule=method_code,args=avs})}
                          val ded_info = reconcile(tail_ded_info,arg_ded_infos)
                      in
                         (res_val,ded_info)
                      end handle PrimError(msg) => evError(msg,SOME(app_pos)))
               | primUMethodVal(f,method_code) =>
                                      let val method_name = S.name method_code
					  val (arg_vals,ded_vals,arg_ded_infos,pos_array) = getArgValsAndPositions()
                                          val new_ab = ABaseAugment(ab,ded_vals)
                                          val res_val = f(hd(arg_vals),env,new_ab)
                                          val avs = map (fn v => getAlphaVal(v,method_name)) arg_vals
                                          val tail_ded_info = {conc=getProp(res_val),
		   			                       fa=getFA(method_code,arg_vals,new_ab),
					                       proof=ruleApp({rule=method_code,args=avs})}
                                          val ded_info = reconcile(tail_ded_info,arg_ded_infos)
                                      in
                                        if not(length(arg_vals)  = 1) then
                                           evError(wrongArgNumber(S.name(method_code),length(arg_vals),1),getPosOpt(pos_array,0))
                                        else ((res_val,ded_info) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | primBMethodVal(f,method_code) =>
                                      let val method_name = S.name method_code
                                          val (arg_vals,ded_vals,arg_ded_infos,pos_array) = getArgValsAndPositions()
                                          val new_ab = ABaseAugment(ab,ded_vals)
                                          val res_val = f(hd(arg_vals),hd(tl(arg_vals)),env,new_ab)
                                          val avs = map (fn v => getAlphaVal(v,method_name)) arg_vals
                                          val tail_ded_info = {conc=getProp(res_val),
		   			                       fa=getFA(method_code,arg_vals,new_ab),
					                       proof=ruleApp({rule=method_code,args=avs})}
                                          val ded_info = reconcile(tail_ded_info,arg_ded_infos)
                                      in
                                        if not(length(arg_vals)  = 2) then
                                           evError(wrongArgNumber((S.name method_code),length(arg_vals),2),getPosOpt(pos_array,0))
                                        else ((res_val,ded_info) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,arg_ded_infos,pos_array) = getArgValsAndPositions()
			 (* val _ = print("\nAbout to execute a binary closure named " ^ (!name) ^ " to these args: " ^ (Basic.printListStr(arg_vals,valToString, " !! ")) ^ "\n") *)
                           val _ =  if not(length(arg_vals)  = 2) then
                                       evError(wrongArgNumber(!name,length(arg_vals),2),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s1,hd(arg_vals))
                           val vm' = Symbol.enter(vm,s2,hd(tl(arg_vals)))
                           val new_env = ref(valEnv({val_map=vm',mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals)
                           val result as (res_val,body_ded_info as {proof,conc,fa,...}) = evDed(d,new_env,new_ab)
                           val final_ded_info = reconcile(body_ded_info,arg_ded_infos)
                       in
                          (res_val,final_ded_info)
                       end
               | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,arg_ded_infos,pos_array) = getArgValsAndPositions()
			   (* val _ = print("\nAbout to execute a unary closure named " ^ (!name) ^ " to this arg: " ^ (valToString (hd arg_vals)) ^ "\n") *)
                           val _ =  if not(length(arg_vals)  = 1) then
                                       evError(wrongArgNumber(!name,length(arg_vals),1),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s,hd(arg_vals))
                           val new_env = ref(valEnv({val_map=vm,mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals)
                           val result as (res_val,body_ded_info as {proof,conc,fa,...}) = evDed(d,new_env,new_ab)
                           val final_ded_info = reconcile(body_ded_info,arg_ded_infos)
                       in
                          (res_val,final_ded_info)
                       end
               | v => let val _ = Basic.mark("E") in evError("The leftmost expression of a method application "^
                              "must produce a method---here it produced a "^valLCTypeAndString(v),
                              SOME(A.posOfExp(method))) end)
       end)
in
    fn (d,env,ab) => let val _ = Basic.mark("1")
                         val res = evDed(d,env,ab)
                         val _ = Basic.mark("2")
                     in
                       res
	             end
end
 
end (* of structure Alpha *) 



