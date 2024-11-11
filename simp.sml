structure Simplify_New =

struct

exception IllFormedProof

structure A = AbstractSyntax;

fun illFormed() = raise IllFormedProof;

fun fp f = fn D => let val D' = f D
                    in
                       if D = D' then D else (fp f) D'
                    end;

fun weave f [] = f
  | weave f (g::rest) = f o g o (weave f rest);

fun memberOf L x = List.exists (fn a => a = x) L;

fun emptyIntersection(L1,L2) = not (List.exists (memberOf L2) L1);

fun remove(x,L) = List.filter (fn y => not(x = y)) L;

fun removeDuplicates [] = []
  | removeDuplicates (x::rest) = x::removeDuplicates(remove(x,rest));

fun getThreadElements(A.beginDed({members,...})) = Basic.flatten(map getThreadElements members)
  | getThreadElements(D) = [D];


fun makeEvalExpFunction(env,ab) =      
       (fn (e,binding_map) => (case binding_map of 
                                  NONE => Semantics.evalExp(e,env,ab)
                                | SOME(map) => Semantics.evalExp(e,ref(Semantics.augmentWithMap(!env,map)),ab)))


fun getValAndEnv(b:A.binding as {bpat,pos,def,...},env,ab) = 
      let val v = Semantics.evalPhrase(def,env,ab)
      in
        (case Semantics.matchPat(v,bpat,makeEvalExpFunction (env,ab)) of 
          SOME(map,_) => let val (vmap,mmap) = Semantics.getValAndModMaps(!env)
                             val env' = ref(Semantics.valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                         in
                            (v,env')
                         end
        | _ => Basic.fail("Pattern failed to match the corresponding value."))
      end 

fun getPropAndEnv(b:A.binding as {bpat,pos,def,...},env,ab) = 
      let val pval = Semantics.evalPhrase(def,env,ab)
      in
         (case Semantics.coerceValIntoProp(pval) of
             SOME(p) => (case Semantics.matchPat(pval,bpat,makeEvalExpFunction (env,ab)) of 
                           SOME(map,_) => let val (vmap,mmap) = Semantics.getValAndModMaps(!env)
                                              val env' = ref(Semantics.valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                          in
                                            (p,env')
                                          end
		         | _ => Basic.fail("Pattern failed to match the corresponding value."))
           | _ => Basic.fail("A sentence (hypothesis) was expected here..."))
      end 

fun getPropsAndEnv(bindings,env,ab,binding_transformer_option) = 
  let fun getPropsAndEnvAux([],props,env,_,bindings_so_far) = (props,env,rev(bindings_so_far))
        | getPropsAndEnvAux((b:A.binding as {bpat,pos,def,...})::rest,props,env,ab,bindings_so_far) = 
             let val pval = Semantics.evalPhrase(def,env,ab)
                 val (p,env') =  getPropAndEnv(b,env,ab)
                 val new_binding = (case binding_transformer_option of SOME(transformer) => transformer(b,props,env') | _ => b)
             in
                getPropsAndEnvAux(rest,p::props,env',ab,new_binding::bindings_so_far)
             end
  in
     getPropsAndEnvAux(bindings,[],env,ab,[])
  end

fun getProp(phrase,env,ab) = 
     (case Semantics.coerceValIntoPropVal(Semantics.evalPhrase(phrase,env,ab)) of 
         SOME(Semantics.propVal(p)) => p
       | _ => Basic.fail("A sentence was expected here."))

fun getLeftConjunct(p) = 
   (case Prop.isConj(p) of
       SOME(l::_) => l
     | _ => Basic.fail("A conjunction was expected here..."))

fun getLeftIff(p) = 
   (case Prop.isBiCond(p) of
       SOME(p1,p2) => Prop.makeConditional(p1,p2)
     | _ => Basic.fail("A biconditional was expected here..."))

fun getRightIff(p) = 
   (case Prop.isBiCond(p) of
       SOME(p1,p2) => Prop.makeConditional(p2,p1)
     | _ => Basic.fail("A biconditional was expected here..."))

fun getRightConjunct(p) = 
   (case Prop.isConj(p) of
       SOME(h::more) => Prop.makeConjunction(more)
     | _ => Basic.fail("A conjunction was expected here..."))

fun getDnBody(p) = 
   (case Prop.isNeg(p) of
       SOME(q) => (case Prop.isNeg(q) of 
                      SOME(r) => r
 	            | _ => Basic.fail("A double negation was expected here..."))
     | _ => Basic.fail("A double negation was expected here..."))

fun getDmConclusion(p) = 
   (case Prop.isNeg(p) of
       SOME(q) => (case Prop.isConj(q) of
                      SOME(props) => Prop.makeDisjunction(map Prop.makeNegation props)
		    | _ => (case Prop.isDisj(q) of
                              SOME(props) => Prop.makeConjunction(map Prop.makeNegation props)
			    | _ => Basic.fail("A conjunction or disjunction was expected here.")))
     | _ => Basic.fail("A negation was expected here."))

fun getCondDefConclusion(p) = 
   (case Prop.isCond(p) of 
       SOME(q1,q2) => Prop.makeDisjunction([Prop.makeComplement(q1),q2])
     | _ => (case Prop.isDisj(p) of 
                SOME(d::more) => Prop.makeConditional(Prop.makeComplement(d),Prop.makeDisjunction(more))
              | _ => Basic.fail("A conditional or disjunction was expected here.")))

fun getNegCondConclusion(p) = 
   (case Prop.isNeg(p) of
       SOME(body) => 
          (case Prop.isCond(body) of 
              SOME(q1,q2) => Prop.makeConjunction([q1,Prop.makeNegation(q2)])
            | _ => Basic.fail("A conditional was expected here."))
     | _ => (case Prop.isConj(p) of
                SOME([q1,q2]) => 
                   (case Prop.isNeg(q2) of 
                       SOME(body) => Prop.makeNegation(Prop.makeConditional(q1,q2))
                     | _ => Basic.fail("A negation was expected here."))
              | _ => Basic.fail("A binary conjunction was expected here.")))

fun getBdnConclusion(p) =
   (case Prop.isNeg(p) of
       SOME(q) => (case Prop.isNeg(q) of 
                      SOME(r) => r
 	            | _ => Prop.makeNegation(Prop.makeNegation(p)))
     | _ => Prop.makeNegation(Prop.makeNegation(p)))


fun getCommConclusion(p) = Basic.fail("")
   (case Prop.isConj(p) of 
       SOME(q1::more) => Prop.makeConjunction([Prop.makeDisjunction(more),q1])
     | _ => (case Prop.isDisj(p) of 
                SOME(q1::more) =>  Prop.makeDisjunction([Prop.makeDisjunction(more),q1])
              | _ => Basic.fail("A conjunction or disjunction was expected here.")))

fun getContraPosConclusion(p) = 
   (case Prop.isCond(p) of 
       SOME(q1,q2) => 
         (case (Prop.isNeg(q1),Prop.isNeg(q2)) of
             (SOME(q1'),SOME(q2')) => Prop.makeConditional(q2',q1')
           | _ => Prop.makeConditional(Prop.makeNegation(q2),Prop.makeNegation(q1))))

fun getBiCondDefConclusion(p) = 
   (case Prop.isBiCond(p) of 
       SOME(q1,q2) => Prop.makeConjunction([Prop.makeConditional(q1,q2),Prop.makeConditional(q2,q1)])
     | _ => (case Prop.isConj(p) of
                SOME([q1,q2]) => (case (Prop.isCond(q1),Prop.isCond(q2)) of 
                                     (SOME(p1,p2),SOME(p2',p1')) => Prop.makeBiConditional(p1,p2)
                                   | _ => Basic.fail(""))))


fun complements(p1,p2) = Prop.alEq(p2,Prop.makeComplement(p1)) orelse Prop.alEq(p1,Prop.makeComplement(p2))

fun getNegatedBiCondDefConclusion(p) = Basic.fail("")

fun getDistConclusion(p) = Basic.fail("")

fun getMpConclusion(p1,p2) = 
   (case Prop.isCond(p1) of 
       SOME(q1,q2) => if Prop.alEq(p2,q1) then q2 else Basic.fail("Invalid use of mp")
     | _ => Basic.fail("Invalid use of mp: A conditional was expected as the first argument"))

fun getMtConclusion(p1,p2) =
   (case Prop.isCond(p1) of 
       SOME(q1,q2) => if complements(p2,q2) then Prop.makeComplement(q1) else Basic.fail("Invalid use of mt")
     | _ => Basic.fail("Invalid use of mt: A conditional was expected as the first argument"))

fun getDsylConclusion(p1,p2) = 
   (case Prop.isDisj(p1) of 
       SOME(q1::(more as (_::_::_))) => if complements(p2,q1) then Prop.makeDisjunction(more) else Basic.fail("Invalid use of mt")
     | SOME([q1,q2]) => if complements(p2,q1) then q2 else if complements(p2,q2) then q1 else Basic.fail("Invalid use of dsyl")
     | _ => Basic.fail("Invalid use of dsyl: a disjunction with at least 2 components was expected here."))

fun getFromComplementsConclusions(args) = 
   (case args of 
       [p,q1,q2] => p
     | _ => Basic.fail("Invalid use of from-complements."))

val (proofConclusionTop,FATop) = 
let fun conclusion(D,starting_env,starting_ab) = 
  let fun C(A.assumeDed({assumption,body,...}),env) = 
           let val p = C(body,env)
           in
              (case Semantics.coerceValIntoProp(Semantics.evalPhrase(assumption,env,starting_ab)) of 
                  SOME(hyp) => Prop.makeConditional(hyp,p)
                | _ => Basic.fail("A sentence was expected here."))
           end
        | C(A.beginDed({members,...}),env) = C(List.last members,env)
        | C(A.absurdDed({hyp,body,...}),env) = 
              (case Semantics.coerceValIntoPropVal(Semantics.evalPhrase(hyp,env,starting_ab)) of 
                  SOME(Semantics.propVal(hyp)) => Prop.makeNegation(hyp)
                | _ => Basic.fail("A sentence was expected here."))
        | C(A.infixAssumeDed({bindings,body,...}),env) = 
              let val (props,new_env,bindings') = getPropsAndEnv(bindings,env,starting_ab,NONE)
   	          val hyps = rev(props)
                  val q = C(body,new_env)					    
              in
                (case hyps of
                   [P] => Prop.makeConditional(P,q) 
                 | _ => Prop.makeConditional(Prop.makeConjunction(hyps),q))
              end
        | C(A.letDed({bindings, body, ...}),env) = 
              let (*** val _ = print("\nAbout to call getPropsAndEnv...\n")  ***)
                  val (props,new_env,bindings') = getPropsAndEnv(bindings,env,starting_ab,NONE)
              in
                 C(body,new_env)					    
              end                         
        | C(A.BMethAppDed({method,arg1,arg2,...}),env) = 
             let val p1 = getProp(arg1,env,starting_ab)
                 val p2 = getProp(arg2,env,starting_ab)
             in 
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
                          "mp" => getMpConclusion(p1,p2)
                        | "by-contradiction" => p1 
			| "mt" => getMtConclusion(p1,p2)
			| "dsyl" => getDsylConclusion(p1,p2)
			| "both" => Prop.makeConjunction([p1,p2])
			| "left-either" => Prop.makeDisjunction([p1,p2])
			| "right-either" => Prop.makeDisjunction([p1,p2])
			| "either" => Prop.makeDisjunction([p1,p2])
 	  	        | _ => Basic.fail("Unknown binary method, cannot compute conclusion..."))
                 | _ => Basic.fail("Cannot compute conclusions for BMethodApps where the operator is not an identifier."))
             end
        | C(A.UMethAppDed({method,arg,...}),env) = 
             let val p = getProp(arg,env,starting_ab)
             in
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
                          "claim" => p
                         | "force" => p
                         | "from-false" => p 
                         | "bdn" => getBdnConclusion(p)
                         | "ex-middle" => Prop.makeDisjunction([p,Prop.makeNegation(p)])
                         | "contra-pos" => getContraPosConclusion(p) 
  	  	         | "left-and" => getLeftConjunct(p)
  	  	         | "right-and" => getRightConjunct(p)
  	  	         | "left-iff" => getLeftIff(p)
  	  	         | "right-iff" => getRightIff(p)
  	  	         | "dn" => getDnBody(p)
  	  	         | "dm" => getDmConclusion(p)
  	  	         | "comm" => getCommConclusion(p)
  	  	         | "dist" => getDistConclusion(p)
  	  	         | "cond-def" => getCondDefConclusion(p)
  	  	         | "neg-cond" => getNegCondConclusion(p)
  	  	         | "bicond-def" => getBiCondDefConclusion(p)
  	  	         | "negated-bicond" => getNegatedBiCondDefConclusion(p)
  	  	         | _ => Basic.fail("Unknown unary method, cannot compute conclusion..."))
                 | _ => Basic.fail("Cannot compute conclusions for UMethodApps where the operator is not an identifier."))
             end
        | C(A.methodAppDed({method,args,...}),env) = 
	     let val props = map (fn arg => getProp(arg,env,starting_ab)) args
             in
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
                          "from-complements" => getFromComplementsConclusions(props)
   		        | _ => Basic.fail("Unknown method, cannot compute conclusion..."))
		 | _ => Basic.fail("Cannot compute conclusions for methodApps where the operator is not an identifier."))
             end
	| C(A.byCasesDed({disj,from_exps,arms,...}),env) = 
               (case arms of 
                   [] => Basic.fail("At least one case arm was expected here.")
                 | (arm:A.case_clause as {proof,...})::_  => C(proof,env))
        | C(_) = Basic.fail("Unable to compute conclusions for this type of deduction.")
              
  in
    C(D,starting_env)
  end
and getSeqFAs(deds,env,ab) = 
            let fun loop([],fas_so_far,conclusions_so_far) = rev(fas_so_far)
                  | loop(member::more,fas_so_far,conclusions_so_far) = 
                        let val member_fas = fa(member,env,ab)
                            val true_fas = Basic.removeAllEq(conclusions_so_far,member_fas,Prop.alEq)
                            val member_conclusion = conclusion(member,env,ab)
                        in
                           loop(more,true_fas@fas_so_far,member_conclusion::conclusions_so_far)
                        end
            in
               loop(deds,[],[])
            end 
and faLoop([],fas_so_far,conclusions_so_far,env,ab) = (rev(fas_so_far),rev(conclusions_so_far),env)
  | faLoop((b:A.binding as {bpat,pos,def,...})::more,fas_so_far,conclusions_so_far,env,ab) = 
                       let  val (p,env') = getPropAndEnv(b,env,ab)
                       in
                          (case def of
                             A.ded(d) =>
                                  let val member_fas = fa(d,env,ab)
                                      val true_fas = Basic.removeAllEq(conclusions_so_far,member_fas,Prop.alEq)
                                      val member_conclusion = conclusion(d,env,ab)
                                  in
				    faLoop(more,true_fas@fas_so_far,member_conclusion::conclusions_so_far,env',ab)
				  end
                           | _ => faLoop(more,fas_so_far,conclusions_so_far,env',ab))
                       end
and fa(A.assumeDed({assumption,body,...}),env,ab) = 
          let val hypothesis = getProp(assumption,env,ab)
          in
            Basic.removeEq(hypothesis,fa(body,env,ab),Prop.alEq)
          end
  | fa(A.absurdDed({hyp,body,...}),env,ab) = 
        let val hypothesis = getProp(hyp,env,ab)
        in
           Basic.removeEq(hypothesis,fa(body,env,ab),Prop.alEq)
        end 
  | fa(A.infixAssumeDed({bindings,body,...}),env,ab) =  
          let val (binding_fas,binding_conclusions,new_env) = faLoop(bindings,[],[],env,ab)
              val (props,new_env',bindings') = getPropsAndEnv(bindings,env,ab,NONE)
              val hyps = rev(props)
              val conjuncts:Prop.prop list = List.concat (map Prop.decomposeConjunctionsStrict hyps)
              val all_hyps = hyps@conjuncts		
              val body_fas = fa(body,new_env,ABase.augment(ab,all_hyps))
              val true_body_fas = Basic.removeAllEq(all_hyps,body_fas,Prop.alEq)
          in
             Basic.removeDuplicatesEq(true_body_fas@binding_fas,Prop.alEq)
          end
  | fa(A.letDed({bindings, body, ...}),env,ab) = 
             let val (binding_fas,binding_conclusions,env') = faLoop(bindings,[],[],env,ab)
                 (** val _ = print("FAs of bindings: " ^ (Basic.printListStr(binding_fas,fn p => Prop.toPrettyStringDefault(0,p),"\n"))) **)
                 val (body_fas,body_conclusion) = (fa(body,env',ab),conclusion(body,env',ab))
						      
                 val true_body_fas = Basic.removeAllEq(binding_conclusions,body_fas,Prop.alEq)
              in
                 Basic.removeDuplicatesEq(true_body_fas@binding_fas,Prop.alEq)
              end                         
  | fa(A.beginDed({members,...}),env,ab) = getSeqFAs(members,env,ab)
  | fa(A.BMethAppDed({method,arg1,arg2,...}),env,ab) = 
             let val p1 = getProp(arg1,env,ab)
                 val p1_lst = if A.isDeduction(arg1) then [] else [p1]
                 val p2 = getProp(arg2,env,ab)
                 val p2_lst = if A.isDeduction(arg2) then [] else [p2]
             in 
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
			  "left-either" => p1_lst
			| "right-either" => p2_lst
			| "either" => let val fas = ref([])
                                          val _ = if not(ABase.isMember(p1,ab)) then fas := [p1] else ()
                                          val _ = if not(ABase.isMember(p2,ab)) then fas := p1::(!fas) else ()
                                      in
                                        !fas
				      end
 	  	        | _ => p1_lst @ p2_lst)
                 | _ => Basic.fail("Cannot compute free assumptions for BMethodApps where the operator is not an identifier."))
             end
  | fa(A.UMethAppDed({method,arg,...}),env,ab) = 
             if A.isDeduction(arg) then []
             else 
             let val p = getProp(arg,env,ab)
             in
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
                           "ex-middle" => []
                         | "from-false" => []
  	  	         | _ => [p])
                 | _ => Basic.fail("Cannot compute free assumptions for UMethodApps where the operator is not an identifier."))
             end
  | fa(A.methodAppDed({method,args,...}),env,ab) = 
             let fun getAllNonDeds([],res) = rev(res)
                   | getAllNonDeds(phrase::more,res) = if A.isDeduction(phrase) then getAllNonDeds(more,res) else getAllNonDeds(more,(getProp(phrase,env,ab))::res)
                 val tail_props_non_deds = getAllNonDeds(tl args,[])
                 val props_non_deds = if not(null(args)) andalso not(A.isDeduction(hd args)) then (getProp(hd args,env,ab))::tail_props_non_deds else tail_props_non_deds
             in
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                     (case Symbol.name(sym) of 
                         "from-complements" => tail_props_non_deds 
 	  	     | _ => props_non_deds)
	         | _ => Basic.fail("Cannot compute free assumptions for methodApps where the operator is not an identifier."))
             end
  | fa(input_ded as A.byCasesDed({disj,from_exps,arms,...}),env,ab) = 
(***
If from_exps is SOME(<expression-list>), then <expression-list> must produce a list of sentences, all of which will be members of the result (i.e., of FA(input_ded). ). 
Otherwise, disj must produce a sentence, and that sentence will be a member of the result UNLESS disj is a deduction. 
Finally, the FAs of all the proofs of all the arms will also be in the result.
***)
               (case arms of 
                   [] => Basic.fail("At least one case arm was expected here.")
                 | _ => let val disj_sentence = getProp(disj,env,ab)                                               
                            val disj_sentences = if A.isDeduction(disj) orelse Prop.isExMiddleInstance(disj_sentence) then [] else [disj_sentence]
                            val arm_fas = List.concat (map (fn cc:A.case_clause as {alt,proof,...} => 
                                                                  let val alt_sentence = getProp(A.exp(alt),env,ab)
                                                                      val proof_fas = Basic.removeEq(alt_sentence,fa(proof,env,ab),Prop.alEq)
                                                                  in
                                                                     proof_fas
								  end)
                                                           arms)
                        in
                          (case from_exps of
                              SOME(exps) => let val exp_sentences = map (fn e => getProp(A.exp(e),env,ab)) exps
                                            in
                                               disj_sentences @ exp_sentences @ arm_fas 
                                            end
			    | _ => (disj_sentences @ arm_fas))
                        end)
  | fa(D,_,_) = Basic.fail("Don't know how to do FAs on this type of proof yet: " ^ (A.unparseDed D))
in
  (fn (D,starting_env,starting_ab) => 
       let val res = conclusion(D,starting_env,starting_ab)
       in
          res
       end,
   fn (D,env,starting_ab) => fa(D,env,starting_ab))
end

fun proofConclusion(D,ab) = proofConclusionTop(D,SemanticValues.top_val_env,ab)

fun FA(D,ab) = FATop(D,SemanticValues.top_val_env,ab)

fun getBindingProofs(bindings) = 
  let fun loop([],so_far) = rev(so_far)
	| loop((b:A.binding as {bpat,pos,def})::more,so_far) = 
            (case def of 
                A.ded(d) => loop(more,d::so_far) 
              | _ => loop(more,so_far))
  in
    loop(bindings,[])
  end

fun makeStrict(D,ab) = 
  let fun ms(A.assumeDed({assumption,body,pos})) = A.assumeDed({assumption=assumption,body=ms(body),pos=pos})
        | ms(A.absurdDed({hyp,body,pos})) = A.absurdDed({hyp=hyp,body=ms(body),pos=pos})
	| ms(D as A.beginDed({members,pos})) = 
                let val members' = map ms members
                    fun loop([last_proof],retained) = A.beginDed({members=rev(last_proof::retained),pos=pos})
		      | loop(D::(more as (_::_)),retained) = 
                               let val D_conc = proofConclusion(D,ab)
                                   val rest_proof = A.beginDed({members=more,pos=pos})
                                   val more_fas = FA(rest_proof,ab)
                               in
                                 if Basic.isMemberEq(D_conc,more_fas,Prop.alEq) then loop(more,D::retained) else loop(more,retained)
                            end
                    val res = loop(members',[])
                in
                  res 
                end
        | ms(A.infixAssumeDed({bindings,body,pos})) = 
            let val body' = ms(body)
                fun loop([],bindings_so_far) = rev(bindings_so_far)
		  | loop((b:A.binding as {bpat,pos,def,...})::more,bindings_so_far) = 
                      (case def of
                          A.ded(d) => loop(more,{bpat=bpat,pos=pos,def=A.ded(ms(d))}::bindings_so_far)
  		        | _ => loop(more,b::bindings_so_far))
                val bindings' = loop(bindings,[])
            in
               A.infixAssumeDed({bindings=bindings',body=body',pos=pos}) 
            end
        | ms(A.letDed({bindings, body, ...})) = 
             let val bindings' = map (fn (b:A.binding as {bpat,pos,def}) =>
                                        (case def of
                                            A.ded(D) => {bpat=bpat,def=A.ded(ms(D)),pos=pos}
					  | _ => b))
                                     bindings 
                 fun loop([],bindings_so_far) = rev(bindings_so_far)
		   | loop((b:A.binding as {bpat,pos,def})::more,bindings_so_far) = 
                                        (case def of
                                            A.ded(D) => 
                                              let val rest_proof = A.beginDed({members=getBindingProofs(more)@[body],pos=pos})
                                                  val rest_fas = FA(rest_proof,ab)
						  val D_conc = proofConclusion(D,ab)
                                              in
                                                if Basic.isMemberEq(D_conc,rest_fas,Prop.alEq) then loop(more,b::bindings_so_far) 
                                                else (**** Keep the binding/naming part only, not the deduction ****)
                                                    let val D_conc_as_string = Semantics.prettyValToString(Semantics.propVal(D_conc))
                                                        val D_conc_as_an_expression =       
                                                               (case Parse.parse_from_string(D_conc_as_string) of 
                                                                   [A.phraseInput(p as A.exp(_))] => p
								 | _ => Basic.fail("A sole expression was expected here."))
                                                    in
                                                       loop(more,{bpat=bpat,def=D_conc_as_an_expression,pos=pos}::bindings_so_far)
					            end
                                              end
					  | _ => loop(more,b::bindings_so_far))
             in
               Basic.fail("")
             end                         
	| ms(D) = D
  in
    ms(D)
  end  

fun makeUnaryRuleApp(rule_name,
		     rule_arg_as_string,
		     pos) = 
      (case Parse.parse_from_string(rule_arg_as_string) of
         [A.phraseInput(proof as A.ded(_))] => A.UMethAppDed({method=A.makeIdExpSimple(rule_name,pos),
	 			 			      arg=proof,
	 						      pos=pos})
       | _ => Basic.fail("A sole deduction was expected here."))
 
fun removeRepetitions(D,env,ab) = 
  let fun RR(D,already_hold,env) = 
         let val p = proofConclusion(D,ab)
         in
           if Basic.isMemberEq(p,already_hold,Prop.alEq) then  
              makeUnaryRuleApp("claim",Semantics.prettyValToString(Semantics.propVal(p)),A.posOfDed(D))
           else
              (case D of  
                 A.assumeDed({assumption,body,pos}) =>    
                        let val hyp = getProp(assumption,env,ab)
                        in
                          A.assumeDed({assumption=assumption,body=RR(body,hyp::already_hold,env),pos=pos})
                        end
	       | (D as A.beginDed({members,pos})) =>
                   let fun loop([],so_far,L) = A.beginDed({members=rev(so_far),pos=pos})
			 | loop(D::more,so_far,L) = 
                            let val D' = RR(D,L,env)
                                val p = proofConclusion(D',ab)
                            in
                              loop(more,D'::so_far,p::L)
		            end
                   in 
                      loop(members,[],already_hold)
                   end
	       | A.letDed({bindings, body, pos}) =>
                     let val (bindings',conclusions_so_far,env') = bindingsLoop(bindings,[],already_hold,env,ab)
                         val body' = RR(body,conclusions_so_far,env')
                     in
                        A.letDed({bindings=bindings',body=body',pos=pos})
                     end
	       | A.infixAssumeDed({bindings,body,pos})  => 
                     let fun binding_transformer(b:A.binding as {bpat,pos,def},
						 conclusions_so_far,
						 env) = 
                              let val def' = (case def of A.ded(d) => A.ded(RR(d,conclusions_so_far@already_hold,env)) | _ => def)
                              in
                                {bpat=bpat,def=def',pos=pos}
                              end                                  
                         val (props,env',bindings') = getPropsAndEnv(bindings,env,ab,SOME(binding_transformer))
                     in
                        A.infixAssumeDed({bindings=bindings',body=RR(body,props@already_hold,env'),pos=pos})
                     end
               | A.absurdDed({hyp,body,pos}) =>
                        let val hyp_prop = getProp(hyp,env,ab)
                        in
                           A.absurdDed({hyp=hyp,body=RR(body,hyp_prop::already_hold,env),pos=pos})
                        end                    
               | _ => D)
         end 
  and bindingsLoop([],optimized_bindings_so_far,conclusions_so_far,env,ab) = (rev(optimized_bindings_so_far),conclusions_so_far,env)
    | bindingsLoop((b:A.binding as {bpat,pos,def})::more,optimized_bindings_so_far,conclusions_so_far,env,ab) = 
          let  val (v,env') = getValAndEnv(b,env,ab)
          in
            (case def of 
                A.ded(D) => let val D' = RR(D,conclusions_so_far,env)
                                val p = proofConclusion(D',ab)                         
                            in
                               bindingsLoop(more,{bpat=bpat,pos=pos,def=A.ded(D')}::optimized_bindings_so_far,p::conclusions_so_far,env',ab)
		 	   end 
 	      | _ => bindingsLoop(more,b::optimized_bindings_so_far,conclusions_so_far,env',ab))
          end
  in
    RR(D,[],env)
  end

fun is_claim_ded(A.UMethAppDed({method,arg,...})) = 
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
                           "claim" => true
		         | _  => false)
		 | _ => false)
  | is_claim_ded(A.letDed({bindings, body, ...})) = is_claim_ded(body)
  | is_claim_ded(A.beginDed({members,...})) = is_claim_ded(List.last(members))
  | is_claim_ded(_) = false 

fun elimClaims(D,env,ab) = 
  let fun elim(A.beginDed({members,pos}),env,ab) = 
                let val members' = map (fn D => elim(D,env,ab)) members
                    val members'' = Basic.filterOut(Basic.allButLast(members'),is_claim_ded)
                in
                  A.beginDed({members=members''@[List.last(members)],pos=pos})
                end						
	| elim(A.assumeDed({assumption,body,pos}),env,ab) =  
              A.assumeDed({assumption=assumption,body=elim(body,env,ab),pos=pos})
	| elim(A.absurdDed({hyp,body,pos}),env,ab) = 
	      A.absurdDed({hyp=hyp,body=elim(body,env,ab),pos=pos})
        | elim(A.infixAssumeDed({bindings,body,pos}),env,ab) = 
                     let fun binding_transformer(b:A.binding as {bpat,pos,def},
						 conclusions_so_far,
						 env) = 
                                 let val def' = (case def of A.ded(d) => A.ded(elim(d,env,ab)) | _ => def)
                                 in
                                    {bpat=bpat,def=def',pos=pos}
				 end 
                         val (props,env',bindings') = getPropsAndEnv(bindings,env,ab,SOME(binding_transformer))
                     in
                        A.infixAssumeDed({bindings=bindings',body=elim(body,env',ab),pos=pos})
                     end
        | elim(A.letDed({bindings, body, pos}),env,ab) = 
                     let fun binding_transformer(b:A.binding as {bpat,pos,def},
						 conclusions_so_far,
						 env) = 
                                 let val def' = (case def of A.ded(d) => A.ded(elim(d,env,ab)) | _ => def)
                                 in
                                    {bpat=bpat,def=def',pos=pos}
				 end 
                         val (props,env',bindings') = getPropsAndEnv(bindings,env,ab,SOME(binding_transformer))
                         val bindings'' = Basic.filterOut(bindings', 
                                                          fn b:A.binding as {def,...} => 
                                                                           (case def of
                                                                               A.ded(proof) => is_claim_ded(proof)
   								             | _ => false))
                     in
                        A.letDed({bindings=bindings'',body=elim(body,env',ab),pos=pos})
                     end  
 	| elim(D,env,ab) = D
  in
    elim(D,env,ab)
  end
 
            

fun fp f = fn D => let val D' = f D
                    in
                       if D = D' then D else (fp f) D'
                    end


end; (* of structure Simplify_New *)
