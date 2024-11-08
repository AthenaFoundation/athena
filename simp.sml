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


fun getPropAndEnv(b:A.binding as {bpat,pos,def,...},env,ab) = 
      let val _ = Basic.mark("HERE WE ARE")
          val pval = Semantics.evalPhrase(def,env,ab)
          val _ = Basic.mark("UHOH...")
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

fun getPropsAndEnv([],props,env,_) = (props,env)
  | getPropsAndEnv((b:A.binding as {bpat,pos,def,...})::rest,props,env,ab) = 
      let val pval = Semantics.evalPhrase(def,env,ab)
          val (p,env') =  getPropAndEnv(b,env,ab)
     in
        getPropsAndEnv(rest,p::props,env',ab)
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
              let val (props,new_env) = getPropsAndEnv(bindings,[],env,starting_ab)
   	          val hyps = rev(props)
                  val q = C(body,new_env)					    
              in
                (case hyps of
                   [P] => Prop.makeConditional(P,q) 
                 | _ => Prop.makeConditional(Prop.makeConjunction(hyps),q))
              end
        | C(A.letDed({bindings, body, ...}),env) = 
              let (*** val _ = print("\nAbout to call getPropsAndEnv...\n")  ***)
                  val (props,new_env) = getPropsAndEnv(bindings,[],env,starting_ab)
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
			| "mt" => getMtConclusion(p1,p2)
			| "dsyl" => getDsylConclusion(p1,p2)
			| "both" => Prop.makeConjunction([p1,p2])
			| "left-either" => Prop.makeDisjunction([p1,p2])
			| "right-either" => Prop.makeDisjunction([p1,p2])
			| "either" => Prop.makeDisjunction([p1,p2])
 	  	        | _ => Basic.fail("Unknown binary method, cannot compute conclusion..."))
                 | _ => Basic.fail("Cannot compute conclusions for BMethodApps where the operator is not an identifier."))
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
                       let  val _ = Basic.mark("GPGP")
                            val (p,env') = getPropAndEnv(b,env,ab)
			    val _ = Basic.mark("DONE")
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
  | fa(A.infixAssumeDed({bindings,body,...}),env,ab) =  
          let val (binding_fas,binding_conclusions,new_env) = faLoop(bindings,[],[],env,ab)
              val (props,new_env') = getPropsAndEnv(bindings,[],env,ab)
              val hyps = rev(props)
              val conjuncts:Prop.prop list = List.concat (map Prop.decomposeConjunctionsStrict hyps)
              val all_hyps = hyps@conjuncts		
(****			  
              val _ = print("\nHere's new_env: " ^ (SemanticValues.envToString (!new_env)))
***)
              val _ = Basic.mark("XXXXXXXXXXXXXXXXXX")
              val body_fas = fa(body,new_env,ABase.augment(ab,all_hyps))
              val _ = Basic.mark("DDDDD")
              val true_body_fas = Basic.removeAllEq(all_hyps,body_fas,Prop.alEq)
          in
             Basic.removeDuplicatesEq(true_body_fas@binding_fas,Prop.alEq)
          end
  | fa(A.letDed({bindings, body, ...}),env,ab) = 
             let val _ = Basic.mark("YYYYYYYYYYYYYYYYY")
                 val (binding_fas,binding_conclusions,env') = faLoop(bindings,[],[],env,ab)
                 val _ = print("FAs of bindings: " ^ (Basic.printListStr(binding_fas,fn p => Prop.toPrettyStringDefault(0,p),"\n")))
                 val (body_fas,body_conclusion) = (fa(body,env',ab),conclusion(body,env',ab))
						      
                 val true_body_fas = Basic.removeAllEq(binding_conclusions,body_fas,Prop.alEq)
              in
                 Basic.removeDuplicatesEq(true_body_fas@binding_fas,Prop.alEq)
              end                         
  | fa(A.beginDed({members,...}),env,ab) = getSeqFAs(members,env,ab)
  | fa(A.BMethAppDed({method,arg1,arg2,...}),env,ab) = 
             let val p1 = getProp(arg1,env,ab)
                 val p2 = getProp(arg2,env,ab)
             in 
               (case method of 
                   A.idExp({msym, mods=[],sym,...}) => 
                      (case Symbol.name(sym) of 
                          "mp" => [p1,p2]
			| "left-either" => [p1]
			| "right-either" => [p2]
			| "either" => let val fas = ref([])
                                          val _ = if not(ABase.isMember(p1,ab)) then fas := [p1] else ()
                                          val _ = if not(ABase.isMember(p2,ab)) then fas := p1::(!fas) else ()
                                      in
                                        !fas
				      end
 	  	        | _ => [p1,p2])
                 | _ => Basic.fail("Cannot compute free assumptions for BMethodApps where the operator is not an identifier."))
             end
  | fa(A.UMethAppDed({method,arg,...}),env,ab) = 
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

end; (* of structure Simplify_New *)
