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




fun getPropsAndEnv([],props,env,_) = (props,env)
  | getPropsAndEnv((b:A.binding as {bpat,pos,def,...})::rest,props,env,ab) = 
      let val pval = Semantics.evalPhrase(def,env,ab)
      in
         (case Semantics.coerceValIntoProp(pval) of
             SOME(p) => (case Semantics.matchPat(pval,bpat,makeEvalExpFunction (env,ab)) of 
                           SOME(map,_) => let val (vmap,mmap) = Semantics.getValAndModMaps(!env)
                                              val env' = ref(Semantics.valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                          in
                                             getPropsAndEnv(rest,p::props,env',ab)
                                          end
                         | _ => Basic.fail("Assume pattern failed to match the corresponding value."))
           | _ => Basic.fail("A sentence (hypothesis) was expected here..."))
      end
and makeEvalExpFunction(env,ab) =      
       (fn (e,binding_map) => (case binding_map of 
                                  NONE => Semantics.evalExp(e,env,ab)
                                | SOME(map) => Semantics.evalExp(e,ref(Semantics.augmentWithMap(!env,map)),ab)))


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

fun getNegatedBiCondDefConclusion(p) = Basic.fail("")

fun getDistConclusion(p) = Basic.fail("")

fun conclusion(D,starting_ab) = 
  let val _ = print("\nENTERING conclusion inside simp.sml...\n")
      fun C(A.assumeDed({assumption,body,...}),env) = 
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
                  val q = C(body,env)					    
              in
                (case hyps of
                   [P] => Prop.makeConditional(P,q) 
                 | _ => Prop.makeConditional(Prop.makeConjunction(hyps),q))
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
    C(D,SemanticValues.top_val_env)
  end


end; (* of structure Simplify_New *)
