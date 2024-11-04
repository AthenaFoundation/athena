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


fun conclusion(D,starting_env:SemanticValues.value_environment ref,starting_ab) = 
  let fun C(A.assumeDed({assumption,body,...}),env) = 
           let val p = C(body,env)
           in
              (case Semantics.evalPhrase(assumption,env,starting_ab) of 
                  Semantics.propVal(hyp) => Prop.makeConditional(hyp,p)
                | _ => Basic.fail("A sentence was expected here."))
           end
        | C(A.beginDed({members,...}),env) = C(List.last members,env)
        | C(A.absurdDed({hyp,body,...}),env) = 
              (case Semantics.evalPhrase(hyp,env,starting_ab) of 
                  Semantics.propVal(hyp) => Prop.makeNegation(hyp)
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
        | C(_) = Basic.fail("Unable to compute conclusions for this type of deduction.")
              
  in
    C(D,starting_env)
  end


end; (* of structure Simplify_New *)
