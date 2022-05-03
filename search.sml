(*======================================================================

Implementation of some classic search algorithms (depth-first,
breadth-first, and best-first).

=======================================================================*)

datatype term_state = state of {term:AthTerm.term,parent:term_state option,uplink_count:int,equation: Prop.prop,matching_sub: AthTerm.sub,score:real}

signature TERM_STATE_SPACE = STATE_SPACE where type state = term_state

structure TermSearch = 

struct

structure AT = AthTerm

fun rewriteResultToString(t,eqn,sub) = 
      "[[[[Redex term: "^(AT.toStringDefault(t))^"\nredex equation: "^
      (Prop.toPrettyStringDefault(0,eqn))^"\nMatching sub: "^(Terms.subToString(sub))^"]]]]\n"

fun ugenVars(s,uvars) = List.filter (fn v => Basic.isMemberEq(v,uvars,AthTermVar.athTermVarEq))
                                    (AT.getVars s)

fun varCondition(uvars,left,right) = 
  let fun isUVar(t) = (case AT.isVarOpt(t) of 
                         SOME(v) => Basic.isMemberEq(v,uvars,AthTermVar.athTermVarEq)
                       | _ => false)
  in
    (not(isUVar(right)))
    andalso 
    (Basic.subsetEq(ugenVars(left,uvars),ugenVars(right,uvars),AthTermVar.athTermVarEq))
    andalso
    (Int.<=(AT.size(left),AT.size(right)))
  end

fun allComponentsHold(p,ab) = 
  if ABase.isMember(p,ab) orelse Prop.isBooleanTrue(p) then true
  else 
    let fun allHold(q) = allComponentsHold(q,ab)
    in 
     (case Prop.isConj(p) of
           SOME(args) => (List.all allHold args)
         | _ => (case Prop.isDisj(p) of
                    SOME(args) => (List.exists allHold args)
                  | _ => (case Prop.isEquality(p) of
                             SOME(l,r) => AT.termEq(l,r)
                           | _ => (case Prop.isNeg(p) of
                                     SOME(q) => 
                                       (case Prop.isEquality(q) of
                                           SOME(l,r) => not(AT.termEq(l,r))
                                         | _ => (case Prop.isConj(q) of
                                                    SOME(args) => (List.exists  allHold (map Prop.makeComplement args))
                                                  | _ => (case Prop.isDisj(q) of
                                                            SOME(args) => (List.all allHold (map Prop.makeComplement args))
                                                          | _ => false)))
                                   | _ => false))))
    end

fun matchWithAntecedent(s,equation,uvars,antecedent,left,right,ab) = 
 let
 in
  (case AT.matchRW(s,left,uvars) of
      SOME(sub) => let val ant_uvars = List.filter (fn v => Basic.isMemberEq(v,uvars,AthTermVar.athTermVarEq))
                                                   (Prop.freeVars antecedent)
                       val antecedent' = Prop.applySub(sub,antecedent)
                       val varEq = AthTermVar.nameEq
                       val (sub',is_new) = if Basic.subsetEq(ant_uvars,AT.supp(sub),AthTermVar.athTermVarEq) then
                                              (SOME(sub),false)
                                           else Basic.findInListCont(ABase.getAll(ab), 
                                                                     (fn p => (case Prop.matchRW(p,antecedent',uvars) of
                                                                                  NONE => false
                                                                                | _ => true)),
                                                                     (fn p => (Prop.matchRW(p,antecedent',uvars),true)),
                                                                     (fn p => (NONE,false)))
                   in
                      (case sub' of
                         SOME(new_sub) => let val sub'' = if is_new then AT.composeSubs(new_sub,sub) else new_sub
			                      val antecedent'' = Prop.applySub(sub'',antecedent)
                                          in
                                             if allComponentsHold(antecedent'',ab) then
                                                SOME(AT.applySub(sub'',right),equation,sub'')
                                             else 
                                                NONE
                                          end
                       | _ => NONE)
                   end
    | _ => (case AT.matchRW(s,right,uvars) of
               SOME(sub) => if varCondition(uvars,left,right) andalso allComponentsHold(antecedent,ab)
                            then SOME(AT.applySub(sub,left),equation,sub)
                            else NONE
             | _ =>  NONE))
 end	     

fun getRewrite(t,equation,ab) = 
 let val res =    (case Prop.splitVars(equation) of 
                     (SOME(AbstractSyntax.forallCon),uvars,body) => 
                        (case Prop.isEquality(body) of 
                           SOME(left,right) => (case AthTerm.matchRW(t,left,uvars) of
                                                  SOME(sub) => SOME(AthTerm.applySub(sub,right),equation,sub)
                                                | _ => (case AthTerm.matchRW(t,right,uvars) of
                                                           SOME(sub) => if varCondition(uvars,left,right) then 
                                                                           SOME(AthTerm.applySub(sub,left),equation,sub)
                                                                        else NONE
                                                         | _ => NONE))
                        |  _ => (case Prop.isCond(body) of 
                                    SOME(antecedent,consequent) => 
                                       (case Prop.isEquality(consequent) of
                                           SOME(left,right) => 
                                              matchWithAntecedent(t,equation,uvars,antecedent,left,right,ab)
                                         | _ => NONE)
                                  | _ => (case Prop.isBiCond(body) of
                                             SOME(antecedent,consequent) =>                                            
                                                 (case Prop.isEquality(consequent) of
                                                     SOME(left,right) => 
                                                        matchWithAntecedent(t,equation,uvars,antecedent,left,right,ab)
                                                   | _ => (case Prop.isEquality(antecedent) of
                                                              SOME(left,right) => matchWithAntecedent(t,equation,uvars,consequent,left,right,ab)
                                                            | _ => NONE))
                                           | _ => NONE)))
                    | (NONE,[],body) => 
                        let val uvars = []
                        in
                          (case Prop.isEquality(body) of 
                             SOME(left,right) => (case AthTerm.matchRW(t,left,uvars) of
                                                    SOME(sub) => SOME(AthTerm.applySub(sub,right),equation,sub)
                                                  | _ => (case AthTerm.matchRW(t,right,uvars) of
                                                             SOME(sub) => if varCondition(uvars,left,right) then 
                                                                             SOME(AthTerm.applySub(sub,left),equation,sub)
                                                                          else NONE
                                                           | _ => NONE))
                          |  _ => (case Prop.isCond(body) of 
                                      SOME(antecedent,consequent) => 
                                         (case Prop.isEquality(consequent) of
                                             SOME(left,right) => 
                                                matchWithAntecedent(t,equation,uvars,antecedent,left,right,ab)
                                           | _ => NONE)
                                    | _ => (case Prop.isBiCond(body) of
                                               SOME(antecedent,consequent) =>                                            
                                                   (case Prop.isEquality(consequent) of
                                                       SOME(left,right) => 
                                                          matchWithAntecedent(t,equation,uvars,antecedent,left,right,ab)
                                                     | _ => (case Prop.isEquality(antecedent) of
                                                                SOME(left,right) => matchWithAntecedent(t,equation,uvars,consequent,left,right,ab)
                                                              | _ => NONE))
                                             | _ => NONE)))
                        end
                    | _ => NONE)
 in
    res
 end

fun listToStr(L) = "["^(Basic.printListStr(L,Int.toString,","))^"]"

fun getAllRewrites(s,equations,ab) = 
  let val positions = AT.dom(s)
      fun doPos(pos) = let val s_pos = AT.subterm(s,pos)
                           val results = Basic.mapSelect(fn eqn => getRewrite(s_pos,eqn,ab),equations,fn NONE => false | _ => true)
                       in 
                          map (fn SOME(t,eqn,sub) => (AT.posReplace(s,pos,t),eqn,sub)) results
                       end
      val L = map doPos positions
      val res = List.foldr op@ [] L
  in
    res 
  end

exception TermHashTable

structure Term_Space: TERM_STATE_SPACE = 
struct 
       type state = term_state 
       type term = AT.term;
       type state_table = (term,state) HashTable.hash_table
       fun eq(state({term=term1,...}),state({term=term2,...})) = AT.termEq(term1,term2);
       val size_hint = 128;
       fun makeStateTable() = HashTable.mkTable(AT.hashTerm, AT.termEq) (size_hint,TermHashTable);
       fun addState(s as state({term=t,...}),table) = (HashTable.insert table (t,s);table);
       fun isMember(s as state({term=t,...}),table) = (case (HashTable.find table t) of
                                                   SOME(_) => true
                                                 | _ => false);
       fun remove(s as state({term=t,...}),table) = 
        (((HashTable.remove table t);table) handle _ => table);
       fun show(term,parent,equation,score) =
                                              "\nState term: "^(AT.toStringDefault(term))^
                                              "\nParent: "^parent^"\nEquation: "^(Prop.toPrettyStringDefault(20,equation))^
                                              "\nScore: "^(Real.toString(score))
       fun stateToString(state({term,parent=NONE,equation,score,...})) = show(term,"NONE",equation,score)
         | stateToString(state({term,parent=SOME(s),equation,score,...})) = show(term,"SOME",equation,score)
end

structure Term_Search: STATE_SPACE_SEARCH = MakeStateSearch(structure state_space = Term_Space)

fun println(s) = print(s^"\n")

fun debugPrintln(s) = if Term_Search.isSilentOutput() then () else println(s)

fun getDerivation(s as state({term,parent=NONE,equation,score,matching_sub,...}),results) = (term,NONE,matching_sub)::results
  | getDerivation(s as state({term,parent=SOME(s'),equation,score,matching_sub,...}),results) = getDerivation(s',(term,SOME(equation),matching_sub)::results)
       
fun showSolution(final_state) = 
     let val derivation = getDerivation(final_state,[])
         fun showPair(term,NONE,sub) = debugPrintln(AT.toStringDefault(term))
           | showPair(term,SOME(eqn),sub) = debugPrintln("-------->\n"^(AT.toStringDefault(term))^"\nby:\n"^(Prop.toPrettyStringDefault(0,eqn)))
     in 
        (List.app showPair derivation;())
     end

fun search(term_1,term_2,eqns,style,max,silent,ab) = 
      let val _ = if silent then Term_Search.silenceOutput() else Term_Search.unSilenceOutput()
          fun preProcess(s as state({term,parent,equation,score,matching_sub,...}),more_states,count) =  ()
          fun score(state({score,...})) = score 
          fun expand(s as state({term,parent,equation,uplink_count,score,...})) = 
                let val new_terms_and_equations = getAllRewrites(term,eqns,ab)
                    val up_distance = uplink_count + 1 
                    val rup_distance = Real.fromInt(up_distance)
                    val rup_distance' = rup_distance
                in 
                   List.map (fn (t,eqn,sub) => state({term=t,parent=SOME(s),matching_sub=sub,uplink_count=up_distance,equation=eqn,
                                                      score=AT.distance(t,term_2)}))
                            new_terms_and_equations
                end
          val search_style = (case style of
                                 "depth-first" => Term_Search.depth_first
                               | "best-first"  => Term_Search.best_first
                               | _  => Term_Search.breadth_first)

          val search_fun = Term_Search.makeSearchFunction(preProcess,expand,search_style,SOME(score))
          val init_state: term_state = state({term=term_1,parent=NONE,uplink_count=0,matching_sub=AT.empty_sub,equation=Prop.makeEquality(term_1,term_1),
                                              score=AT.distance(term_1,term_2)})
          fun isGoalState(state({term,...})) = AT.termEq(term,term_2)
      in 
         search_fun(init_state,isGoalState,max)
      end

end