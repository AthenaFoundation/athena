(*======================================================================

An implementation of the proof simplification algorithms in
https://link.springer.com/article/10.1007/s10817-005-9000-3

=======================================================================*)

structure Simplify =

struct

datatype prim_rule = claim | dn | mp | both | leftAnd | rightAnd | cd 
                     | leftEither | rightEither | equiv | leftIff | rightIff 
                     | absurd | trueIntro | condRule | negRule

datatype prop =  atom of string
               | trueProp
               | falseProp
               | neg of prop
               | conj of prop * prop 
               | disj of prop * prop 
               | cond of prop * prop 
               | biCond of prop * prop

datatype proof = ruleApp of prim_rule * prop list 
               | assumeProof of prop * proof * bool
               | supAbProof of prop * proof * bool
               | compProof of proof * proof  


exception IllFormedProof

fun illFormed() = raise IllFormedProof

fun fp f = fn D => let val D' = f D
                    in
                       if D = D' then D else (fp f) D'
                    end

fun weave f [] = f
  | weave f (g::rest) = f o g o (weave f rest)

fun memberOf L x = List.exists (fn a => a = x) L

fun emptyIntersection(L1,L2) = not (List.exists (memberOf L2) L1)

fun remove(x,L) = List.filter (fn y => not(x = y)) L

fun removeDuplicates [] = []
  | removeDuplicates (x::rest) = x::removeDuplicates(remove(x,rest))

fun getThreadElements(compProof(D1,D2)) = D1::getThreadElements(D2)
  | getThreadElements(D) = [D]

fun makeThread([D]) = D
  | makeThread(D::rest) = compProof(D,makeThread(rest))
 
fun isClaim(ruleApp(claim,_)) = true
  | isClaim(_) = false

fun ruleConcl(claim,[P]) = P
  | ruleConcl(dn,[neg(neg(P))]) = P
  | ruleConcl(condRule,[P,Q]) = cond(P,Q)
  | ruleConcl(negRule,[P]) = neg(P)
  | ruleConcl(mp,[cond(P1,P2),P3]) = if (P1 = P3) then P2 else illFormed()
  | ruleConcl(both,[P1,P2]) = conj(P1,P2)
  | ruleConcl(leftAnd,[conj(P1,P2)]) = P1
  | ruleConcl(rightAnd,[conj(P1,P2)]) = P2
  | ruleConcl(equiv,[cond(P1,P2),cond(P3,P4)]) = 
      if P1 = P4 andalso P2 = P3 then biCond(P1,P2) else illFormed()
  | ruleConcl(leftIff,[biCond(P,Q)]) = cond(P,Q)
  | ruleConcl(rightIff,[biCond(P,Q)]) = cond(Q,P)
  | ruleConcl(leftEither,[P,Q]) = disj(P,Q)
  | ruleConcl(rightEither,[P,Q]) = disj(P,Q)
  | ruleConcl(cd,[disj(P1,P2),cond(P3,Q),cond(P4,Q')]) = 
     if P1 = P3 andalso P2 = P4 andalso Q = Q' then Q else illFormed()
  | ruleConcl(absurd,[P1,neg(P2)]) = if P1 = P2 then falseProp else illFormed()
  | ruleConcl(trueIntro,[]) = trueProp
  | ruleConcl(_) = illFormed()

fun concl(ruleApp(M,args)) = ruleConcl(M,args)
  | concl(assumeProof(P,D,_)) = cond(P,concl(D))
  | concl(supAbProof(P,D,_)) = neg(P)
  | concl(compProof(_,D2)) = concl(D2)
                                            
fun fa D = 
 let fun h(ruleApp(leftEither,[P1,P2])) = [P1]
       | h(ruleApp(rightEither,[P1,P2])) = [P2]
       | h(ruleApp(M,args)) = args 
       | h(assumeProof(P,D,_)) = remove(P,h(D))
       | h(supAbProof(P,D,_)) = remove(P,h(D))
       | h(compProof(D1,D2)) = 
           h(D1)@(remove(concl(D1),h(D2)))
 in
   removeDuplicates(h(D))
 end


fun makeStrict(assumeProof(P,D,mark)) = assumeProof(P,makeStrict(D),mark)
  | makeStrict(supAbProof(P,D,mark)) = supAbProof(P,makeStrict(D),mark)
  | makeStrict(compProof(D1,D2)) = 
     let val D1' = makeStrict(D1)
         val D2' = makeStrict(D2)
     in 
        if memberOf (fa D2') (concl D1') then compProof(D1',D2') else D2'
     end
  | makeStrict(D) = D

fun removeRepetitions(D) = 
 let fun RR(D,L) = 
        let val P = concl(D)
        in
           if memberOf L P then ruleApp(claim,[P])
           else
              case D of
                 assumeProof(hyp,D_b,mark) => assumeProof(hyp,RR(D_b,hyp::L),mark)
               | supAbProof(hyp,D_b,mark) => supAbProof(hyp,RR(D_b,hyp::L),mark)
               | compProof(D1,D2) => let val D1' = RR(D1,L)
                                          in
                                             compProof(D1',RR(D2,concl(D1')::L))
                                          end
               | _ => D
        end 
 in
    RR(D,[])
 end

fun elimClaims(assumeProof(P,D_b,mark)) = assumeProof(P,elimClaims(D_b),mark)
  | elimClaims(supAbProof(P,D_b,mark)) = supAbProof(P,elimClaims(D_b),mark)
  | elimClaims(compProof(D1,D2)) = 
      let val (D1',D2') = (elimClaims(D1),elimClaims(D2))
          val comp = compProof(D1',D2')
      in
         (case D1' of
             ruleApp(claim,_) => D2'
           | _ => (case D2' of 
                     ruleApp(claim,_) => 
                       if concl(D1') = concl(D2') then D1' else comp
                   | _ => comp))
      end
  | elimClaims(D) = D

val contract = fp (elimClaims o removeRepetitions o makeStrict)

fun H(compProof(D1,D2),L) = 
             let val (D1',L1,Delta1) = H(D1,L)
                 val (D2',L2,Delta2) = H(D2,L1)
             in
                (compProof(D1',D2'),L2,Delta1 @ Delta2)
             end
  | H(D,L) = let val C = concl(D)
             in
               if emptyIntersection(fa(D),L) then 
                  (ruleApp(claim,[C]),L,[D])
               else
                  (D,C::L,[])
             end

val maximizeScope = 
 let val rightLinearize = 
           let fun rl(assumeProof(P,D,b)) = assumeProof(P,rl(D),b)
                 | rl(supAbProof(P,D,b)) = supAbProof(P,rl(D),b)
                 | rl(compProof(D_l,D_r)) = 
                      (case D_l of
                          compProof(D1,D2) => rl(compProof(D1,compProof(D2,D_r)))
                        | _ => compProof(rl(D_l),rl(D_r)))
                 | rl(D) = D
           in
             rl
           end
     fun allMarked(assumeProof(_,D,mark)) = mark andalso allMarked(D)
       | allMarked(supAbProof(_,D,mark)) =  mark andalso allMarked(D)
       | allMarked(compProof(D1,D2)) = allMarked(D1) andalso allMarked(D2)
       | allMarked(ruleApp(_)) = true
     fun hoist(assumeProof(P,D_b,mark as false)) =
           if allMarked(D_b) then
              let val (D_b',_,Delta) = H(D_b,[P])
              in
                if not(null(Delta)) andalso concl(makeThread(Delta)) = concl(D_b')
                then makeThread(Delta@[ruleApp(condRule,[P,concl(D_b')])])
                else
                   makeThread(Delta@[assumeProof(P,D_b',true)])
              end
           else
              assumeProof(P,hoist(D_b),mark)
       | hoist(supAbProof(P,D_b,mark as false)) =     
           if allMarked(D_b) then
              let val (D_b',_,Delta) = H(D_b,[P])
              in
                if not(null(Delta)) andalso concl(makeThread(Delta)) = concl(D_b') 
                then makeThread(Delta@[ruleApp(negRule,[P])])
                else
                   makeThread(Delta@[supAbProof(P,D_b',true)])
              end
           else
              supAbProof(P,hoist(D_b),mark)
       | hoist(compProof(D1,D2)) = compProof(hoist(D1),hoist(D2))
       | hoist(D) = D
 in
    (fp (rightLinearize o hoist)) o rightLinearize 
 end

fun A(D) = 
  let fun T(assumeProof(P,D_b,mark),L) = 
            if memberOf L P then 
               let val D_b' = T(D_b,L)
               in
                  compProof(D_b',ruleApp(condRule,[P,concl(D_b')]))
               end
            else
               assumeProof(P,T(D_b,P::L),mark)
        | T(supAbProof(P,D_b,mark),L) = 
            if memberOf L P then 
               let val D_b' = T(D_b,L)
               in
                 compProof(D_b',ruleApp(negRule,[P]))
               end
            else
               supAbProof(P,T(D_b,P::L),mark)
        | T(compProof(D1,D2),L) = 
              let val D1' = T(D1,L)
              in
                compProof(D1',T(D2,concl(D1')::L))
              end
        | T(D,_) = D
  in
     T(D,fa(D))
  end

fun A3(assumeProof(P,D,mark)) = assumeProof(P,A3(D),mark)
  | A3(supAbProof(P,D,mark)) = supAbProof(P,A3(D),mark)
  | A3(compProof(assumeProof(P,D_b,mark),D)) = 
        let val (D_b',D') = (A3(D_b),A3(D))
            val (D'',_,Delta) = H(D',[cond(P,concl(D_b'))])
        in
          if memberOf (map concl (getThreadElements D)) P
          then 
             (if not(null(Delta)) andalso concl(makeThread(Delta)) = concl(D'')
              then makeThread(Delta)
              else 
                 makeThread(Delta@[assumeProof(P,D_b',mark),D'']))
          else 
              compProof(assumeProof(P,D_b',mark),D')
        end
  | A3(compProof(supAbProof(P,D_b,mark),D)) = 
        let val (D_b',D') = (A3(D_b),A3(D))
            val (D'',_,Delta) = H(D',[neg(P)])
        in
           if memberOf (map concl (getThreadElements D)) P 
           then 
               (if not(null(Delta)) andalso concl(makeThread(Delta)) = concl(D'')
                then makeThread(Delta)
                else
                   makeThread(Delta@[supAbProof(P,D_b',mark),D'']))
           else
               compProof(supAbProof(P,D_b',mark),D')
        end
  | A3(compProof(D1,D2)) = compProof(A3(D1),A3(D2))
  | A3(D) = D

val restructure =  weave maximizeScope [A,A3]

val simplify = contract o restructure

end (* of structure Simplify *)
