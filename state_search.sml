(*======================================================================

A functor that takes a state-space implementation and produces
a state-space-search implementation.

=======================================================================*)

functor MakeStateSearch (structure state_space: STATE_SPACE): STATE_SPACE_SEARCH = 

struct

structure state_space = state_space

open state_space

datatype search_style = depth_first | breadth_first | best_first

type search_function = state * (state -> bool) * int -> (state * int) option 

fun enterStates(states,table) = List.map (fn s => addState(s,table)) states

val silent_output = ref true

fun isSilentOutput() = !silent_output = true

fun silenceOutput() = silent_output := true

fun unSilenceOutput() = silent_output := false

fun printMsg(s) = if !silent_output then () else print(s)

val merge = Basic.merge

val mergeSort = Basic.mergeSortBuiltInComp

val no_progress_limit = 100

fun isMultiple(a,b) = Int.mod(a,b) = 0

fun makeSearchFunction(preProcess,expand,style,score_option) = 
     let val fringe_table = makeStateTable()
         val closed_table = makeStateTable()
         fun alreadySeen(s,table) = isMember(s,table)
         val scoreFun = (case score_option of
                            SOME(score) => score
                          | _ => (fn s => ~1.0))
         val (compareStates,sorted) = 
                               (case score_option of 
                                 SOME(score) => ((fn (s1,s2) => (Real.<=(score(s1),score(s2)))),
                                                  fn L => true)
                                      | _ => ((fn (s1,s2) => false), fn L => true))
         val (sort,merge) = (case style of  
                               depth_first => (fn states => states,fn (x,y,z) => x@y)
                             | best_first  => (fn states => mergeSort(states,compareStates),merge)
                             | _ => raise Basic.Never)
         fun noProgress(np_count) = np_count > no_progress_limit
         fun breadthFirstMakeFringe(sorted_new_states,tail_states,count) = tail_states@sorted_new_states 
         fun allElseMakeFringe(sorted_new_states,tail_states,count) = 
             if isMultiple(count,10) then 
                 let val L = sorted_new_states@tail_states
                     val (element_opt,rest) = let val r = MT.getRandomInt(Int.div(length(L),2))
                                              in
                                                  Basic.decomposeNth(L,r)
                                              end
                 in                       
                    (case element_opt of 
                        SOME(x) => x::rest
                      | _ => L)
                 end
             else merge(sorted_new_states,tail_states,compareStates)
         val makeFringe  = (case style of
                              breadth_first => breadthFirstMakeFringe
                            | _ => allElseMakeFringe)
         fun search([],closed,count,_,_,_,_) =  NONE
           | search(first_state::more_states,closed,count,isGoalState,max,last_score,np_count) = 
                let val _ = remove(first_state,fringe_table)
                    val _ = preProcess(first_state,more_states,count)
                in
                   if isGoalState(first_state) then 
                       SOME(first_state,count)
                   else (if count > max then 
                            (printMsg("Exceeded the maximum number of iterations: " ^ Int.toString(max));NONE)
                         else if noProgress(np_count) then (printMsg("\nSearch is getting stuck, no progress after: " ^ 
			      Int.toString(np_count) ^ ", aborting...\n");NONE)
                              else
                              let val new_score = scoreFun(first_state)
                                  val np_count' = if new_score < last_score then 0 else np_count + 1
                                  val new_states = expand(first_state)
                                  val new_states' = List.filter (fn s => (not(alreadySeen(s,closed_table)) andalso
                                                                          not(alreadySeen(s,fringe_table)))) 
                                                                new_states
                                  val ns_count = length(new_states')
                                  val _ = enterStates(new_states',fringe_table)
                                  val _ = addState(first_state,closed_table)
                                  val sorted_new_states = sort(new_states')
                                  val fringe' = makeFringe(sorted_new_states,more_states,count)
                              in
                                 search(fringe',first_state::closed,count+1,isGoalState,max,new_score,np_count')
                              end)
                end
         in
           (fn (init_state,isGoalState,max) => search([init_state],[],1,isGoalState,max,scoreFun(init_state),0))
        end

end