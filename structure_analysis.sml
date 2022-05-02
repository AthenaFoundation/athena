(*======================================================================

Some code for analyzing/processing inductive structures.

=======================================================================*)

structure StructureAnalysis = 

struct

open Data

structure ATV = AthTermVar
structure AT = AthTerm
structure P = Prop

type symbol = Symbol.symbol
type msymbol = ModSymbol.mod_symbol

val equality_symbol:declared_fun_sym = {name=Names.mequal_logical_symbol,obtype_params=[Symbol.symbol("T")],
                                        bits = Data.polyWord,
                                        argument_types=let val v = FTerm.makeFreshVar()
					 	       in [v,v] end,
                                        range_type=boolean_object_type,
                                        absyn_argument_types=[], arity = 2, prec=ref(Options.standard_bool_symbol_precedence), 
                                        assoc=ref(SOME(false)), 
                                        absyn_range_type=SymTerm.makeTaggedVar(Names.equal_logical_symbol,A.dum_pos)}

val _ = addFSym(declared(equality_symbol))

val evaluator_table:(AthTerm.term list -> AthTerm.term) S.htable = S.makeHTable()

fun addEvaluator(name,evaluator) = S.insert(evaluator_table,name,evaluator)

type logic_decs = {structures:ath_structure,constructors:ath_struc_constructor,
                   fsym_table:ath_fun_sym,evaluator_table:AthTerm.term list -> AthTerm.term}

fun printFunType(arg_types,ran_type) = 
              let fun print_arg_types([]) = ""
                    | print_arg_types([ot1]) = FTerm.toString(ot1,FTerm.varToString)
                    | print_arg_types(ot1::ot2::rest) = FTerm.toString(ot1,FTerm.varToString)^" "^
                                                        print_arg_types(ot2::rest)
                  val key = (case arg_types of [] => "" | _ => " -> ")
                  val domains = (case arg_types of [] => "" | _ => "["^(print_arg_types arg_types)^"]")
               in
                  domains^key^FTerm.toString(ran_type,FTerm.varToString)
               end


(************************************************************************************************
				Datatype shapes in inductive proofs 
*************************************************************************************************)

type struc_shape = {struc_sort:FTerm.term,shapes:AthTerm.term list}

fun isStrucObType(obtype) = 
      (case FTerm.isApp(obtype) of
          SOME(sort_name,_) => 
             (case findStructure(sort_name) of 
                 SOME(_) => SOME(sort_name)
               | _ => NONE)
        | _ => NONE)

fun isStructureType(obtype:FTerm.term) = case isStrucObType(obtype) of
                                            NONE => false
                                          | _ => true

fun printStrucShape(sh:struc_shape as {struc_sort,shapes}) = 
      let  val _ = print("\nShapes for structure "^FTerm.toString(struc_sort,FTerm.varToString)^":\n")
      in
         (Basic.printLnList(shapes,fn t => AT.toString(t,F.varToString));print("\n"))
      end

fun makeStrucShapes(struc_sort:FTerm.term) = 
    let fun makeGenericSymSort(struc_name,param_names) = 
    	    	  SymTerm.makeApp(struc_name,map SymTerm.makeVar param_names)
        fun f(c:ath_struc_constructor as {name,arity,absyn_argument_types,...},gen_sort,sub,mapping) = 
          let val arg_sorts = map (fn obtype => FTerm.translateFromSymTermWithSortVarMap(obtype,mapping)) 
                                  (map SymTerm.stripTags absyn_argument_types)
              val arg_sorts' = map (fn sort => FTerm.applySub(sub,sort)) arg_sorts 
              val atvs = map ATV.freshWithSort arg_sorts' 
          in
              if arity = 0 then AthTerm.makeSortedConstant(name,gen_sort)
              else AthTerm.makeApp(name,map AthTerm.makeVar atvs)
          end
        fun fLst([],_,sub,mapping,res) = res
          | fLst(c::more,gen_sort,sub,mapping,res) = fLst(more,gen_sort,sub,mapping,f(c,gen_sort,sub,mapping)::res)
    in
      (case FTerm.isApp(struc_sort) of
          SOME(struc_name,_) => 
             (case findStructure(struc_name) of 
                 SOME(ath_struc as {obtype_params,constructors,...}) =>
                       let val gen_sort_as_symterm = makeGenericSymSort(struc_name,obtype_params)
                           val (gen_sort,mapping) = FTerm.translateFromSymTermWithSortVarMapAux(gen_sort_as_symterm,Symbol.empty_mapping)
                       in
                          (case FTerm.match(struc_sort,gen_sort) of 
                              SOME(sub) =>  {struc_sort=struc_sort,shapes=fLst(constructors,struc_sort,
									         sub,mapping,[])}
                            | _ => raise Basic.Never)
                       end
               | _ => raise Basic.Never)
        | _ => raise Basic.Never)
    end

fun pt(t) = AT.toString(t,F.varToString)

val ndb = true

fun coveredShapes(sh:struc_shape as {struc_sort,shapes},
                  pats_as_ath_terms:AthTerm.term list) = 
   let val max_pat_height = Basic.maxLst(map AthTerm.height pats_as_ath_terms)
       fun printExpansions(l) = (print("\nHere are these expansions: ");
                                 Basic.printLnList(l,fn t => AT.toString(t,F.varToString));
				 print("\nPress return...");
                                 Basic.continue())
       fun tryExpansions(shape,open_vars) = 
           let val height_map = AthTerm.makeVarHeightMap(shape,open_vars)
               fun getCandidateVars(vars_and_heights) =
                     let fun f([],res) = res
                           | f(v::more,res) = (case GMap.lookUp(v,height_map,AthTermVar.athTermVarEq) of 
                                                  SOME(h) => if h > max_pat_height then f(more,res) 
                                                             else f(more,v::res)
                                                | NONE => raise Basic.Never)
                     in
                       f(open_vars,[])
                     end
               val candidate_vars = getCandidateVars(open_vars)
	       fun vtype_fun'(v) = (case AT.sortOfVarInTerm(v,shape) of
				      SOME(sort) => sort
                                    | _ => raise Basic.Never)
               fun filterCandidates(vars) = 
                    let fun f([],res) = res
                          | f(v::more,res) = 
                              let val obt = vtype_fun'(v)
                              in
                                 (case isStrucObType(obt) of 
                                     SOME(_) => f(more,(v,obt)::res)
                                   | _ => f(more,res))
                              end
                    in
                       f(vars,[])
                    end         
               val new_candidate_vars = filterCandidates(candidate_vars)                  
               fun expandShape(shape,(v,obt)) = 
                   let val _ = if ndb then () else 
                               (print("\nAbout to expand shape "^(AT.toString(shape,F.varToString))^
                                      "\non variable "^(ATV.toString(v,F.varToString)));
                                print("\nPress return...");Basic.continue())
                       val foo as {shapes,...} = makeStrucShapes(obt)
                       fun g([],res,_) = res
                         | g(s::more,res,i) = 
                                 let val sub = AthTerm.incSub(AthTerm.empty_sub,(v,s))
                                     val new = AthTerm.applySub(sub,shape)
                                 in
                                     g(more,new::res,i+1)
                                 end
                       val replacements = g(shapes,[],1)
                   in
                      (if ndb then () else printExpansions(replacements);replacements)
                   end
               fun expandShapeLst(shapes,candidate_var) = 
                    let fun f([],res) = res
                          | f(shape::more,res) = f(more,expandShape(shape,candidate_var)@res)
                    in
                       f(shapes,[])
                    end
               fun doVars([],results) = results
                 | doVars(v::more,shapes) = doVars(more,expandShapeLst(shapes,v))
           in
             if null(new_candidate_vars) then []
             else 
                  let val res = doVars(new_candidate_vars,[shape])
                      val _ = if ndb then () else
                              print("\nAnd here are the results of doVars on shape "^pt(shape)^":\n");
                      val _ = if ndb then () else printExpansions(res)
                  in
                     res
                  end
           end 
       fun tryMatchingSomePat(shape) = 
            let fun f([],ov,left_pats) = (false,ov,left_pats)
                  | f(pat::more_pats,ov,left_pats) = 
                       (case AthTerm.specialMatch(shape,pat) of
                           (true,_) => raise Basic.Never
                         | (false,ovars) => if null(ovars) then f(more_pats,ov,left_pats) 
                                            else f(more_pats,ovars@ov,pat::left_pats))
                val (b,ov,lpats) = f(pats_as_ath_terms,[],[]) handle Basic.Never => (true,[],[])
            in
               (b,Basic.removeDuplicatesEq(ov,AthTermVar.athTermVarEq),lpats)
            end
       fun loopShapes([]) = NONE
         | loopShapes(shape::more_shapes) = 
             case tryMatchingSomePat(shape) of
                (true,_,_) => loopShapes(more_shapes)
              | (false,open_vars,left_pats) => let val expansions = tryExpansions(shape,open_vars)
                                               in
                                                 if null(expansions) then SOME(shape)
                                                 else 
                                                    (case coveredShapes({struc_sort=struc_sort,
                                                                         shapes=expansions},left_pats) of
                                                        NONE => loopShapes(more_shapes)
                                                      | res => res)
                                               end
   in
     loopShapes(shapes) 
   end                    

fun exhaustStructure(pats_as_ath_terms,ob_type) = 
let val shapes = makeStrucShapes(ob_type)
in
  coveredShapes(shapes,pats_as_ath_terms)
end
     
fun getFirstNVars(n,prefix) = 
     let fun f(i,res) = if i < 1 then res
                        else
                            f(i-1,AthTermVar.athTermVar(prefix^Int.toString(i))::res)
     in
        f(n,[])
     end

fun doStrucSpan(struc:ath_structure as {constructors,...}) = 
       let fun makeConClause(t,con:ath_struc_constructor as {name,arity,bits,...}) = 
                 let val vars = getFirstNVars(arity,"x")
                     val vars_as_terms = map AthTerm.makeVar vars
                     val equality = Prop.makeEquality(t,AthTerm.makeApp(name,vars_as_terms))
                 in
                     Prop.makeEGen(vars,equality)
                 end
           val uvar = AthTermVar.athTermVar("v")
           val uvar_as_term = AthTerm.makeVar(uvar)
           val clauses = map (fn c => makeConClause(uvar_as_term,c)) constructors
           val body = if List.length(clauses) = 1 then hd(clauses) else Prop.makeDisjunction(clauses)
       in
          Prop.makeUGen([uvar],body)
       end

end (* end of structure StructureAnalysis *) 
