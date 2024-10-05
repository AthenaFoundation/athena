(*======================================================================

Code for dealing with definitions (of structures, symbols, functions, and
so on). This file also contains code for processing top-level phrases and
assertions.

=======================================================================*)

structure DefinitionProcessor = 

struct

structure N = Names 
structure D = Data
structure MS = ModSymbol
structure SV = SemanticValues

type mod_symbol = MS.mod_symbol

open StructureAnalysis

exception LoadedFileEx

val processString = Semantics.processString

val getValAndModMaps = Semantics.getValAndModMaps

fun debugPrint(str) = ()

fun setVal([],sym,v,SV.valEnv({val_map,mod_map})) = 
         SV.valEnv({val_map=Symbol.enter(val_map,sym,v),mod_map=mod_map})
  | setVal(m::rest,sym,v,given_env as SV.valEnv({val_map,mod_map})) =  
     let val _ = debugPrint("\nTrying to look up module name "^(Symbol.name m)^" on the mod_map of the given environment...\n")
     in
     (case Symbol.lookUp(mod_map,m) of 
         SOME(module:SV.module as {mod_name,env=e',open_mod_directives}) => 
               let val _ = if null(rest) then debugPrint("\nUpdating module: "^(MS.name mod_name)^" on an empty path.\n")
                           else debugPrint("\nUpdating module: "^(MS.name mod_name)^" on an non-empty path.\n")
                   val e'' = setVal(rest,sym,v,e')
                   val module':SV.module = {mod_name=mod_name,env=e'',open_mod_directives=open_mod_directives}
               in
                  SV.valEnv({val_map=val_map,mod_map=Symbol.enter(mod_map,m,module')})
               end
       | _ => given_env)
     end

fun forceSetVal([],sym,v,SV.valEnv({val_map,mod_map})) = 
      let val _ = ()
      in
         SV.valEnv({val_map=Symbol.enter(val_map,sym,v),mod_map=mod_map})
      end
  | forceSetVal(m::rest,sym,v,given_env as SV.valEnv({val_map,mod_map})) =  
     let val _ = debugPrint("\nTrying to look up module name "^(Symbol.name m)^" on the mod_map of the given environment...\n")
     in
     (case Symbol.lookUp(mod_map,m) of 
         SOME(module:SV.module as {mod_name,env=e',open_mod_directives}) => 
               let val _ = if null(rest) then debugPrint("\nUpdating module: "^(MS.name mod_name)^" on an empty path.\n")
                           else debugPrint("\nUpdating module: "^(MS.name mod_name)^" on an non-empty path.\n")
                   val e'' = forceSetVal(rest,sym,v,e')
                   val module':SV.module = {mod_name=mod_name,open_mod_directives=open_mod_directives,env=e''}
               in
                  SV.valEnv({val_map=val_map,mod_map=Symbol.enter(mod_map,m,module')})
               end
       | _ => let val empty_mod = SV.makeEmptyModule(m)
                  val given_env' = SV.valEnv({val_map=val_map,mod_map=Symbol.enter(mod_map,m,empty_mod)})
              in
                forceSetVal(m::rest,sym,v,given_env')
              end)
     end

structure Pos = Position

fun myPrint(msg) = if !(Options.silent_mode) then () else print(msg)

fun alwaysPrint(msg) = print(msg)

val pprint =  TopEnv.pprint

val top_assum_base = ABase.top_assum_base

fun addPropToGlobalAb(p,mod_path,string_opt) = 
    (top_assum_base := ABase.insert(p,!top_assum_base);
     P.addToModuleAb(mod_path,p,string_opt);
     top_assum_base := ABase.addAssertion(p,!top_assum_base))
                                     
fun addPropsToGlobalAb(props,mod_path,string_opt) = List.app (fn p => addPropToGlobalAb(p,mod_path,string_opt)) props
val top_val_env = SV.top_val_env 

fun ok() = myPrint("\nOK.\n")

fun error(position,msg) = genEx(msg,SOME(position),"")

exception DecError of string

val makeWord = Data.makeWord

fun decError(msg,SOME(pos)) = raise DecError("Error, "^A.posToString(pos)^": "^msg^".")
  | decError(msg,NONE) = raise DecError("Error:, "^msg^".")

val evError = Semantics.evError
val primError = Semantics.primError

fun evWarning(str,SOME(pos)) = myPrint("\nWarning, " ^ A.posToString(pos) ^ ": "^str^".\n")
 |  evWarning(str,NONE) = myPrint("\nWarning, "^str^".\n")

val num_ops_defined: Symbol.symbol option option ref = ref(NONE)

val dum_pos = Position.dummy_pos

fun checkStrucOrDomainReDefinition(name,pos) = 
    if MS.exists(structure_table,name) then
       (evWarning("the name "^MS.name(name)^" already refers to a structure",SOME(pos));true)
    else
        if MS.exists(sort_table,name) then 
           (evWarning("the name "^MS.name(name)^" already refers to a domain",SOME(pos));true)
        else 
           false

fun printDefinitionMessage(name,v,mod_path,is_private) = 
   if not(is_private) then 
      let val val_type = Semantics.getType(v)
      in
         myPrint "\n";
         myPrint (val_type^" ");
         (myPrint (SV.qualifyNameStr(name,mod_path)));
         myPrint " defined.";
         myPrint "\n"
      end
   else () 

fun checkStrucConOrFSymRedef(name:MS.mod_symbol,pos:A.position) = 
    case MS.find(constructor_table,name) of              
       SOME(c' as {mother_structure=msym,...}) => 
         evError("Duplicate symbol---the name "^MS.name(name)^" is already used as a "^
                   "constructor of "^MS.name(msym),SOME(pos))
     | NONE => if MS.exists(fsym_table,name) then
                  evError("Duplicate symbol---the name "^MS.name(name)^" is already used as "^
                          "a function symbol",SOME(pos))
               else ()

fun checkFSymRedef(name:MS.mod_symbol,pos:A.position) = 
    case MS.find(constructor_table,name) of              
       SOME(c' as {mother_structure=msym,...}) => 
         (evWarning("Duplicate symbol---the name "^MS.name(name)^" is already used as a "^
                   "constructor of "^MS.name(msym),SOME(pos));true)
     | NONE => if MS.exists(fsym_table,name) then
                  (evWarning("Duplicate symbol---the name "^MS.name(name)^" is already used as "^
                          "a function symbol",SOME(pos));true)
               else false

fun checkDistinctConstructors(con_names,con_positions) = 
    let fun f([],[]) = ()
          | f(name::more,pos::rest) = 
               if Basic.isMemberEq(name,more,MS.modSymEq) then
                  evError("Duplicate constructor: "^MS.name(name)^
                        "---constructors must have unique names",SOME(pos))
               else
                  f(more,rest)
          | f(_,_) = ()
        in
            f(con_names,con_positions)
    end

fun checkDistinctNames(names,positions,msg1,msg2) = 
    let fun f([],[],_) = ()
          | f(name::more,pos::rest,members) = 
               if Basic.isMemberEq(name,members,MS.modSymEq) then
                  evError(msg1^MS.name(name)^msg2,SOME(pos))
               else
                  f(more,rest,name::members)
          | f(_,_,_) = ()
    in
           f(names,positions,[])
    end

fun checkDistinctSNames(names,positions,msg1,msg2) = 
    let fun f([],[],_) = ()
          | f(name::more,pos::rest,members) = 
               if Basic.isMemberEq(name,members,Symbol.symEq) then
                  evError(msg1^Symbol.name(name)^msg2,SOME(pos))
               else
                  f(more,rest,name::members)
          | f(_,_,_) = ()
    in
           f(names,positions,[])
    end

fun areInhabited(new_structures) = 
let val structure_number = length(new_structures)    
    val bit_array = Array.array(structure_number,0)
    fun ithStructure(i) = List.nth(new_structures,i)
    fun ithStrucName(i) = 
          (case List.nth(new_structures,i) of
              struc:ath_structure as {name,...} => name)
    val struc_names = map #name new_structures
    fun isReflexive(c:ath_struc_constructor as {absyn_argument_types,...}) = 
              Basic.exists(struc_names,(fn struc_name => Basic.exists(absyn_argument_types,
                                        fn t => SymTerm.fsymOccursInTagged(struc_name,t))))
    val doFirstIteration =  
         let val i = ref(0)
             in
               while (!i < structure_number) do
                  (case List.nth(new_structures,!i) of
                      struc:ath_structure as {constructors,...} =>
                         (if Basic.exists(constructors,
                                    (fn c:ath_struc_constructor =>
                                        not(isReflexive(c)))) then
                             Array.update(bit_array,!i,1)
                          else ();
                          Basic.inc(i)))
         end
    fun checkIthStructure(i) = 
         let fun checkCon(c:ath_struc_constructor as {absyn_argument_types,...}) = 
                    let val i = ref(0)
                        val con_passes = ref(true)
                        in
                          ((while ((!i < structure_number) andalso !con_passes) do
                              if (Array.sub(bit_array,!i) = 0) andalso 
                                 Basic.exists(absyn_argument_types,(fn t => 
                                              SymTerm.fsymOccursInTagged(ithStrucName(!i),t)))
                              then
                                 con_passes := false
                              else Basic.inc(i));
                           !con_passes)
                    end
             in
                (case ithStructure(i) of
                   struc:ath_structure as {name,arity,obtype_params,constructors,free,option_valued_selectors} =>
                      if Array.sub(bit_array,i) = 0 andalso 
                         Basic.exists(constructors,checkCon) then
                         (Array.update(bit_array,i,1);true)
                      else
                         false)
         end
    fun loop() = 
          let val iterations = ref(1)
              val done = ref(false)
              fun iterate() = 
                    let val change = ref(false)
                        fun doSub(i) = 
                                if i >= structure_number then ()
                                else 
                                   let val r_i_promoted = checkIthStructure(i)
                                       in
                                         (if r_i_promoted then 
                                             change := true
                                          else ();
                                             doSub(i+1))
                                   end
                        in
                          (doSub(0); 
                           Basic.inc(iterations); 
                           if !iterations >= structure_number orelse
                              not(!change) then done := true else ())
                    end
              in
                 while not(!done) do
                       iterate()
          end
    fun getRes() = 
           let val j = ref(0)
               val res = ref(true)
               in
                 (loop();
                  while ((!j < structure_number) andalso (!res = true)) do
                     if Array.sub(bit_array,!j) = 0 then
                        res := false
                     else Basic.inc(j);
                  !res)
           end
    in
      getRes()
end

fun expandSortAbbreviationsInStrucDef(absyn_struc:A.absyn_structure as {name,pos,obtype_params,constructors,free},mod_path) = 
   let fun expandConstructorSorts(con:A.absyn_structure_constructor as {name,pos,selectors,argument_types}) = 
	     let val res:A.absyn_structure_constructor =
                       {name=name,pos=pos,selectors=selectors,argument_types = 
                                           map (fn tt => Terms.replaceTaggedSymTermConstants(
                                                tt,fn sym => MS.find(Data.sort_abbreviations,sym),A.dum_pos))
                  argument_types}
             in
               res
             end
       val res:A.absyn_structure = {name=name,pos=pos,obtype_params=obtype_params,
				    constructors = map expandConstructorSorts constructors,free=free}
   in
     res
   end

fun expandSortAbbreviationsInStrucDefLst(absyn_struc_list,mod_path) = 
       map (fn a => expandSortAbbreviationsInStrucDef(a,mod_path)) absyn_struc_list

fun expandSortAbbreviationsInFSymDecl(absyn_fsym:A.absyn_fsym as {name,pos,obtype_params,input_transformer,
                                      argument_types,range_type,prec,assoc,overload_sym,...},mod_path) =
            
        let fun f sym = let val full_name = (case MS.split(sym) of
                                               (mod_path',sym_name) => (case mod_path' of
                                                                          [] => SV.qualifyName(sym_name,mod_path)
                                                                        | _ => sym))
                            val _ = ()
                        in
                           MS.find(Data.sort_abbreviations,full_name)
                        end
            val res:A.absyn_fsym = {name=name,pos=pos,obtype_params=obtype_params,input_transformer=input_transformer,
                                    argument_types = map (fn tt => Terms.replaceTaggedSymTermConstants(
                                                          tt,f,A.dum_pos))
                                                     argument_types,prec=prec,assoc=assoc,overload_sym=overload_sym,
                                    range_type = Terms.replaceTaggedSymTermConstants(range_type,f,A.dum_pos)}
        in
           res
        end

fun checkNewFunSym(sym,pos) = 
            let val str = Symbol.name(sym) 
                fun f1() = (case A.getAthNumber(str) of  
                               SOME(ath_num) => evError("Duplicate symbol---the name "^str^
                                                        " is already used as a "^"function symbol",SOME(pos))
                             | _ => ())
            in f1() end

fun checkConNames(con_names_and_positions) = 
     List.app (fn (name,pos) => checkNewFunSym(name,pos)) con_names_and_positions

fun makeUniqueDTName(length) = 
       let val prefix = "TTuple-"^(Int.toString(length))
           fun trySuffix(i) = let val new_name_sym = A.makeMS(prefix^"_"^(Int.toString(i)),NONE)
                              in
                                if Data.isStructure(new_name_sym) then trySuffix(i+1) else new_name_sym
                              end
           val first_try = A.makeMS(prefix,NONE)
       in 
          if Data.isStructure(first_try) then trySuffix(0) else first_try
       end

fun makeUniqueConName(length) = 
       let val prefix = "ttuple-"^(Int.toString(length))
           fun trySuffix(i) = let val new_name_sym = A.makeMS(prefix^"_"^(Int.toString(i)),NONE)
                              in
                                if Data.isStructureConstructorBool(new_name_sym) then trySuffix(i+1) else new_name_sym
                              end
           val first_try = A.makeMS(prefix,NONE)
       in 
          if Data.isStructureConstructorBool(first_try) then trySuffix(0) else first_try
       end

fun addTempDT(len) = 
     let val dt_name = makeUniqueDTName(len)
         val con_name = makeUniqueConName(len)
         fun makeParam(i) = {name=Symbol.symbol("S"^(Int.toString(i))),pos=A.dum_pos}
         fun makeNParams(n,res) = if n = 0 then rev res else makeNParams(n-1,(makeParam n)::res)
         val obtype_params = makeNParams(len,[])
         val obtype_params_as_symbols = map #name obtype_params
         val obtype_params_as_SymTerms = map SymTerm.makeVar obtype_params_as_symbols	 
         val arg_types = List.map (fn t => Terms.putBogusTags(t,A.dum_pos)) obtype_params_as_SymTerms
         val arg_types_as_SymTerms = map SymTerm.stripTags arg_types
         val range_type_as_SymTerm = SymTerm.makeApp(dt_name,obtype_params_as_SymTerms)
         val range_type_as_AbSynTerm:A.absyn_term = Terms.putBogusTags(range_type_as_SymTerm,A.dum_pos)
         val types_as_FTerms = Terms.SymTermsToFTerms(range_type_as_SymTerm::arg_types_as_SymTerms)
         val argument_types_as_FTerms = tl types_as_FTerms
         val range_type_as_FTerm = hd types_as_FTerms
         val c:Data.ath_struc_constructor = 
              {name=con_name,arity=len,mother_structure=dt_name,reflexive=false,bits=makeWord({poly=true,pred_based_sig=false}),
               argument_types=argument_types_as_FTerms,range_type=range_type_as_FTerm,prec=ref(110),
               absyn_argument_types=arg_types,assoc=ref(SOME(true)),selectors=List.map (fn _ => NONE) arg_types,
               sym_range_type=range_type_as_SymTerm}
         val _ = (Data.addFSym(Data.struc_con(c));Data.addConstructor(c))
         val res:Data.ath_structure = {name=dt_name,arity=len,obtype_params=obtype_params_as_symbols,option_valued_selectors=false,
                                       constructors=[c],free=true}
         val _ = MS.insert(Data.structure_table,dt_name,res)
     in
        (dt_name,con_name,res)
     end

fun removeDT(dt:Data.ath_structure as {name=dt_name,constructors,...}) = 
  let fun handleSelector(NONE) = ()
        | handleSelector(SOME(ms)) = (Data.removeFSymByName(ms); 
                                      MS.removeHT(Data.selector_table,ms);
                                      Semantics.removeTopValEnvBinding(ModSymbol.lastName(ms)))
      fun removeConstructor(c:Data.ath_struc_constructor as {name,selectors,...}) = 
         (List.map handleSelector selectors;
          Data.deleteConstructor(c);
          Data.removeFSymByName(name);
          Semantics.removeTopValEnvBinding(MS.lastName name))
  in
     ((List.app removeConstructor constructors);Data.deleteStructure(dt))
  end

fun fdCondition(g,args,right,right_fsyms) = 
          let val left_syms = AT.termSymbolsLst(args)
              val cond1 = List.all isStructureConstructorBool left_syms 
          in
             if cond1 andalso (not(List.null(left_syms)) orelse not(Basic.isMemberEq(g,right_fsyms,AT.fsymEq))) 
              then SOME(g) else NONE
          end

fun fdConditionNew(g,left_args,right_opt,right_syms,guards,all_args) = 
          let val left_syms = AT.termSymbolsLst(left_args)
              val left_vars = Basic.flatten(List.map AT.getVars left_args)
              val guard_vars = Basic.flatten(List.map Prop.freeVars guards)
              val right_vars = (case right_opt of
                                   SOME(right) =>AT.getVars(right)
                                  | _ => [])
              val cond0 = true (* not(Basic.hasDuplicates(left_vars,ATV.nameEq)) *)
              val cond1 = List.all isStructureConstructorBool left_syms 
              val cond2 = Basic.subsetEq(right_vars,left_vars@guard_vars,ATV.nameEq)
	      val cond3 = (not(null(guards)) orelse (not(List.null(left_syms)) orelse not(Basic.isMemberEq(g,right_syms,AT.fsymEq))))
              val ok = cond0 andalso cond1 andalso cond2 andalso cond3
          in
             if ok then 1 else 
                (if not(cond1) then ~1
                 else if not(cond2) then ~2 else ~3)
          end

fun fdConditionNewRelaxed(g,left_args,right_opt,right_syms,guards,all_args) = 
          let 

              val left_syms = AT.termSymbolsLst(left_args)
              val left_vars = Basic.flatten(List.map AT.getVars left_args)
              val right_vars = (case right_opt of
                                   SOME(right) =>AT.getVars(right)
                                  | _ => [])
              val guard_vars = Basic.flatten(List.map Prop.freeVars guards)
              val cond2 = Basic.subsetEq(right_vars,left_vars@guard_vars,ATV.nameEq)
	      val cond3 = (not(null(guards)) orelse (not(List.null(left_syms)) orelse not(Basic.isMemberEq(g,right_syms,AT.fsymEq))))
	      val ok = cond2 andalso cond3
          in
            if ok then 1 else (if not(cond2) then ~2 else ~3)
          end

fun isDefiningBody0(p) = 
       (case Prop.isEquality(p) of 
           SOME(left,right) => 
             (case AT.isApp(left) of
                 SOME(g,args) => fdCondition(g,args,right,AT.termSymbols(right))
               | _ => NONE)
         | _ => (case Prop.isCond(p) of
                    SOME(_,p2) => isDefiningBody0(p2)
                  | _ => NONE))

val isDefiningBody = isDefiningBody0

fun makeProp(uvars,guards,left,right,eq_opt:Prop.prop option) = 
  let fun makeConjunction([guard]) = guard
        | makeConjunction(guard::guards) = let val prop = makeConjunction guards 
                                           in 
                                              Prop.makeConjunction([guard,prop])
                                           end
  in
      if null(guards) then
         (case eq_opt of
             SOME(e) => Prop.makeUGen(uvars,e)
           | NONE => Prop.makeUGen(uvars,Prop.makeEquality(left,right)))
      else 
         (case eq_opt of
             SOME(e) => let val guard = makeConjunction(rev guards)
                        in Prop.makeUGen(uvars,Prop.makeConditional(guard,e))
                        end
           | NONE => let val guard = makeConjunction(rev guards)
                     in Prop.makeUGen(uvars,Prop.makeConditional(guard,Prop.makeEquality(left,right)))
                     end)
  end

fun getTermSymbols(t) = Basic.filterOut(AT.termSymbols t,Data.isStructureConstructorBool)
fun getTermSymbols'(t) = AT.termSymbols(t)
fun getTermSymbolsLst(props) = 
  let val term_syms = AT.termSymbolsLst(Basic.flatten(map P.allAtoms props))
  in
    Basic.filterOut(term_syms,Data.isStructureConstructorBool)
  end

fun isIdentity(p) = (case Prop.isEquality(p) of 
                       NONE => false
                     | _ => true)

fun isVarEquality(p) = 
   (case Prop.isAtom(p) of
      SOME(t) => (case AT.isApp(t) of 
                     SOME(f,args) => 
                        if MS.modSymEq(N.mequal_logical_symbol,f) then   
                           let val left = hd(args)
                               val right = hd(tl(args))
                           in
			      AT.isVar(left) andalso AT.isVar(right)
                           end
                        else false
                    | _ => false)
    | _ => (case Prop.isConj(p) of
              SOME(props) => Basic.forall(props,isVarEquality)
            | _ => false))

(***** 

allVarEqualities below is meant to detect a conditional identity all 
of whose guards are equalities of the form x1 = y1, ..., xn = yn. 
Often, the conclusion of such a rule is of the form 
(= (C x1 ... xn) (C y1 ... yn)) for a constructor C, and we want 
to avoid treating such a congruence rule as a "defining" axiom for 
the constructor C. This is avoided in the part of isDefiningBodyNew
that applies allVarEqualities; see the line 

if MS.modSymEq(g,h) andalso Data.isStructureConstructorBool(g)  andalso allVarEqualities(guards)

where g and h are the top function symbols of the left and right sides
of the consequent identity. 

****)

fun allVarEqualities(guards) = Basic.forall(guards,isVarEquality)

fun isDefiningBodyNew(p,uvars,guards,must_be_a_defining_equation) = 
  let val fdCondition = if  must_be_a_defining_equation then fdConditionNew else fdConditionNewRelaxed
  in
       (case Prop.isAtom(p) of
           SOME(t) => (case AT.isApp(t) of 
                          SOME(f,args) => 
                             if MS.modSymEq(N.mequal_logical_symbol,f) then
                               let val left = hd(args)
                               in
                                (case AT.isApp(left) of
                                   SOME(g,args') => let val right =  hd(tl(args))
                                                        val right_syms = getTermSymbols(right)
							val left_syms = getTermSymbols'(left)
							val guard_syms = (getTermSymbolsLst guards) 
 							val fd_cond = fdCondition(g,args',SOME right,right_syms,guards,args)
							val res = {fsym=g,defining_props=[makeProp(uvars,guards,left,right,SOME(p))],
  	 			                                   guard_syms=guard_syms,left_syms=left_syms,right_syms=right_syms}
                                                    in
						       (case AT.isApp(right) of
                                                           SOME(h,args) => if MS.modSymEq(g,h) andalso 
							                      Data.isStructureConstructorBool(g) andalso 
									      let val res = allVarEqualities(guards) 
								              in
                                                                                 res
								              end
							                   then NONE
									   else
                                                                             if (fd_cond > 0) then SOME(res) else NONE
                                                       | _ => if (fd_cond > 0) then SOME(res) else NONE)
                                                    end
                                 | _ => let val right =  hd(tl(args))
                                        in
                                         (case (AT.isVarOpt(left),AT.isVarOpt(right)) of
                                             (SOME(v1),SOME(v2)) => 
                                                 let val sort = ATV.getSort(v1)
                                                 in
                                                   (case FTerm.isApp(sort) of
                                                      SOME(sort_con,_) => 
                                                         if Data.isNonFreeDT(sort_con) then 
                                                            let val guard_conj = Prop.makeConjunction(guards)
                                                                val guard_fvs = Prop.freeVarsSet(guard_conj)
                                                                val S = ATV.addLst([v1,v2],ATV.empty)
                                                                val cond = ATV.equal(S,guard_fvs)
							    in
                                                                if cond then
                                                                   let fun f(t1,t2) = Prop.replace(v2,t2,Prop.replace(v1,t1,guard_conj))
                                                                       val _ = MS.insert(Prop.structure_equality_table,sort_con,f)
                                                                   in
                                                                     NONE 
                                                                   end
                                                                else NONE
                                                            end
                                                         else NONE
                                                   | _ => NONE)
                                                  end 
                                             | _ => NONE)
                                        end)
                               end
                             else let val fd_cond = fdCondition(f,args,NONE,[],guards,args)
                                  in (if fd_cond >0 then 
                                      SOME({defining_props=[makeProp(uvars,guards,t,AT.true_term,NONE)],fsym=f,guard_syms=(getTermSymbolsLst guards),left_syms=[],right_syms=[]})
                                      else NONE)
                                  end
                        | _ => NONE)
         | _ => (case Prop.isCond(p) of
                    SOME(p1,p2) => isDefiningBodyNew(p2,uvars,p1::guards,must_be_a_defining_equation)
                  | _ => (case Prop.isNeg(p) of
                             SOME(q) =>  (case Prop.isAtom(q) of
                                             SOME(t) => (case AT.isApp(t) of 
                                                            SOME(f,args) => let val fd_cond = fdCondition(f,args,NONE,[],guards,args)
                                                                            in  
                                                                            if  fd_cond > 0 
                                                                            then SOME({defining_props=[makeProp(uvars,guards,t,AT.false_term,NONE)],
                                                                                       fsym=f,guard_syms=(getTermSymbolsLst guards),left_syms=[],right_syms=[]})
                                                                            else NONE
                                                                            end
                                                          | _ => NONE)
                                           | _ => NONE)
                           | _ => (case Prop.isBiCond(p) of
                                      SOME(p1,p2) => (case Prop.isAtom(p1) of 
                                                         SOME(t1) => 
                                                            (case Prop.isAtom(p2) of 
                                                                 SOME(t2) => if isIdentity(p1) then 
                                                                                (if ATV.isSubset(P.freeVarsSet(p2),P.freeVarsSet(p1)) 
                                                                                 then (case isDefiningBodyNew(p1,uvars,p2::guards,must_be_a_defining_equation) of 
                                                                                          NONE =>  isDefiningBodyNew(p2,uvars,p1::guards,must_be_a_defining_equation)
                                                                                        | res => res)
                                                                                 else NONE)
                                                                              else 
                                                                                if isIdentity(p2) then isDefiningBodyNew(Prop.makeEquality(t1,t2),uvars,guards,must_be_a_defining_equation)
                                                                                else   
                                                                                   isDefiningBodyNew(Prop.makeEquality(t1,t2),uvars,guards,must_be_a_defining_equation)

                                                               | _ => (case (isDefiningBodyNew(p1,uvars,p2::guards,must_be_a_defining_equation),
                                                                             isDefiningBodyNew(Prop.makeNegation(p1),uvars,(Prop.makeNegation p2)::guards,
                                                                                               must_be_a_defining_equation)) of
                                                                          (SOME({defining_props=dp1,fsym=f1,guard_syms=gs,right_syms=rs1,left_syms=ls1,...}),
                                                                           SOME({defining_props=dp2,...})) =>
                                                                            (if ATV.isSubset(P.freeVarsSet(p2),P.freeVarsSet(p1)) 
                                                                             then SOME({defining_props=dp1@dp2,fsym=f1,guard_syms=gs,right_syms=rs1,left_syms=ls1})
									     else NONE)
                                                                        | _ => NONE)
								       )
                                                       | _ => NONE)
                                    | _ => NONE))))
  end
       
fun isDefiningBody(p) = 
       (case Prop.isEquality(p) of 
           SOME(left,right) => 
             (case AT.isApp(left) of
                 SOME(g,args) => 
                        let val left_syms = AT.termSymbolsLst(args)
                            val cond1 = List.all isStructureConstructorBool left_syms 
                            val cond2 = not(List.null(left_syms)) orelse not(Basic.isMemberEq(g,AT.termSymbols(right),AT.fsymEq))
                        in
                           if cond1 andalso cond2 then SOME(g) else NONE
                        end
               | _ => NONE)
         | _ => (case Prop.isCond(p) of
                    SOME(antecedent,p2) => if ATV.isSubset(P.freeVarsSet(antecedent),P.freeVarsSet(p2)) then isDefiningBody(p2) else NONE 
                  | _ => NONE)) 

fun isDefiningEquationForSomeFunSym(p) = 
 (case P.splitVars(p) of 
     (SOME(A.forallCon),_,body) => isDefiningBody(body)
   | _ => isDefiningBody(p))

fun isDefiningEquationForSomeFunSymNew(p,must_be_a_defining_equation) = 
 (case P.splitVars(p) of 
     (SOME(A.forallCon),uvars,body) => isDefiningBodyNew(body,uvars,[],must_be_a_defining_equation)
   | _ => isDefiningBodyNew(p,[],[],must_be_a_defining_equation))

fun isDefiningEquation(p,f) = 
       (case isDefiningEquationForSomeFunSym(p) of
           SOME(g) => AT.fsymEq(f,g)
         | _ => false)

fun getDefiningEquations(f,ab) = 
  let val assertions = ABase.getAssertions(ab) 
      fun allConstructors(_) = true 
      fun test(p) = isDefiningEquation(p,f)
  in 
    List.filter test assertions
  end

fun checkFunDef(f,new_equation,ab,pos,file,which_check) = 
  let val arity = (case Data.isTermConstructor(f) of
                    SOME(i) => i) 
      val (dt_name,con_name,dt) = addTempDT(arity)
      val cname = MS.name(con_name)
      val sym_name = MS.name(f)
      fun getLeftSide(p,inside_cond) = 
            (case Prop.splitVars(p) of 
               (SOME(A.forallCon),vars,body) => 
                  (case Prop.isEquality(body) of 
                      SOME(l,_) => (l,false)
                    | _ => (case Prop.isCond(body) of
                              SOME(_,p2) => (getLeftSide(p2,true))))
              | _ => (case Prop.isEquality(p) of 
                         SOME(l,_) => (l,inside_cond)
                       | _ => (case Prop.isCond(p) of
                                  SOME(_,p2) => getLeftSide(p2,true))))
      val old_equations = getDefiningEquations(f,ab)
      val equations = new_equation::old_equations 
      val old_left_sides = List.map (fn eq => getLeftSide(eq,false)) old_equations
      val new as (new_left_side,is_new_cond) = getLeftSide(new_equation,false)
      val left_sides = new::old_left_sides 
      fun makeConTerm(left) = AT.makeApp(con_name,AT.getChildren left)
      fun checkDisjointness() = List.map 
                                 (fn (old_left_side,is_old_cond) => if is_old_cond orelse is_new_cond then () else 
                                  (case AT.unify(old_left_side,new_left_side) of
                                      SOME(sub) =>  
                                        myPrint("\n[Warning, "^(A.posToString pos)^": "^
                                                "this new equational axiom\ndefining "^sym_name^
                                                " is not disjoint from previous axioms. For example,\nboth it"^
                                                " and at least one previous axiom apply to every instance of this term:\n"^
                                                (AT.toStringDefault(AT.applySub(sub,new_left_side)))^".]\n")
                                    | _ => ()))
                                old_left_sides 
      val at_least_one_conditional_equation = List.exists (fn (_,b) => b = true) left_sides
      fun checkExaustiveness() = 
             let 
                 val (param_sorts,result_sort,is_poly,has_pred_based_sorts) = Data.getSignature(con_name) 
                                                             handle _ => (print("\nCan't get the signature of "^cname);raise Basic.Never)
                 val left_patterns = (List.map (fn (side,is_cond) => makeConTerm side) left_sides)
                 val arg_sorts = (case (Data.getSignature f) of
                                    (asorts,_,_,has_pred_based_sorts) => asorts)
                 val uvar = ATV.freshWithSort(FTerm.makeApp(dt_name,arg_sorts))
                 val uvar_sort = ATV.getSort(uvar)
                 val str = if at_least_one_conditional_equation then " should be " else " are " 
             in
               (case StructureAnalysis.exhaustStructure(left_patterns,uvar_sort) of
                   SOME(t) => let val t' = (case AT.isApp(t) of 
                                              SOME(_,args) => AT.makeApp(f,args))
                              in
                                  myPrint("\n[Warning: The current equational axioms for "^sym_name^" are not\nexhaustive. "^
                                          "For example, the value of every ground instance of:\n"^(AT.toStringDefault t')^
                                          "\nis currently unspecified.]\n")
                              end
                  | _ => myPrint("\nDefinition of "^sym_name^" is complete; the current equational axioms"^str^"exhaustive.\n"))
             end
      val _ = (case which_check of 
                  "disjoint" => (checkDisjointness();())
                | "exhaust" =>  checkExaustiveness()
                | "both" => (checkDisjointness();checkExaustiveness()))
      val _ = removeDT(dt)
  in
     ()
  end    

fun getAllRemainingPatterns(patterns) = 
  let val first_pattern = hd(patterns)
      val arg_sorts = map AT.getSort (AT.getChildren first_pattern)
      val f = (case AT.isApp(first_pattern) of
                  SOME(g,_) => g)
      val arity = (case Data.isTermConstructor(f) of
                    SOME(i) => i) 
      val (dt_name,con_name,dt) = addTempDT(arity)
      val uvar = ATV.freshWithSort(FTerm.makeApp(dt_name,arg_sorts))
      val uvar_sort = ATV.getSort(uvar)
      val cname = MS.name(con_name)
      val sym_name = MS.name(f)
      fun makeConTerm(left) = AT.makeApp(con_name,AT.getChildren left)
      fun loop(patterns) = 
             let val (param_sorts,result_sort,is_poly,has_pred_based_sorts) = Data.getSignature(con_name) 
                                                             handle _ => (print("\nCan't find the signature of "^cname);raise Basic.Never)
                 val patterns' = (List.map makeConTerm patterns)
             in
               (case StructureAnalysis.exhaustStructure(patterns',uvar_sort) of
                   SOME(t) => (case AT.isApp(t) of 
                                  SOME(_,args) => loop(patterns@[AT.makeApp(f,args)]))
                 | _ => patterns)
             end
      val res = loop(patterns)
      val _ = removeDT(dt)
  in
    res
  end

fun getPatternsPrimUFun(SV.listVal(tvals),env,_) = 
               let val terms = TopEnv.getTermsNoPos(tvals,"the first argument of "^N.getPatternsFun_name)
	           val res = getAllRemainingPatterns(terms)
               in 
                   SV.listVal(map SV.termVal res)
               end    
  | getPatternsPrimUFun(v2,env,_) = primError(TopEnv.wrongArgKind(N.getPatternsFun_name,2,SV.listLCType,v2))

val _ = TopEnv.updateTopValEnvLstOldAndFast([(N.getPatternsFun_symbol,SV.primUFunVal(getPatternsPrimUFun,TopEnv.default_ufv_pa_for_procs N.getPatternsFun_name))])

fun getLeftSide(p,inside_cond) = 
            (case Prop.splitVars(p) of 
               (SOME(A.forallCon),vars,body) => 
                  (case Prop.isEquality(body) of 
                      SOME(l,_) => (l,false)
                    | _ => (case Prop.isCond(body) of
                              SOME(_,p2) => (getLeftSide(p2,true))))
              | _ => (case Prop.isEquality(p) of 
                         SOME(l,_) => (l,inside_cond)
                       | _ => (case Prop.isCond(p) of
                                  SOME(_,p2) => getLeftSide(p2,true))))

fun checkFunDef(f,equations,pos_option) = 
  let val arity = (case Data.isTermConstructor(f) of
                    SOME(i) => i) 
      val (dt_name,con_name,dt) = addTempDT(arity)
      val cname = MS.name(con_name)
      val sym_name = MS.name(f)
      val all_left_sides = List.map (fn eq => getLeftSide(eq,false)) equations 
      fun makeConTerm(left) = AT.makeApp(con_name,AT.getChildren left)
      val error = ref(false)  
      val at_least_one_conditional_equation = List.exists (fn (_,b) => b = true) all_left_sides
      val myPrint0 = myPrint
      fun noPrint(_) = ()
      fun myPrint(s) = if at_least_one_conditional_equation then noPrint(s) else myPrint0(s)
      fun checkDisjointness() = 
              let fun loop([],_) = () 
                    | loop((x as (left_side,is_cond))::remaining_left_sides,left_sides_to_be_examined) =          
                        let val _ = List.map 
                                      (fn (old_left_side,is_old_cond) => if is_old_cond orelse is_cond then () else 
                                         (case AT.unify(old_left_side,left_side) of
                                             SOME(sub) =>  
					       (case pos_option of
                                                SOME(pos) => 
                                                let val _ = error := true
                                                in
                                                myPrint("\n[Warning, "^(A.posToString(pos))^": "^
                                                        "the equational axioms defining "^sym_name^
                                                        " are not disjoint.\nFor example, at least "^
                                                        " two distinct axioms apply to every instance of this term:\n"^
                                                       (AT.toStringDefault(AT.applySub(sub,left_side)))^".]\n")
                                                end
					     | _ =>  let val _ = error := true  
                                                     in
                                                     myPrint("\n[Warning: " ^ 
                                                        "the equational axioms defining "^sym_name^
                                                        " are not disjoint.\nFor example, at least "^
                                                        " two distinct axioms apply to every instance of this term:\n"^
                                                       (AT.toStringDefault(AT.applySub(sub,left_side)))^".]\n")
                                                     end)
                                           | _ => ()))
                                    left_sides_to_be_examined
                        in
                          loop(remaining_left_sides,x::left_sides_to_be_examined)
                        end
              in
                 loop(all_left_sides,[])
              end
      fun checkExaustiveness() = 
             let val (param_sorts,result_sort,is_poly,has_pred_based_sorts) = Data.getSignature(con_name) 
                                                             handle _ => (print("\nCan't find the signature of "^cname);raise Basic.Never)
                 val left_patterns = (List.map (fn (side,is_cond) => makeConTerm side) all_left_sides)
                 val arg_sorts = (case (Data.getSignature f) of
                                    (asorts,_,_,has_pred_based_sorts) => asorts)
                 val uvar = ATV.freshWithSort(FTerm.makeApp(dt_name,arg_sorts))
                 val uvar_sort = ATV.getSort(uvar)
                 val str = if at_least_one_conditional_equation then " should be " else " are " 
             in
               (case StructureAnalysis.exhaustStructure(left_patterns,uvar_sort) of
                   SOME(t) => let val t' = (case AT.isApp(t) of 
                                              SOME(_,args) => AT.makeApp(f,args))
                                  val _ = error := true 
                              in
                                  myPrint("\n[Warning: The current equational axioms for "^sym_name^" are not\nexhaustive. "^
                                          "For example, the value of every ground instance of:\n"^(AT.toStringDefault t')^
                                          "\nis currently unspecified.]\n")
                              end
                  | _ => noPrint("\nDefinition of "^sym_name^" is complete; the given equational axioms"^str^"exhaustive.\n"))
             end
  in
     (checkDisjointness();checkExaustiveness();removeDT(dt);(!error,at_least_one_conditional_equation))
  end    

(**

The following is a very conservative approximation of whether or not 
a set of equations completely and unambiguously define a function symbol f.
If there is even one conditional equation in the given axioms, the 
result will automatically be false, since the problem is undecidable 
in the presence of general conditional equational axioms.

**)

fun isFunDefExhaustive(f,equations) = 
  let val arity = (case Data.isTermConstructor(f) of
                    SOME(i) => i) 
      val (dt_name,con_name,dt) = addTempDT(arity)
      val cname = MS.name(con_name)
      val sym_name = MS.name(f)
      val all_left_sides = List.map (fn eq => getLeftSide(eq,false)) equations 
      fun makeConTerm(left) = AT.makeApp(con_name,AT.getChildren left)
      val at_least_one_conditional_equation = List.exists (fn (_,b) => b = true) all_left_sides
  in
    if at_least_one_conditional_equation then false
    else
    let fun checkExaustiveness() = 
             let val (param_sorts,result_sort,is_poly,has_pred_based_sorts) = Data.getSignature(con_name) 
                                                             handle _ => (print("\nCan't find the signature of "^cname);raise Basic.Never)
                 val left_patterns = (List.map (fn (side,is_cond) => makeConTerm side) all_left_sides)
                 val arg_sorts = (case (Data.getSignature f) of
                                    (asorts,_,_,has_pred_based_sorts) => asorts)
                 val uvar = ATV.freshWithSort(FTerm.makeApp(dt_name,arg_sorts))
                 val uvar_sort = ATV.getSort(uvar)
             in
               (case StructureAnalysis.exhaustStructure(left_patterns,uvar_sort) of
                   SOME(t) => false
                  | _ => true)
             end
          val res = checkExaustiveness()
          val _ = removeDT(dt)
    in
       res
    end
  end

val qualifyName = SV.qualifyName
val qualifySort = SV.qualifySort
val qualifyFSym = SV.qualifyFSym
              
fun addSelectorAxioms({name,...}:ath_structure,mod_path,env,eval_env) = 
                    let val name_str = MS.name(name)
                        val axioms_str = "make-selector-axioms"
                        val quote = "\""
                        val cmd = "(assert* (" ^ axioms_str ^ " " ^ quote ^ name_str ^ quote ^ "))"
                        val process = (!Semantics.processString)
                    in
                       process(cmd,mod_path,env,eval_env)
                    end

fun processStructuresDefinition0(absyn_structure_list: A.absyn_structure list,env,eval_env,mod_path) = 
let val struc_names: symbol list = map #name absyn_structure_list
    val option_valued_selectors_currently = (!(Options.option_valued_selectors_option))
    val positions = map #pos absyn_structure_list
    val (keyword_singular,keyword_plural) = (case hd(absyn_structure_list) of
					       {free=true,...} => ("datatype","datatypes")
					     | _ => ("structure","structures")) 
    val _ = List.app (fn (name:symbol,pos) => 
                            let val str = Symbol.name(name)
                            in 
                              if illegalSortName(str) then
                                 evError("A structure name cannot begin with "^Names.sort_variable_prefix,SOME(pos)) 
                              else A.checkNoDots(str,pos)
                            end)
           (ListPair.zip(struc_names,positions))
    val one_struc_only = case absyn_structure_list of
                            [_] => true | _ => false 
    fun loopReDefs([]) = false
      | loopReDefs(({name,pos,...}:A.absyn_structure)::rest) = 
         let val name' = qualifyName(name,mod_path)
         in
            if checkStrucOrDomainReDefinition(name',pos) then true else loopReDefs(rest)
         end
in
   if loopReDefs(absyn_structure_list) then () else
let  val _ = checkDistinctSNames(struc_names,map #pos absyn_structure_list,
                                 "Duplicate occurence of ","---structure names must be unique")
     val all_constructor_names_and_positions = 
         let  fun get_cons(some_absyn_structure:A.absyn_structure as
                                     {name=struc_name,pos,obtype_params,constructors,free}) = 
                  constructors
              fun get_name(some_absyn_constructor:A.absyn_structure_constructor as
                             {name,pos,...}) = (name,pos);
              fun g([]:A.absyn_structure list,names_and_positions) = names_and_positions
                | g(ab_struc::more,names) = 
                    let val constructors:A.absyn_structure_constructor list = get_cons(ab_struc)
                        val con_names_and_positions = map get_name constructors 
                        in
                           g(more,names@con_names_and_positions)
                    end
              in
                g(absyn_structure_list,[])
         end
    val struc_names_and_arities = List.map (fn (ab_struc) => let val struc_name = #name(ab_struc)
                                                                 val qualified_name = qualifyName(struc_name,mod_path)
                                                             in 
                                                                (qualified_name,length(#obtype_params(ab_struc)))
                                                             end) 
                                           absyn_structure_list
    val new_struc_and_domain_arities = 
          let fun f([],arities) = arities
                | f((struc_name,arity)::more,arities) = 
                     f(more,MS.enter(arities,struc_name,arity))
              in
                f(struc_names_and_arities,!structure_and_domain_arities)
          end
    val _ = structure_and_domain_arities := new_struc_and_domain_arities 
    fun processStructureDefinition(some_absyn_structure:A.absyn_structure as
                                     {name=struc_name,pos,obtype_params,constructors,free=is_free}) = 

       let val _ = let val str = Symbol.name(struc_name) 
                   in
                      if illegalSortName(str) then
                         evError("A structure name cannot begin with "^Names.sort_variable_prefix,SOME(pos))
                      else A.checkNoDots(str,pos)
                   end
           val full_struc_name = qualifyName(struc_name,mod_path)
           val _ = debugPrint("\nProcessing the definition of this structure: "^(MS.name full_struc_name)^"\n")
           val obtype_params_as_symbols = map #name obtype_params
           val obtype_params_as_SymTerms = map SymTerm.makeVar obtype_params_as_symbols
           val range_type_as_SymTerm = SymTerm.makeApp(full_struc_name,obtype_params_as_SymTerms)
	   val range_type_as_AbSynTerm:A.absyn_term = Terms.putBogusTags(range_type_as_SymTerm,A.dum_pos)
	   val con_count = List.length constructors
           fun makeStrucCon({name=con_name,pos,selectors,argument_types}:A.absyn_structure_constructor) = 
               let val con_arity = length(argument_types)
                   val argument_types' =  map qualifySort argument_types
                   val argument_types = argument_types'
                   val is_poly = not(null(obtype_params))
                   val argument_types_as_SymTerms = map SymTerm.stripTags argument_types
                   val types_as_FTerms = 
                         Terms.SymTermsToFTerms(range_type_as_SymTerm::argument_types_as_SymTerms)
                   val argument_types_as_FTerms = tl types_as_FTerms
                   val involves_pred_based_sorts = F.findOutDynamicallyIfAnySortsHavePredicateBasedSortSymbols(argument_types_as_FTerms)
                   val range_type_as_FTerm = hd types_as_FTerms
                   fun decideOption(t) = t
		   fun declareSelectors([],_,_) = ()
    		     | declareSelectors(NONE::rest,_,_) = ()
                     | declareSelectors(SOME({name=sel_name,pos}:A.param)::rest,
					     (ith_arg_type:FTerm.term)::more_arg_types,
					     ith_absynterm_arg_type::more_absynterm_arg_types) = 
			 let val bits_val = makeWord({poly=is_poly,pred_based_sig=false}) 
                             val full_sel_name = qualifyName(sel_name,mod_path)
                             val range_sort = if option_valued_selectors_currently then
                                                 FTerm.makeApp(Names.moption_structure_symbol,[ith_arg_type])
                                              else ith_arg_type
			     val sel_sym:declared_fun_sym = {name=full_sel_name,obtype_params=obtype_params_as_symbols,
					    bits=bits_val,argument_types=[range_type_as_FTerm], arity=1,
					    range_type=range_sort,prec=ref(Options.lowest_fsymbol_precedence),
					    absyn_argument_types=[range_type_as_AbSynTerm],assoc=ref(NONE),
					    absyn_range_type=ith_absynterm_arg_type}
			     val _ = addFSym(declared(sel_sym))
                             val _ = MS.insert(Data.selector_table,full_sel_name,{is_polymorphic=is_poly})
			     val sel_val = Semantics.makeTermConVal(SV.regFSym(Data.declared(sel_sym)))
			 in
			    (Semantics.updateTopValEnv(env,sel_name,sel_val,false);
                             Semantics.updateTopValEnv(eval_env,sel_name,sel_val,false);
			     declareSelectors(rest,more_arg_types,more_absynterm_arg_types))
			 end
		   val _ = declareSelectors(selectors,argument_types_as_FTerms,argument_types)
                   fun getFullSelName(SOME({name=sel_name,pos}:A.param)) = SOME(qualifyName(sel_name,mod_path))
                     | getFullSelName(_) = NONE
                   val full_sel_names = map getFullSelName selectors 
                   val is_reflexive = Basic.exists(argument_types_as_FTerms,
                                                   fn fterm => F.fsymOccursIn(full_struc_name,fterm))
                   fun allSame() = if con_arity = 0 then (true,NONE)
                                   else 
                                     let val t = hd(argument_types_as_FTerms)
                                     in
                                        if FTerm.isGround(t) andalso
                                           (List.all (fn s => FTerm.termEq(s,t))
                                                     (tl argument_types_as_FTerms))  
                                        then (true,SOME(t))
                                        else (false,NONE)
                                     end
                   in 
                      {name=qualifyName(con_name,mod_path),arity=con_arity,mother_structure=qualifyName(struc_name,mod_path),reflexive=is_reflexive,
                       argument_types=argument_types_as_FTerms,range_type=range_type_as_FTerm,prec=ref(Options.defaultPrec(con_arity)),
                       absyn_argument_types=argument_types,bits=makeWord({poly=is_poly,pred_based_sig=involves_pred_based_sorts}),
                       selectors=full_sel_names,assoc=ref(NONE),
                       sym_range_type=range_type_as_SymTerm}
               end 
           fun makeStructureConstructors() = map makeStrucCon constructors    
           val struc_arity = length(obtype_params)
           fun typeCheckConstructor({name,argument_types,...}:A.absyn_structure_constructor) =
               let fun isLegalVariable(sym) = Basic.isMember(sym,obtype_params_as_symbols)
                   fun checkArgTypes([]:A.absyn_term list,_) = () 
                     | checkArgTypes(t::rest,i:int) = 
                               let val t' = qualifySort(t)
                                   val _ = (case SymTerm.isTaggedLegal(t', fn sym => MS.lookUp(new_struc_and_domain_arities,sym),isLegalVariable) of
                                               NONE => ()
                                             | SOME(error_pos) =>  
                                                    evError("Ill-formed sort given for"^" argument position "^Int.toString(i)^
                                                            " of constructor "^Symbol.name(name)^": "^Terms.printSymTermSExp(SymTerm.stripTags(t)),SOME(error_pos)))
                               in
                                  checkArgTypes(rest,i+1)
                               end
                   in
                     checkArgTypes(argument_types,1)
               end
           fun typeCheckConstructors() = map typeCheckConstructor constructors
           val _ = checkStrucOrDomainReDefinition(full_struc_name,pos) 
           val _ = List.app checkStrucConOrFSymRedef
                    (map (fn {name,pos,...}:A.absyn_structure_constructor => (qualifyName(name,mod_path),pos)) constructors)
           val _ = typeCheckConstructors();  
           val new_constructors =  map makeStrucCon constructors 
           val new_struc:ath_structure = {name=full_struc_name,arity=struc_arity,obtype_params=obtype_params_as_symbols,
                                          option_valued_selectors=option_valued_selectors_currently,
                                          constructors=new_constructors,free=is_free}
         in
            new_struc
       end;  (** End of "let fun processStructureDefinition **)
     val (con_names,con_positions) = ListPair.unzip(all_constructor_names_and_positions)
     val full_con_names = map (fn name => qualifyName(name,mod_path)) con_names 
     val _ = checkConNames(all_constructor_names_and_positions)
     val (new_structures,error_msg) = (checkDistinctNames(full_con_names,con_positions,
                                                          "Duplicate occurence of ",
                                                          "---constructor names must be unique");
                                       ((map processStructureDefinition absyn_structure_list),""))
     in 
          let fun makeConstructorValue(acon as {name:mod_symbol,arity:int,range_type,bits:Word8.word,...}:ath_struc_constructor) = 
                    let val constructorFunVal = Semantics.makeTermConValFromStructureConstructor(acon)
                        val last_con_name = MS.lastName(name)
                        val _ = Semantics.updateTopValEnv(eval_env,last_con_name,constructorFunVal,false)
                        val _ = Semantics.updateTopValEnv(env,last_con_name,constructorFunVal,false)
                        val _ = eval_env := forceSetVal(mod_path,last_con_name,constructorFunVal,!eval_env)
                        in
                          ()
                    end


              fun makeStructure(new_struc:ath_structure as {name,constructors,...}) = 
                   (List.app addConstructor constructors;
		    List.app (fn c => D.addFSym(D.struc_con(c))) constructors;
		    List.app makeConstructorValue constructors;
		    Data.addStructure(new_struc))
              fun makeStructures() = (List.app makeStructure new_structures)                                      
              val structure_number = length(absyn_structure_list) 
              val bit_array = Array.array(structure_number,0)
              val _ = if not(areInhabited(new_structures)) then
                     evError("Uninhabited (empty) set of structures defined",
                     SOME(#pos(hd(absyn_structure_list))))
                      else makeStructures()
              fun setSortNames([]) = ()
                | setSortNames((struc_name,arity)::more) = 
                    (Basic.inc(sort_index); 
                     if (!sort_index) > (!domain_max) then expandSubsortMatrix() else ();
                     setSortName(!sort_index,struc_name);
                     MS.insert(sort_table,struc_name,{name=struc_name,arity=arity,index=(!sort_index)});
                     setSortNames(more))
              val _ = setSortNames(struc_names_and_arities)
              fun makeString(name::more) = 
                   (case more of
                       [] => "and "^MS.name(name)
                     | rest as _::_ => MS.name(name)^", "^makeString(rest))
                | makeString(_) = "";
              fun addAxioms({name,free=is_free,...}:ath_structure) = 
                    let val name_str = MS.name(name)
                        val axioms_str = if is_free then "datatype-axioms" else "structure-axioms"
                        val quote = "\""
                        val cmd = "(assert* " ^ (name_str^"-axioms") ^ " := (" ^ axioms_str ^ " " ^ quote ^ name_str ^ quote ^ "))"
                        val process = (!Semantics.processString)
                    in
                       process(cmd,mod_path,env,eval_env)
                    end
              val _ = if (!Options.auto_assert_dt_axioms) then 
                         (List.app addAxioms new_structures)
                      else ()

              val _ = if (!Options.auto_assert_selector_axioms) andalso not(!(Options.first_time)) then 
                         ((List.app (fn (struc) => addSelectorAxioms(struc,mod_path,env,eval_env)) new_structures) handle _ => ())
                      else ()
              in
                 if one_struc_only then
                    myPrint("\nNew "^keyword_singular^" "^(MS.name(qualifyName(hd struc_names,mod_path)))^" defined.\n")
                 else
                    myPrint("\nNew "^keyword_plural^" "^Basic.printLnListStr(map (fn s => qualifyName(s,mod_path)) struc_names,MS.name)^" defined.\n")
          end
end
end 

fun processStructuresDefinition(absyn_structure_list: A.absyn_structure list,env,eval_env,mod_path) = 
  let val starting_structure_and_domain_arities = (!(Data.structure_and_domain_arities))
  in
    ((processStructuresDefinition0(absyn_structure_list: A.absyn_structure list,env,eval_env,mod_path))
        handle ex => (Data.structure_and_domain_arities := starting_structure_and_domain_arities;
                      raise ex))
  end

fun checkSubsortIntegrity(pos) = 
  let val sorts = MS.listItems(sort_table)
      fun checkDatatypes(name1,name2) = 
             if isStructure(name1) andalso isStructure(name2) andalso areSubsorts(name1,name2) 
                andalso not(MS.modSymEq(name1,name2)) then 
             evError("These datatypes have been made subsorts: "^(MS.name(name1))^" and "^(MS.name(name2)),SOME(pos))
             else ()
      fun checkPredefined(name1,name2) = 
             if not(MS.modSymEq(name1,name2)) andalso misPredefinedSort(name1) andalso misPredefinedSort(name2) andalso 
                not(mintendedPredefinedSubsorts(name1,name2) orelse mintendedPredefinedSubsorts(name2,name1)) 
                andalso (areSubsorts(name1,name2) orelse areSubsorts(name2,name1)) then
             evError("These predefined sorts have been made subsorts: "^(MS.name(name1))^" and "^(MS.name(name2)),SOME(pos))
             else ()
      fun check({name=name1,index=index1,...}:SortOrder.ath_domain) = 
      	  List.app (fn {name=name2,index=index2,...}:SortOrder.ath_domain => (checkDatatypes(name1,name2);checkPredefined(name1,name2)))
                   sorts
  in 
     List.app check sorts
  end

fun processSubSortDeclaration(name1,pos1,name2,pos2,str) = 
 if MS.modSymEq(name1,name2) then
    myPrint("\nThis holds by default.\n")
 else
 if (Data.isStructure(name1) andalso Data.isStructure(name2)) then
    evError("A datatype cannot be made a subsort of another datatype",SOME(pos1))
 else if (Data.misPredefinedSort(name1) andalso Data.misPredefinedSort(name2) andalso (not(MS.modSymEq(name1,mint_sort_symbol))
          orelse not(MS.modSymEq(name2,mreal_sort_symbol))))
      then
          evError("These predefined sorts cannot be made subsorts of each other",SOME(pos1))
 else 
    (case MS.find(sort_table,name1) of  
	SOME(dom as {name=dname1,arity=arity1,index=index1,...}) => 
	    (case MS.find(sort_table,name2) of  
		SOME(dom as {name=dname2,arity=arity2,index=index2,...}) => 
		  if not(arity1 = arity2) then
                     evError("Polymorphic domains of different arities cannot be made subsorts",SOME(pos2))
		  else 
		   (Array.update(!order_sorted_array,index1,true);
		    Array.update(!order_sorted_array,index2,true);
		    setSortMatrix(!global_sort_matrix,index1,index2,(dname1,dname2,true));
		    warshallTransitiveClosure(!global_sort_matrix); 
		    checkGlobalSortMatrix(pos1);
                    checkSubsortIntegrity(pos1);
	 	    if str = "" then () else myPrint("\nOK.\n"))
              | _ => evError("Invalid sort name: "^(MS.name name2),SOME(pos2)))
      | _ => evError("Invalid sort name: "^MS.name(name1),SOME(pos1)))

fun processSubSortsDeclaration(domains_and_positions,dom,pos) =  
    (List.app (fn (d,d_pos) => processSubSortDeclaration(d,d_pos,dom,pos,"")) domains_and_positions;
     myPrint("\nOK.\n"))
	handle Semantics.EvalError(msg,_) => myPrint(msg)

fun processDomainDeclaration(d as {name,arity,pos,sort_predicate,...}:A.absyn_domain,mod_path) = 
      let val full_name = qualifyName(name,mod_path)
          val _ = let val str = Symbol.name(name)
                  in
                     if illegalSortName(str) then
                        evError("A domain name cannot begin with "^Names.sort_variable_prefix,SOME(pos))
                     else A.checkNoDots(str,pos)
                  end
          val already = ref(false)
          val _ = if MS.exists(sort_table,full_name) then 
                     (already := true;
                      Semantics.warning("The domain "^(MS.name(full_name))^" has already been introduced",pos))
                  else
                     if MS.exists(structure_table,full_name) then
                        evError("Redefinition---the name "^(MS.name(full_name))^
                                " already refers to a structure",SOME(pos))
                     else ()
          val _ = structure_and_domain_arities := MS.enter(!structure_and_domain_arities,full_name,arity)
	  val dom_name = MS.name(full_name)
          val _ =  if !already then () else
                      (Basic.inc(sort_index); 
     	               if (!sort_index) > (!domain_max) then expandSubsortMatrix() else ();
 	               setSortName(!sort_index,full_name);
 	               MS.insert(sort_table,full_name,{name=full_name,arity=arity,index=(!sort_index)}))
                       
          in 
             (case sort_predicate of
                 NONE => myPrint("\nNew domain "^dom_name^" introduced.\n")
               | SOME(fsym) => 
                   let val fsym_name = MS.name(fsym)
                   in
                     (case MS.find(Data.fsym_table,fsym) of 
                         SOME(defined({argument_types,range_type,bits,...})) =>  
                          if length(argument_types) = 1 andalso FTerm.sortEq(range_type,FTerm.boolean_sort) then
                             let val def_name = fsym_name^"-definition"
                                 val def_name = Names.getSafeName(def_name)
                                 val def_val = ((!Semantics.evaluateStringFlexible) (def_name,top_val_env))
                                 val def_prop = (case def_val of
                                                    Semantics.propVal(p) => p)
                                 val (vars,body) = (case Prop.splitVars(def_prop) of
                                                       (SOME(A.forallCon),vars,body) => (vars,body))
                                 val body = (case Prop.isBiCond(body) of
                                                SOME(left,right) => right 
                                              | _ => (case Prop.isEquality(body) of               
                                                         SOME(t1,t2) => Prop.makeAtom(t2)))
                                 fun makeBody(terms) = Prop.replaceLst(vars,terms,body)
                                 val (super_sort_root,super_sort,arity) = 
                                         let val ss = hd(argument_types)
                                         in
                                            (case FTerm.isApp(ss) of
                                                SOME(root,args) => (root,ss,length(args))
                                              | _ => evError("The domain of a sort predicate cannot be a sort variable",SOME(pos)))
                                         end
                                 val _ = HashTable.insert Prop.sort_predicate_table (full_name,(super_sort_root,makeBody))
                                 val _ = FTerm.addSortWithPredicate(full_name,arity)
                             in
                                (processSubSortDeclaration(full_name,pos,super_sort_root,pos,"");
                                 print("\nNew domain "^(MS.name(full_name))^" introduced, as a subsort of "^(MS.name(super_sort_root))^".\n"))
                             end
                        else evError("Wrong kind of sort predicate "^fsym_name,SOME(pos))
                      | _ => evError("There is no sort predicate "^fsym_name,SOME(pos)))
                   end)
      end  
 
fun processDomainsDeclaration(dd_lst,mod_path) = List.app (fn d => processDomainDeclaration(d,mod_path)) dd_lst

fun evalPhrase((p,fids),env,ab) = 
   let 
       val env'' = env
       val _ = if (false andalso !Options.fundef_mlstyle_option) then print("\nINSIDE evalPhrase, given env:\n" ^ SV.envToString(!env) ^ "\n") else ()
       val env' = Semantics.makeEnv(fids,!env)

       val _ = if (false andalso !Options.fundef_mlstyle_option) then print("\nAnd transformed env':\n" ^ SV.envToString(!env') ^ "\n") else ()
       val v = Semantics.evalPhrase(p,env',ab)
   in
      v
   end

fun evalExp((e,fids),env,ab) = let val env'' = env
                                        val env' = Semantics.makeEnv(fids,!env) 
                                        val v = Semantics.evalExp(e,env',ab)
                                    in
					v
                                    end

fun printVal(Semantics.propVal(p),(true,_)) = 
      myPrint("\nTheorem: "^pprint(9,p)^"\n")  
  | printVal(v,_) = Semantics.printVal(v)

fun addProp(v as Semantics.propVal(p),env,eval_env,(is_ded,name_opt),mod_path,definition_sym_opt) = 
         if is_ded then
            (top_assum_base := ABase.augment(!top_assum_base,[p]);  	     
             (case (name_opt,definition_sym_opt) of 
                 (SOME(name),_) => (Semantics.updateTopValEnv(env,name,v,true);Semantics.updateTopValEnv(eval_env,name,v,true);P.addToModuleAb(mod_path,p,SOME(S.name(name))))
               | (_,SOME(name)) => (Semantics.updateTopValEnv(env,name,v,true);Semantics.updateTopValEnv(eval_env,name,v,true);P.addToModuleAb(mod_path,p,SOME(S.name(name))))
               | _ => P.addToModuleAb(mod_path,p,NONE)))
         else ()
  | addProp(_) = ()

fun processAssocDeclaration(((msym,pos),b)) = 
  let fun setAssoc(arity,assoc,b,pos) = 
             if arity = 2 then 
                assoc := SOME(b)
             else evError("Associativity can be specified only for binary procedures and function symbols",SOME(pos))
  in
     (case Semantics.evalPhrase(A.exp(A.idExp({msym=msym,mods=MS.modules(msym),sym=MS.lastName(msym),no_mods=null(MS.modules(msym)),pos=pos})),top_val_env,!top_assum_base) of
        v as Semantics.closFunVal(A.functionExp({params,...}),_,{prec,assoc,...}) =>  
             let val arity = length params
             in 
               setAssoc(arity,assoc,b,pos)
             end
      | v as Semantics.termConVal(Semantics.regFSym(some_fsym)) => setAssoc(Data.fsymArity(some_fsym),Data.fsymAssoc(some_fsym),b,pos)
      | v as Semantics.funVal(_,_,{arity,assoc,...}) => setAssoc(arity,assoc,b,pos)
      | v as Semantics.propConVal(A.notCon) => A.set_PC_Assoc(A.notCon,b)
      | v as Semantics.propConVal(A.andCon) => A.set_PC_Assoc(A.andCon,b)
      | v as Semantics.propConVal(A.orCon) => A.set_PC_Assoc(A.orCon,b)
      | v as Semantics.propConVal(A.ifCon) => A.set_PC_Assoc(A.ifCon,b)
      | v as Semantics.propConVal(A.iffCon) => A.set_PC_Assoc(A.iffCon,b)
      | _ => evError("Only binary procedures, function symbols, and sentential\n"^
                     "connectives can have their associativity specified",SOME(pos)))
  end

fun processAssocDeclarations(msyms_and_positions,b) = 
       (List.app (fn (p as (msym,pos)) => processAssocDeclaration((p,b))) msyms_and_positions;ok())

fun fromTo(i,j) = let val (ai,aj) = (SemanticValues.termVal(AT.makeNumTerm(A.int_num(i,ref ""))),
                                     SemanticValues.termVal(AT.makeNumTerm(A.int_num(j,ref ""))))
                  in 
                     if Semantics.valEq(ai,aj) then [] 
                     else let val _ = AT.makeNumTerm(A.int_num(i+1,ref ""))
                          in ai::(fromTo(i+1,j))
                          end
                   end

val infixProcess = TopEnv.infixProcess

fun printToCR(str) = 
   let val stream = TextIO.openAppend("compilationResults.txt")
   in  
     TextIO.output(stream,str);
     TextIO.closeOut(stream)
   end

fun compilePhrase(p) = printToCR(AthenaCompiler.unparse(AthenaCompiler.compilePhrase(p)))

fun printKind(p) = 
                         (case p of 
                              A.exp(A.BAppExp(_)) => print("\nAbout to evaluate a binary application...\n")
                            | A.exp(A.appExp(_)) => print("\nAbout to evaluate a regular application...\n")
                            | _ => ())

fun addDependencyInfo(v,premises) = 
  let val premises = PropSet.list(premises)
      val ht : (Prop.prop,bool) HashTable.hash_table = HashTable.mkTable(Prop.hash,Prop.alEq) (30,Basic.Fail("Hashing Exception"))
      val premises' = Prop.dedup(premises)
  in
    (case v of
         SV.propVal(p) => PropSet.enterDependency(p,premises')
       | _ => Basic.fail("\nDeduction resulted in a non-sentential value, might need conversion!\n"))
  end

fun processPhrase(p:A.phrase,env,eval_env,fids,mod_path) = 
              let val ip = infixProcess(p,eval_env,fids)
                  val fids = MS.add(Names.mite_symbol,fids)
                  val fids = MS.add(Names.mconcatFun_symbol,fids);
                  val _ = if (!Options.compilation_on) then compilePhrase(ip) else ()
                  val is_ded = A.isNamedDeduction(p)		  
                  val p_pos = A.posOfPhrase(p)
                  val v = if  !Options.expand_proof then
                               (print("\nThe expanding interpreter is not currently implemented.\n");SV.unitVal)
                          else
                             (let val v = (if (!Options.proof_tracking_option) then
				               (case ip of
                                                  A.exp(_) => evalPhrase((ip,fids),eval_env,!top_assum_base)
                                                | A.ded(d) => let val (th_val,premises:PropSet.prop_set) = Semantics.evalDedWT(d,eval_env,!top_assum_base)
								  val prems = PropSet.list(premises)
								  val _ = addDependencyInfo(th_val,premises)
                                                              in
                                                                 th_val
                                                              end)
                                          else
					       evalPhrase((ip,fids),eval_env,!top_assum_base))                             
 			      in
                                Semantics.updateLastValueAndReturn(v)
			      end)
                  val answer = addProp(v,env,eval_env,is_ded,mod_path,NONE)
              in 
                 (printVal(v,is_ded); answer)
              end

fun processPhraseAndReturn(p,env,eval_env,fids,mod_path) = 
              let val ip = infixProcess(p,eval_env,fids)
                  val fids = MS.add(Names.mite_symbol,fids)
                  val v = if !Options.expand_proof then 
                               (print("\nThe expanding interpreter is not currently implemented.\n");SV.unitVal)
                          else
                             (if (!Options.proof_tracking_option) then
				               (case ip of
                                                  A.exp(_) => evalPhrase((ip,fids),eval_env,!top_assum_base)
                                                | A.ded(d) => let val (th_val,premises) = Semantics.evalDedWT(d,eval_env,!top_assum_base)
								  val _ = addDependencyInfo(th_val,premises)
                                                              in
                                                                 th_val
                                                              end)
                                          else
					       evalPhrase((ip,fids),eval_env,!top_assum_base))
                  val is_ded = A.isNamedDeduction(p)
              in
                (addProp(v,env,eval_env,is_ded,mod_path,NONE);v)
              end

fun processPhraseAndReturnInEnv(p,fids,env,eval_env,mod_path,definition_sym_opt) = 
              let val ip = infixProcess(p,eval_env,fids)
                  val fids = MS.add(Names.mite_symbol,fids)
                  val v =  (if (!Options.proof_tracking_option) then
				               (case ip of
                                                  A.exp(_) => evalPhrase((ip,fids),eval_env,!top_assum_base)
                                                | A.ded(d) => let val (th_val,premises) = Semantics.evalDedWT(d,eval_env,!top_assum_base)
								  val _ = addDependencyInfo(th_val,premises)
                                                              in
                                                                 th_val
                                                              end)
                                          else
					       evalPhrase((ip,fids),eval_env,!top_assum_base))

                  val is_ded = A.isNamedDeduction(p)
              in
                (addProp(v,env,eval_env,is_ded,mod_path,definition_sym_opt);v)
              end

fun processPhraseAndReturnInEnvWithoutAdding(p,fids,eval_env,mod_path) = 
              let val ip = infixProcess(p,eval_env,fids)
                  val fids = MS.add(Names.mite_symbol,fids)
                  val v =  (if (!Options.proof_tracking_option) then
				               (case ip of
                                                  A.exp(_) => evalPhrase((ip,fids),eval_env,!top_assum_base)
                                                | A.ded(d) => let val (th_val,premises) = Semantics.evalDedWT(d,eval_env,!top_assum_base)
								  val _ = addDependencyInfo(th_val,premises)
                                                              in
                                                                 th_val
                                                              end)
                                          else
					       evalPhrase((ip,fids),eval_env,!top_assum_base))
              in
                v
              end

fun evalStringFlexible(str,eval_env) = 
  let val stream = TextIO.openString (str)
      val input  = hd(Parse.parse_from_stream(stream))
      val res_val = (case input of
                       A.phraseInput(p) => let val mod_path = (case (!Paths.open_mod_paths) of
                                                                  [] => []
                                                                | mp::_ => mp)
                                               val (new_phrase,vars,fids) = SV.preProcessPhrase(p,mod_path)
                                           in 
                                              processPhraseAndReturnInEnvWithoutAdding(new_phrase,fids,eval_env,mod_path)
                                           end
                     | _ => evError("Incorrect application of evalStringFlexible. Only phrases can be evaluated.",NONE))
   in
     res_val
   end

val _ = Semantics.evaluateStringFlexible := evalStringFlexible

fun doPhrase(p,env,ab,fids) = 
            let val ip = infixProcess(p,env,fids)
                val fids = MS.add(Names.mite_symbol,fids)
            in
               evalPhrase((ip,fids),env,ab)
            end

fun processInputExpansion(phrase1,(phrase2,v2),env,eval_env,pos,fids,mod_path) = 
   (case processPhraseAndReturnInEnv(phrase1,fids,env,eval_env,mod_path,NONE) of 
      v1 => let val pos_ar = Array.array(3,A.dum_pos)
                val _ = (Array.update(pos_ar,0,pos);Array.update(pos_ar,1,A.posOfPhrase(phrase1));Array.update(pos_ar,2,A.posOfPhrase(phrase2)))
                val (name:MS.mod_symbol,fun_val) =  
                     TopEnv.expandInputFun([v1,v2],(eval_env,!top_assum_base),{pos_ar=pos_ar,file=""})
                val (symbol_mod_path,symbol_name) = MS.split(name)
                val _ = debugPrint("\nUpdating both environments on this symbol: "^(MS.name name)^"\n")
                val _ = debugPrint("\nGiven mod_path: "^(Basic.printListStr(mod_path,Symbol.name," ")))
                val _ = debugPrint("\nSymbol mod_path: "^(Basic.printListStr(symbol_mod_path,Symbol.name," ")))
                val _ = if Basic.listEq(mod_path,symbol_mod_path,Symbol.symEq) then 
                           (Semantics.updateTopValEnv(env,symbol_name,fun_val,false);
                            Semantics.updateTopValEnv(eval_env,symbol_name,fun_val,false))
                        else (env := setVal(symbol_mod_path,symbol_name,fun_val,!env);
                              eval_env := setVal(symbol_mod_path,symbol_name,fun_val,!eval_env))
            in
               ()
            end)

fun processInputExpansionLst(phrases,phrase,env,eval_env,pos,fids,mod_path) = 
      let val v = processPhraseAndReturnInEnv(phrase,fids,env,eval_env,mod_path,NONE)
      in
         List.app (fn p => processInputExpansion(p,(phrase,v),env,eval_env,pos,fids,mod_path)) phrases
      end

fun processOutputTransformation(phrase1,phrase2,env,eval_env,{first_arg_pos,second_arg_pos,overall_pos},fids,mod_path) = 
   (case (processPhraseAndReturnInEnv(phrase1,fids,env,eval_env,mod_path,NONE),processPhraseAndReturnInEnv(phrase2,fids,env,eval_env,mod_path,NONE)) of 
      (v1,v2) => let val pos_ar = Array.array(3,A.dum_pos)
                     val _ = (Array.update(pos_ar,0,overall_pos);Array.update(pos_ar,1,first_arg_pos);Array.update(pos_ar,2,second_arg_pos))
                     val (name,fun_val) =  
                        TopEnv.transformOutputFun([v1,v2],(eval_env,!top_assum_base),{pos_ar=pos_ar,file=""})
                     val (symbol_mod_path,symbol_name) = MS.split(name)
                     val _ = if Basic.listEq(mod_path,symbol_mod_path,Symbol.symEq) then 
                                (Semantics.updateTopValEnv(env,symbol_name,fun_val,false);
                                 Semantics.updateTopValEnv(eval_env,symbol_name,fun_val,false))
                             else (env := setVal(symbol_mod_path,symbol_name,fun_val,!env);
                                   eval_env := setVal(symbol_mod_path,symbol_name,fun_val,!eval_env))
                 in 
                    ()
                 end)

fun doOverload(phrase1,phrase2,env,eval_env,pos0,pos1,pos2,pos3,fids,mod_path,file,inv as {inverted}) = 
     let val pos_ar = Array.array(4,A.dum_pos)
         val _ = (Array.update(pos_ar,0,pos0);Array.update(pos_ar,1,pos1);Array.update(pos_ar,2,pos2);Array.update(pos_ar,3,pos3))
     in
       (case (processPhraseAndReturnInEnv(phrase1,fids,env,eval_env,mod_path,NONE),processPhraseAndReturnInEnv(phrase2,fids,env,eval_env,mod_path,NONE)) of 
          (v1,v2) => 
                     let val (new_name,mod_name) = (case phrase1 of 
                                                      A.exp(A.idExp({msym,...})) => (MS.name(msym),msym)
                                                         | _ => ("",MS.dum_modsym("")))
                         val (new_name_sym,fun_val) =  
                               TopEnv.overloadFun([v1,v2],(eval_env,!top_assum_base),{pos_ar=pos_ar,file=file},new_name,inverted)
                         val new_name_sym' = if new_name = "" then new_name_sym else mod_name
                         val (symbol_mod_path,symbol_name) = MS.split(new_name_sym')
                         val _ = if Basic.listEq(mod_path,symbol_mod_path,Symbol.symEq) then 
                                    (Semantics.updateTopValEnv(env,symbol_name,fun_val,false);
                                     Semantics.updateTopValEnv(eval_env,symbol_name,fun_val,false))
                                 else (env := setVal(symbol_mod_path,symbol_name,fun_val,!env);
                                      eval_env := setVal(symbol_mod_path,symbol_name,fun_val,!eval_env))
                     in
                        ()
                     end)
     end

fun processOverload(phrase1,phrase2,env,eval_env,pos0,pos1,pos2,pos3,fids,mod_path,file,inv as {inverted}) = 
      (doOverload(phrase1,phrase2,env,eval_env,pos0,pos1,pos2,pos3,fids,mod_path,file,inv))

fun processPrecedenceDeclaration((mname,pos):(mod_symbol * A.pos),prec_exp,env,eval_env,fids) = 
  let val msg1 = "Only non-negative integer values are allowed as arguments to this command"
      val msg2 = "Precedence values should generally not be\nless than 100. This can interfere "^
                 "with the proper parsing of sentences"
      val ip = infixProcess(A.exp prec_exp,eval_env,fids)
      val fids = MS.add(Names.mite_symbol,fids)
      fun setPrec(arity,prec,prec_exp,pos) = 
             if arity = 2 orelse arity = 1 then 
                (case evalPhrase((ip,fids),eval_env,!top_assum_base) of
                   Semantics.termVal(t) => (case AthTerm.getNumVal(t) of 
                                              SOME(A.int_num(i,_),_) => if Int.>=(i,0) then 
                                                                           (prec := i; 
									    if Int.<(i,100) then 
                                                                               evWarning(msg2,SOME(pos))
                                                                            else ())
                                                                        else evError(msg1,SOME(pos))
                                            | _ => evError(msg1,SOME(pos)))
                  | _ => evError("Invalid precedence value; a non-negative integer was expected here",SOME(pos)))
             else evError("Precedence values can be set only for unary and binary procedures and function symbols",SOME(pos))
      val (mods,s) = MS.split(mname) 
  in
     (case Semantics.evalPhrase(A.exp(A.idExp({msym=mname,mods=mods,sym=s,no_mods=null(mods),pos=pos})),eval_env,!top_assum_base) of
        v as Semantics.closFunVal(A.functionExp({params,...}),_,{prec,assoc,...}) =>  
             let val arity = length params
             in 
               setPrec(arity,prec,prec_exp,pos)
             end
      | v as Semantics.closBFunVal(_,_,_,_,{prec,assoc,...}) => setPrec(2,prec,prec_exp,pos)
      | v as Semantics.closUFunVal(_,_,_,{prec,...}) => setPrec(1,prec,prec_exp,pos)
      | v as Semantics.termConVal(Semantics.regFSym(some_fsym)) => setPrec(D.fsymArity(some_fsym),D.fsymPrec(some_fsym),prec_exp,pos)
      | v as Semantics.funVal(_,_,{arity,prec,...}) => setPrec(arity,prec,prec_exp,pos)

      | v as Semantics.primUFunVal(_,{prec,...}) => setPrec(1,prec,prec_exp,pos)
      | v as Semantics.primBFunVal(_,{prec,...}) => setPrec(1,prec,prec_exp,pos)

      | v as Semantics.propConVal(A.notCon) => setPrec(1,#prec(A.not_con_passoc),prec_exp,pos)
      | v as Semantics.propConVal(A.andCon) => setPrec(2,#prec(A.and_con_passoc),prec_exp,pos)
      | v as Semantics.propConVal(A.orCon) => setPrec(2,#prec(A.or_con_passoc),prec_exp,pos)
      | v as Semantics.propConVal(A.ifCon) => setPrec(2,#prec(A.if_con_passoc),prec_exp,pos)
      | v as Semantics.propConVal(A.iffCon) => setPrec(2,#prec(A.iff_con_passoc),prec_exp,pos)
      | _ => evError("Only binary procedures, function symbols, and sentential\n"^
                     "connectives can have their precedence values set",SOME(pos)))
  end

fun boundMSym(msym,e) =
    let val (mod_names,sym_name) = MS.split(msym)
    in
       (case Semantics.lookUp(e,mod_names,sym_name) of
           SOME(_) => true
         | _ => false)
    end

fun processPrecedenceDeclarations(mod_syms_and_positions,prec_exp,env,eval_env,fids) = 
       (List.app (fn mod_sym_and_pos => processPrecedenceDeclaration(mod_sym_and_pos,prec_exp,env,eval_env,fids)) mod_syms_and_positions)


fun processFSymDeclaration(afs:A.absyn_fsym as {name=fsym_name,pos,obtype_params,input_transformer,
                                                argument_types=absyn_arg_types,prec,assoc,overload_sym,
                                                range_type=absyn_ran_type,...},mod_path,env,eval_env) = 
let val full_fsym_name = MS.makeModSymbol(mod_path,fsym_name,Symbol.symbol(Basic.printListStr(mod_path@[fsym_name],Symbol.name,".")))
in
    if checkFSymRedef(full_fsym_name,pos) then () else
    let val _ = checkNewFunSym(fsym_name,pos)
        val obtype_params_as_symbols = map #name obtype_params
        val arity = length absyn_arg_types  
        val absyn_arg_types' = map (fn absyn_type => qualifySort(absyn_type)) absyn_arg_types
        val absyn_arg_types = absyn_arg_types' 
        val absyn_ran_type' = qualifySort(absyn_ran_type)
        val absyn_ran_type = absyn_ran_type' 
        fun checkArgAndRangeTypes() = 
            let fun isLegalVar(sym) = Basic.isMember(sym,obtype_params_as_symbols)
		fun isLegalFSym(sym) =  (case MS.lookUp(!structure_and_domain_arities,sym) of
                                            NONE => MS.lookUp(!structure_and_domain_arities,qualifyName(MS.lastName(sym),mod_path))
                                          | res => res)
                fun checkArgSorts([]:A.absyn_term list,arg_sort_vars) = arg_sort_vars
                  | checkArgSorts(sort::rest,arg_sort_vars) = 
                      (case SymTerm.isTaggedLegalFlex(sort,isLegalFSym,isLegalVar,Names.fun_name_msym) of
                           NONE => let val new_vars = SymTerm.getVars(SymTerm.stripTags(sort))
				   in
				      checkArgSorts(rest,new_vars@arg_sort_vars)
				   end
                         | SOME(p) => let val sort' = SymTerm.stripTags(sort)
				      in
                                         evError("Ill-formed sort: "^(Terms.printSymTermSExp(sort')),SOME(p)) 
				      end)
		val arg_vars = checkArgSorts(absyn_arg_types,[])
		val flag: SymTerm.variable option ref = ref(NONE)
		fun isLegalVar'(sym) = if arity > 0 then (if Basic.isMember(sym,arg_vars) then true
							  else (flag := SOME(sym);false))
				       else isLegalVar(sym)
            in
                   (case SymTerm.isTaggedLegalFlex(absyn_ran_type,isLegalFSym,isLegalVar',Names.fun_name_msym) of
		       NONE => ()
		     | SOME(p) => (case !flag of
				     SOME(v) => evError("The sort variable "^(Symbol.name(v))^" appears in the "^
							"resulting sort\n"^ 
							"but not in any argument sort",SOME(p))
				   | _ => let val sort' = SymTerm.stripTags(absyn_ran_type)
					  in
					     evError("Ill-formed sort: "^(Terms.printSymTermSExp(sort')),
						     SOME(p))
					  end))
           end
      in                    
          (checkArgAndRangeTypes();
           let val arg_types_as_SymTerms = map SymTerm.stripTags absyn_arg_types
               val range_type_as_SymTerm = SymTerm.stripTags absyn_ran_type
               val types_as_FTerms = 
                     Terms.SymTermsToFTerms(range_type_as_SymTerm::arg_types_as_SymTerms)
               val argument_types_as_FTerms = tl types_as_FTerms
      	       val range_type_as_FTerm = hd types_as_FTerms
               fun allSame() = if null(argument_types_as_FTerms) then (true,NONE)
                               else 
                                  let val t = hd(argument_types_as_FTerms)
                                  in
                                      if FTerm.isGround(t) andalso
                                         (List.all (fn s => FTerm.termEq(s,t))
                                                   (tl argument_types_as_FTerms)) then (true,SOME(t))
                                      else (false,NONE)
                                  end
               val all_sorts = range_type_as_FTerm::argument_types_as_FTerms
               val is_poly = List.exists (fn t => not(FTerm.isGround(t)))
                                         all_sorts
               val involves_pred_based_sorts = F.findOutDynamicallyIfAnySortsHavePredicateBasedSortSymbols(all_sorts)
               val prec_val = if arity = 2 andalso FTerm.termEq(range_type_as_FTerm,FTerm.boolean_sort) then
                              Options.standard_bool_symbol_precedence else Options.defaultPrec(arity)
               val new_fsym = {name=full_fsym_name,
	                       obtype_params=obtype_params_as_symbols,
			       bits=makeWord({poly=is_poly,pred_based_sig=involves_pred_based_sorts}),
                               argument_types=argument_types_as_FTerms,
			       range_type=range_type_as_FTerm, 
                               absyn_argument_types=absyn_arg_types,
			       absyn_range_type=absyn_ran_type,
                               prec=ref(prec_val),
			       assoc=ref(NONE),arity=arity}
               fun setPrec({prec=prec_cell,...}:declared_fun_sym,SOME(i)) = (prec_cell := i)
                 | setPrec({prec=prec_cell,...},NONE) = 
                    (case overload_sym of 
                      SOME(p:A.param as {name,pos=ol_symbol_pos,...}) => 
                       let val name' = A.makeMS(A.makeModString(mod_path,name),NONE)
                       in
                        if boundMSym(name',!eval_env) then
                         (case Semantics.evalPhrase(A.exp(A.idExp({msym=name',mods=mod_path,
			                                           sym=name,no_mods=null(mod_path),pos=pos})),
						   	    	   eval_env,!top_assum_base) of 
                            v => (case Semantics.coerceValIntoTermCon(v) of
                                     SOME(SV.regFSym(new_fsym)) => (prec_cell := !(Data.fsymPrec(new_fsym)))
                                   | _ => (case v of
                                              SV.funVal(f,new_name,{arity,prec=old_prec,assoc,...}) => (prec_cell := !old_prec)
                                           | _ => ())))
                        else ()
                       end
                    | _ => ())
               fun setAssoc({assoc=assoc_ref,...}:declared_fun_sym,SOME(b)) = (assoc_ref := assoc)
                 | setAssoc({assoc=assoc_ref,...},NONE) = 
                                               (case overload_sym of 
                                                  SOME(p:A.param as {name,pos=ol_symbol_pos,...}) => 
                                                   let val name' = A.makeMS(A.makeModString(mod_path,name),NONE)
                                                   in
                                                  if boundMSym(name',!eval_env) then
                                                     (case Semantics.evalPhrase(A.exp(A.idExp({msym=name',mods=mod_path,sym=name,
                                                                                               no_mods=null(mod_path),pos=pos})),eval_env,!top_assum_base) of
                                                       v => (case Semantics.coerceValIntoTermCon(v) of
                                                                SOME(SV.regFSym(new_fsym)) => (assoc_ref := !(Data.fsymAssoc(new_fsym)))
                                                              | _ => (case v of
                                                                         SV.funVal(f,new_name,{assoc,...}) => (assoc_ref := !assoc)
                                                                       | _ => ())))
                                                  else ()
                                                    end
                                                | _ => ())
               val _ = (setPrec(new_fsym,prec);setAssoc(new_fsym,assoc))
               val _ = addFSym(declared(new_fsym));
               val fsymTermConstructorVal = Semantics.makeTermConVal(SV.regFSym(Data.declared(new_fsym)))
               val _ = (Semantics.updateTopValEnv(env,fsym_name,fsymTermConstructorVal,false);
                        Semantics.updateTopValEnv(eval_env,fsym_name,fsymTermConstructorVal,false))
               val _ = eval_env := forceSetVal(mod_path,fsym_name,fsymTermConstructorVal,!eval_env)
	       val funval_after_expansion = ref(NONE)
               fun processInputExpansion() = 
                  (case input_transformer of
                     SOME(exp_list) =>
                      let val converter_values = 
                               let fun f(e) = let val (e',vars,fids) = SV.preProcessExp(e,mod_path)
                                                  val ip = infixProcess(A.exp e',eval_env,fids)
                                              in
                                                 evalPhrase((ip,fids),eval_env,!top_assum_base)
                                              end
                               in 
                                 List.map f exp_list 
                               end  
                          val pos_ar = Array.array(3,A.dum_pos)
                          val pos = A.posOfExp(hd exp_list)
                          val _ = (Array.update(pos_ar,0,pos);Array.update(pos_ar,1,pos);Array.update(pos_ar,2,pos))
                          val (name,fun_val) = TopEnv.expandInputFun([fsymTermConstructorVal,
			                                              SemanticValues.listVal(converter_values)],
                                                                      (eval_env,!top_assum_base),
								      {pos_ar=pos_ar,file=""})


                          val (symbol_mod_path,symbol_name) = MS.split(name)
                          val _ = funval_after_expansion := SOME(fun_val)
                val _ = if Basic.listEq(mod_path,symbol_mod_path,Symbol.symEq) then 
                            
                           (Semantics.updateTopValEnv(env,symbol_name,fun_val,false);
                            Semantics.updateTopValEnv(eval_env,symbol_name,fun_val,false))
                        else (env := setVal(symbol_mod_path,symbol_name,fun_val,!env);
                              eval_env := setVal(symbol_mod_path,symbol_name,fun_val,!eval_env))
                      in
                        ()
                      end
                  | NONE => ())
               fun processOverload(SOME(p:A.param as {name,pos=ol_symbol_pos,...})) = 
                    let val name' = A.makeMS(A.makeModString(mod_path,name),NONE)
                        fun lookUpSym(name,SemanticValues.valEnv({val_map,...})) = Symbol.lookUp(val_map,name)
                    in
                       (case lookUpSym(name,!eval_env) of
                        SOME v => let val pos_ar = Array.array(4,A.dum_pos)
                                   val _ = (Array.update(pos_ar,0,pos);
				            Array.update(pos_ar,1,pos);
					    Array.update(pos_ar,2,ol_symbol_pos);
					    Array.update(pos_ar,3,pos))
                                   val v' = (case lookUpSym(fsym_name,!eval_env) of
                                                SOME(value) => value)
                                   val (new_name_sym,fun_val) = 
				           TopEnv.overloadFun([v,v'],
                                                              (eval_env,!top_assum_base),
							      {pos_ar=pos_ar,file=""},
							      Symbol.name(name),false)

                               val new_name_sym' = new_name_sym
                               val (symbol_mod_path,symbol_name) = MS.split(new_name_sym')
                               val _ = if  Basic.listEq(mod_path,symbol_mod_path,Symbol.symEq) then 
                                          (Semantics.updateTopValEnv(env,symbol_name,fun_val,false);
                                           Semantics.updateTopValEnv(eval_env,symbol_name,fun_val,false))
                                       else (env := setVal(symbol_mod_path,symbol_name,fun_val,!env);
                                             eval_env := setVal(symbol_mod_path,symbol_name,fun_val,!eval_env))
                               in
                                  ()
                               end
                     | _ => 
                       (case funval_after_expansion of
                           ref(NONE) => 
                             (Semantics.updateTopValEnv(env,name,fsymTermConstructorVal,false);
                              Semantics.updateTopValEnv(eval_env,name,fsymTermConstructorVal,false))
                         | ref(SOME(fval)) => 
                            (Semantics.updateTopValEnv(env,name,fval,false);
                             Semantics.updateTopValEnv(eval_env,name,fval,false))))
                    end
                 | processOverload(_) = () 
               val _ = processInputExpansion()
               val _ = processOverload(overload_sym)


               in
                  myPrint("\nNew symbol "^MS.name(full_fsym_name)^" declared.\n")
           end)
    end 
end

fun processFSymListDeclaration(afsl,mod_path,env,eval_env) = List.app (fn x => processFSymDeclaration(x,mod_path,env,eval_env)) afsl

fun processClearAssumBase() = 
      (top_assum_base := ABase.empty_ab;
       myPrint("\nAssumption base cleared.\n"))

fun processDemonAdd(e,fids,silent) = ()

fun processDemonLstAdd(dexps,fids) = (List.app (fn de => processDemonAdd(de,fids,true)) dexps;ok())
      
fun evaluateString(str) = TopEnv.processPhraseFromStringFun([Semantics.MLStringToAthString(str)],top_val_env,
                                                            {pos_ar=Array.array(3,A.dum_pos),file=""})

val _ = Semantics.evaluateString := evaluateString

(**
The following is useful only for evaluating expressions for their side effects, since they can't return 
a proper value (as values aren't defined until semantVal.sml).
**)

val _ = AT.evaluateString := (fn s:string => (evaluateString(s);()))

val (lp,rp,lb,rb,blank) = (Basic.lparen,Basic.rparen,Basic.lbrack,Basic.rbrack,Basic.blank)

fun setEvalProcBeingDefinedFlag(sym,b,code_string_opt,red_code_string_opt,dcode_string_opt) = 
      (case MS.find(Prop.fsym_def_table,sym) of
          SOME({evaluator_being_defined=ebd,code,red_code,dcode,...}) => 
               (ebd := b;
               (case code_string_opt of SOME(str) =>  (code := (if str = "" then "NO-CODE" else str)) | _ => ());
               (case red_code_string_opt of SOME(str) => (red_code := (if str = "" then "NO-CODE" else str)) | _ => ());
               (case dcode_string_opt of SOME(str) => (dcode := (if str = "" then "NO-CODE" else str)) | _ => ()))
        | _ => ())

fun redefineCodes(f,syms,just_defined,eval_env) = 
  let val just_defined_strings = map Symbol.name just_defined 
      fun doString(s,redefined_syms) = let val evaluation_result = evalStringFlexible(s,eval_env) handle _ => Semantics.unitVal
      	  			       	   val evaluation_results = (case evaluation_result of  SV.listVal(vals) => vals | _ => [])
                                           val symbol_value_pairs = Basic.zip(redefined_syms,evaluation_results) 
                                       in
                                          (case evaluation_results of
                                             [] => ()
                                           | _=> List.app (fn (name,value) => Semantics.updateValMap(eval_env,name,value)) symbol_value_pairs)
                                       end
      fun runCode(str) = let val rchars = rev(explode(str))
                             val syms =  (case Basic.skipUntil(rchars, fn c => c = #"]") of
                                             (_,rest) => (case Basic.skipUntilWithExtendedPred(tl rest, fn c => c = #"[", fn L => not(null(L)) andalso Basic.isWhiteSpace(hd(L))) of
                                                            (sym_chars,rest') => map Symbol.symbol (String.tokens Basic.isWhiteSpace (implode sym_chars))))
                         in
                            doString(str,syms)
                         end
      val table: bool MS.htable = MS.makeHTable()
      fun alreadyProcessed(sym:MS.mod_symbol) = 
             let val c1 = (case MS.find(table,sym) of SOME(_) => true | _ => false)
                 val c2 = Basic.isMemberEq(MS.nameAsSymbol sym,just_defined,S.symEq)
             in
                c1 orelse c2 
             end
      val _ = List.app (fn sym => MS.insert(table,sym,true)) syms
      fun processSym0(g:MS.mod_symbol) = 
               (case MS.find(Prop.fsym_def_table,g) of
                   SOME({eval_proc_name,needed_by,code,red_code,...}) => 
		   if Basic.isMemberEq(eval_proc_name,just_defined_strings,op=) then 
                      List.filter (fn s => not(alreadyProcessed(s))) needed_by
                   else
                        let val _ = (runCode(!code)) handle _ => ()
                            val _ = (runCode(!red_code)) handle _ => ()
			    val _ = MS.insert(table,g,true)
                        in
                          List.filter (fn s => not(alreadyProcessed(s))) needed_by
                        end
                 | _ => [])
      fun processSym(g:MS.mod_symbol) = processSym0(g)
      fun loop([]) = ()
        | loop(s::more) = 
             let val new_syms = processSym(s)
             in
                loop(new_syms@more)
             end
     val res = loop(List.filter (fn s => not(Basic.isMemberEq(MS.nameAsSymbol s,just_defined,Symbol.symEq))) syms)
  in
    res
  end

fun findSymsThatNeedSym(g) = 
  let val all_pairs = MS.listItemsi(Prop.fsym_def_table)
      val pairs = List.filter (fn (_,{guard_syms,occurring_syms,...}) => 
                                        Basic.isMemberEq(g,guard_syms@occurring_syms,MS.modSymEq)) 
			      all_pairs
  in
    map (fn (x,_) => x) pairs
  end

fun defineReducer(sym,env,eval_env) = 
  let val s = Symbol.symbol(TopEnv.getReduceProcName(sym,eval_env))
      val exp_str = "(string->symbol \"" ^ (MS.name sym) ^ "\")"
      val sym_val = evalStringFlexible(exp_str,eval_env) handle _ => Semantics.unitVal
  in
    (Semantics.updateTopValEnvLst(eval_env,[(s,sym_val)],true); 
     Semantics.updateTopValEnvLst(env,[(s,sym_val)],true))
  end

fun alreadyCompletelyDefined(f,def_eqs) = isFunDefExhaustive(f,def_eqs)

fun alreadyCompletelyDefined(f,def_eqs) = false


(****************************************************************************************************************************************)
(*      addFSymDefInfoAndCompile returns SOME(f) if the given p is a defining axiom for a function symbol f, and NONE otherwise.        *)
(****************************************************************************************************************************************)

fun addFSymDefInfoAndCompile(p,
			    env,
			    eval_env,
			    mod_path,
			    must_be_a_defining_equation,
			    skip_compilation,
			    pos,
			    all_syms,
			    assertion_name_string_opt) = 
  let 
      val given_axiom = p
      val _ = debugPrint("\nHere is the asserted sentence:\n"^(pprint(0,p)))
      val _ = debugPrint("\nAll syms: " ^ (Basic.printListStr(all_syms,MS.name,",")))
      val _ = A.no_dots_in_ids := false 
      val _ = debugPrint("\nMust be a defining equation: " ^ (Basic.boolToString(must_be_a_defining_equation)))
      val syms_that_need_f = ref([])
  in
     if not(!(Options.compile_mode_option)) then NONE
     else 
      (case let 
                val res = isDefiningEquationForSomeFunSymNew(p,must_be_a_defining_equation)
            in res end of
          NONE => if must_be_a_defining_equation then 
	            let val _ = debugPrint("\nMust be a defining equation but it's not...\n")   
                    in
                       Semantics.evError("This sentence is not a proper defining equation for a function symbol:\n"^(pprint(0,p)),SOME(pos)) 
                    end
                  else NONE
        | SOME({fsym=f,right_syms=right_syms,left_syms=left_syms,guard_syms=guard_syms',defining_props=defining_props,...}) => 
            if MS.modSymEq(f,Names.mequal_logical_symbol) orelse Data.isFreeStructureConstructor(f) then NONE
            else 
                let val _ = debugPrint("\nThis is a defining equation, for symbol: " ^ (MS.name f)
				       ^ "\nHere is the asserted sentence:\n"^(pprint(0,p))^
                                       "\nand here are its defining props:\n"^(Basic.printListStr(defining_props,(fn p => pprint(0,p)),"\n"))^
                                       "\nand here are the right_syms: "^(Basic.printListStr(right_syms,MS.name,",")))
		    val left_syms = Basic.removeEq(f,left_syms,MS.modSymEq)
		    val mod_names = map Symbol.name mod_path
		    val mod_path_string_with_dots = Basic.printListStr(mod_names,fn x => x,".")
		    val _ = debugPrint("\nProper mod path: " ^ mod_path_string_with_dots ^ "\n")
	            val already_defined = ref(false)                   					    
                    val abort = 
                          (case MS.find(Prop.fsym_def_table,f) of
                              SOME({eval_proc_name=ep_name,guard_syms=gsyms,occurring_syms=osyms,needed_by=nb,obsolete_axioms=obs_axioms,
			            eval_proc_name_with_full_mod_path=ep_name_with_mod_path,red_code=red_code_cell,
			            code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
				    defining_equations_finished=def_eq_finished,
				    defining_equations=def_eqs,bicond_sources=bsources,...}) =>
                               let val _ = syms_that_need_f := nb
			           val _ = debugPrint("\nStatus of defining_equations_finished here: " ^ (Basic.boolToString(!def_eq_finished)) ^ "\n")
			           val already_completely_defined = ((!def_eq_finished) = true)
				   val _ = (already_defined := already_completely_defined)
                               in
			        if already_completely_defined then 
				   let val _ = debugPrint("\nAlready completely defined.\n")
				   in 
				      true
				   end
                                else 
                                 if Basic.subsetEq(defining_props,def_eqs,Prop.alEq) then true
                                 else 
				 let val is_bicond = (case P.splitVars(p) of 
                                                        (SOME(A.forallCon),uvars,body) => 
							   (case Prop.isBiCond(body) of SOME(_) => true | _ => false)
                                                      | _ => false)
                                      val new_bicond_sources = if is_bicond then (map (fn d => (d,given_axiom)) defining_props) else []
                                 in
                                   (MS.insert(Prop.fsym_def_table,f,{eval_proc_name=ep_name,occurring_syms=Basic.removeDuplicatesEq(right_syms@osyms,MS.modSymEq),
				    				     eval_proc_name_with_full_mod_path=ep_name_with_mod_path,
								     guard_syms=Basic.removeDuplicatesEq(guard_syms'@gsyms,MS.modSymEq),needed_by=nb, 
                                                                     evaluator_being_defined=ebd,code=code_cell,dcode=dcode_cell,red_code=red_code_cell,
								     obsolete_axioms=(if Basic.isMemberEq(p,defining_props,Prop.alEq) then obs_axioms else p::obs_axioms),
                                                                     defining_equations=defining_props@def_eqs,
								     defining_equations_finished=def_eq_finished,
								     bicond_sources=new_bicond_sources@bsources});
                                    (HashTable.insert Prop.proc_name_table (ep_name,f));
                                    false)
                                 end
                                end
                            | _ => let val _ = syms_that_need_f := findSymsThatNeedSym(f)
                                       val ep_name = Semantics.nextAvailableEvalProcName(Symbol.name(MS.lastName f),eval_env,NONE) 
			               val ep_name_with_mod_path = if null(mod_names) then ep_name else (mod_path_string_with_dots ^ "." ^ ep_name)
				       val is_bicond = (case P.splitVars(p) of 
                                                           (SOME(A.forallCon),uvars,body) => (case Prop.isBiCond(body) of SOME(_) => true | _ => false)
                                                          | _ => false)
                                       val new_bicond_sources = if is_bicond then (map (fn d => (d,given_axiom)) defining_props) else []
                                       val _ = debugPrint("\nAbout to insert, with ep_name: " ^ ep_name ^ "\n")
                                       val _ = MS.insert(Prop.fsym_def_table,f,{eval_proc_name=ep_name,evaluator_being_defined=ref true,
 			       	                                                eval_proc_name_with_full_mod_path=ep_name_with_mod_path,
                                                                                guard_syms=guard_syms',code=ref(""),
										red_code=ref(""),
										dcode=ref(""),
										needed_by=(!syms_that_need_f),
										defining_equations_finished=ref(false),
  								                obsolete_axioms=(if Basic.isMemberEq(p,defining_props,Prop.alEq) then [] else [p]),
                                                                                occurring_syms=right_syms,defining_equations=defining_props,
										bicond_sources=new_bicond_sources})
                                       val _ = (HashTable.insert Prop.proc_name_table (ep_name,f))										
                                   in 
                                      false
                                   end)
                   val _ = if abort then debugPrint("\nAborting is true.\n") else debugPrint("\nAborting is false.\n")
	           val _ = addPropsToGlobalAb(defining_props,mod_path,assertion_name_string_opt)
                in
                   if abort orelse skip_compilation orelse (!already_defined) then (debugPrint("\nAborting...\n");NONE)
                   else let 
                            val A = MS.addLst(all_syms,Prop.tc' f)
                            val syms = if MS.isMember(f,A) then MS.listModSymbols(A) else f::(MS.listModSymbols A)

(** Set the "eval-procedure-being-defined" flags of all symbols in the transitive closure of f to true.
    These flags will be set back to false at the end: 
**) 
                            val _ = List.app (fn sym => setEvalProcBeingDefinedFlag(sym,true,NONE,NONE,NONE)) syms
                            val sym_last_names = map MS.lastName syms
                            fun makeSafe(str) = lp ^ "string->symbol " ^ Basic.string_quote ^  (Basic.escape str) ^ Basic.string_quote ^ rp
                            val sym_names = map (fn s => makeSafe(MS.name(s))) syms
                            val sym_names' = map (fn s => TopEnv.getEvalProcName(s,eval_env)) syms 
                            val red_sym_names' = map (fn s => TopEnv.getReduceProcName(s,eval_env)) syms 
                            val sym_name_string = Basic.printListStr(sym_names,(fn x => x)," ") 
                            val mod_path_names = map (fn mod_name => "\""^mod_name^"\"") mod_names
			    val mod_path_string = Basic.printListStr(mod_path_names,fn x => x," ")			   
			    val compiler_kind = "compile-symbols-simple"
			    val compiler_kind' = "compile-symbols-simple-with-default"
                            val code_string1 = lp^(Semantics.getSafeName compiler_kind)^blank^lb^sym_name_string^rb^blank^lb^mod_path_string^rb^rp
                            val code_string1' = lp^(Semantics.getSafeName compiler_kind')^blank^lb^sym_name_string^rb^blank^lb^mod_path_string^rb^rp
                            val main_sym_name = hd sym_names 
                            val dcode_string1 = lp^(Semantics.getSafeName "dcompile-symbol")^blank^main_sym_name^blank^lb^mod_path_string^rb^rp
                            val _ = debugPrint("\nCode string 1: "^code_string1^"\n")
                            val _ = debugPrint("\nCode string 1': "^code_string1'^"\n")
                            val _ = debugPrint("\nDCode string 1: "^dcode_string1^"\n")
                            val code_string2 = Semantics.AthStringToMLString(evalStringFlexible(code_string1,eval_env)) 
                                  handle Semantics.EvalError(msg,_) => ""
                                       | _ => ""
                            val code_string2' = Semantics.AthStringToMLString(evalStringFlexible(code_string1',eval_env)) 
                                  handle Semantics.EvalError(msg,_) => ""
                                       | _ => ""
                            val dcode_string2 = Semantics.AthStringToMLString(evalStringFlexible(dcode_string1,eval_env)) handle _ => ""
                            val _ = debugPrint("\nCode string 2: "^code_string2^"\n")
                            val _ = debugPrint("\nCode string 2': "^code_string2'^"\n")
                            val _ = debugPrint("\nDCode string 2: "^dcode_string2^"\n")
                            val syms_that_f_needs = Basic.removeDuplicatesEq(List.filter (fn s => not(Basic.isMemberEq(s,syms,MS.modSymEq))) 
                                                                            (right_syms@left_syms@guard_syms'),MS.modSymEq)
                             val _ = List.app (fn sym => (case MS.find(Prop.fsym_def_table,sym) of
                                                             SOME(_) => ()
                                                           | _ => if (MS.modSymEq(sym,Names.mequal_logical_symbol) orelse Data.isFreeStructureConstructor(sym)) then ()
                                                                  else defineReducer(sym,env,eval_env)))
                                               syms_that_f_needs
                            val evaluation_result = evalStringFlexible(code_string2,eval_env) handle _ => Semantics.unitVal
                            val evaluation_result' = evalStringFlexible(code_string2',eval_env) handle _ => Semantics.unitVal

                            val evaluation_results = case evaluation_result of
                                                        SV.listVal(vals) => vals
                                                     | _ => []
                            val evaluation_results' = case evaluation_result' of
                                                         SV.listVal(vals) => vals
                                                     | _ => []
                            val sym_last_names' = map Symbol.symbol sym_names'
                            val red_sym_last_names' = map Symbol.symbol red_sym_names'
                            val symbol_value_pairs = Basic.zip(sym_last_names',evaluation_results)
                            val red_symbol_value_pairs = Basic.zip(red_sym_last_names',evaluation_results')
                            val define_string = code_string2
                            val define_string' = code_string2'
                            (** Now insert the evaluation result - as a list of procedure values - into the eval_env for sym_names' **)
                            val _ = (case evaluation_results of
                                        [] => ()
                                      | _=> (Semantics.updateTopValEnvLst(eval_env,symbol_value_pairs,true);
                                             Semantics.updateTopValEnvLst(env,symbol_value_pairs,true)))
                            val _ = (case evaluation_results' of
                                        [] => ()
                                      | _=> (Semantics.updateTopValEnvLst(eval_env,red_symbol_value_pairs,true); 
                                             Semantics.updateTopValEnvLst(env,red_symbol_value_pairs,true)))
                            val dsym_name = "d"^(TopEnv.getEvalProcName(f,eval_env))
                            val dsym_symbol = Symbol.symbol(dsym_name)

                            val devaluation_result = evalStringFlexible(dcode_string2,eval_env) handle _ => Semantics.unitVal
                            (** Also insert the devaluation result: **)
                            val _ = (case devaluation_result of
                                        Semantics.unitVal => ()
                                      | _ => (Semantics.updateTopValEnv(eval_env,dsym_symbol,devaluation_result,true);
                                              Semantics.updateTopValEnv(env,dsym_symbol,devaluation_result,true)))
			    val _ = List.app (fn sym => (case MS.find(Prop.fsym_def_table,sym) of
                                                            SOME({eval_proc_name=ep_name,
							          eval_proc_name_with_full_mod_path=ep_name_with_mod_path,
								  defining_equations_finished=def_eq_finished,
							          guard_syms=gsyms,occurring_syms=osyms,needed_by=nb,obsolete_axioms=obs_axioms,red_code=red_code_cell,
			                                          code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,defining_equations=def_eqs, 
								  bicond_sources=bsources,...}) => 
								  
                                                                     MS.insert(Prop.fsym_def_table,sym,
                                                                       {eval_proc_name=ep_name,
								       defining_equations_finished=def_eq_finished,
  								        eval_proc_name_with_full_mod_path=ep_name_with_mod_path,
								        occurring_syms=osyms,guard_syms=gsyms,obsolete_axioms=obs_axioms,
									needed_by=(if Basic.isMemberEq(f,nb,MS.modSymEq) then nb else f::nb),
                                                                        evaluator_being_defined=ebd,code=code_cell,dcode=dcode_cell,red_code=red_code_cell,
									bicond_sources=bsources,
                                                                        defining_equations=def_eqs})
                                                          | _ => ()))
                                              syms_that_f_needs
                            val _ = (case !syms_that_need_f of 
                                       [] => ()
                                     | L => (redefineCodes(f,L,sym_last_names',eval_env)))
                        in
                           ((List.app (fn sym => if MS.modSymEq(sym,f) then
                                                  setEvalProcBeingDefinedFlag(sym,false,SOME(define_string),SOME(define_string'),SOME(dcode_string2))
                                                else setEvalProcBeingDefinedFlag(sym,false,SOME(define_string),SOME(define_string'),NONE)) syms; 
						A.no_dots_in_ids := true);
                             SOME(f))						
                        end
                end)
  end

fun rootSym(term) = 
  (case AT.isApp(term) of
     SOME(f,_) => f)

fun equationalToRelational'(p) = 
 (case P.splitVars(p) of 
     (SOME(A.forallCon),uvars,body) => 
        (case Prop.isAtom(body) of
            SOME(t) => (case AT.isApp(t) of 
                           SOME(f,[left,right]) => 
                               if MS.modSymEq(N.mequal_logical_symbol,f) then
                                  (if AT.isTrueTerm(right) then SOME((rootSym(left),P.makeUGen(uvars,P.makeAtom(left))))
                                   else if AT.isFalseTerm(right) then SOME(rootSym(left),P.makeUGen(uvars,P.makeNegation(P.makeAtom(left))))
                                        else if F.sortEq(AT.getSort(left),F.boolean_sort) andalso not(AT.isVar(left)) andalso not(AT.isVar(right)) then
                                                SOME((rootSym(left),P.makeUGen(uvars,P.makeBiConditional(P.makeAtom(left),P.makeAtom(right)))))
                                             else NONE)
                               else NONE
                        | _ => NONE)
         | _ => NONE)
   | _ => NONE)

fun equationalToRelational(p) = 
       (case equationalToRelational'(p) of
           SOME(f,q) => SOME(f,q)
         | _ => NONE) handle _ => NONE
           
val all_fun_defs_must_be_in_one_block = ref(true)

fun completeDefiningEquations(f) = 
     (case MS.find(Prop.fsym_def_table,f) of
       SOME({defining_equations_finished,...}) => 
         let val cond1 = not(!all_fun_defs_must_be_in_one_block)
         in
         if (cond1 orelse Data.isStructureConstructorBool(f)) then () 
         else defining_equations_finished := true
        end
   | _ => ())

fun isMetaIdentifier(v) = 
      (case TopEnv.coerceValIntoTerm(v) of 
          SOME(term) => AthTerm.isIdeConstant(term)
        | _ => NONE)

fun isMetaIdentifierBool(v) = 
      (case TopEnv.coerceValIntoTerm(v) of 
          SOME(term) => (case AthTerm.isIdeConstant(term) of SOME(_) => true | _ => false)
        | _ => false)

fun addMetaIdBindings(vals,env,eval_env,assertion_pos,close) = 
  let fun loop([])  = ()
        | loop(v1::v2::more) =
            (case isMetaIdentifier(v2) of
                SOME(str) => (case TopEnv.coerceValIntoProp(v1) of
                                NONE => Semantics.evError("Only sentences can be asserted",SOME(assertion_pos))
                              | SOME(P) => 
                                     let val sym = S.symbol str
				         val prop_val = if close then SV.propVal(Prop.close(P)) else SV.propVal(P)
                                         val _ = Semantics.updateTopValEnv(env,sym,prop_val,false)
                                         val _ = Semantics.updateTopValEnv(eval_env,sym,prop_val,false)
                                     in
    	 	                       loop(more)
                                     end)
            | _ => (case (TopEnv.coerceValIntoProp(v1),TopEnv.coerceValIntoProp(v2)) of 
                       (SOME(_),SOME(_)) => loop(v2::more)
                     | _ => Semantics.evError("Only sentences can be asserted",SOME(assertion_pos))))
        | loop([v]) =
              (case TopEnv.coerceValIntoProp(v) of
                  SOME(_) => ()
                | _ => Semantics.evError("Only sentences can be asserted",SOME(assertion_pos)))
  in
    loop(vals)
  end

fun processAssertion(e,env,eval_env,fids,mod_path,file,{assertion_name:A.param option,close:bool}) = 
          let val last_prop_asserted = ref(NONE)
              val assertion_pos = A.posOfExp(e)
	      val assertion_name_string_opt = 
 	                (case assertion_name of 
                            SOME({name,...}:A.param) => SOME(S.name(name))
                          | _ => NONE)
              val ip = infixProcess(A.exp e,eval_env,fids)
              val fids = MS.add(Names.mite_symbol,fids)
              val (v_opt,error_msg,error_pos) = 
                           (SOME(evalPhrase((ip,fids),eval_env,!top_assum_base)),"",NONE)
                                handle Semantics.EvalError(msg,pos_opt) => (NONE,msg,pos_opt)                                        
              fun assertError() = myPrint("\nOnly sentences can be asserted!\n")
              fun addProp(p) = (addPropToGlobalAb(p,mod_path,assertion_name_string_opt);
                                myPrint("\nThe sentence "^"\n"^pprint(0,p)^"\n"^
                                        "has been added"^" to the assumption base.\n"))
	      val varSortPrinter = F.makeVarSortPrinter() 
              val named_assertion = not(assertion_name=NONE)
              fun addNameBinding(assertion_name,v) = 
                     (case assertion_name of 
                         SOME({name,...}:A.param) => (Semantics.updateTopValEnv(env,name,v,true);Semantics.updateTopValEnv(eval_env,name,v,true))
                       | _ => ())
              fun addTopNameBinding(v) = addNameBinding(assertion_name,v)
              val starting_ab = !top_assum_base 
              fun doVal(v,is_list,last_value) = 
               let val fun_sym_being_defined = ref(NONE)
               in 
                (case Semantics.coerceValIntoProp(v) of
                   SOME(P) => let val P' = if close then Prop.close(P) else P
		                  val _ = last_prop_asserted := SOME(P')                                      
                                  val res = 
                                  (case (Prop.freeVars P') of
                                    [] => (addProp(P');
				          fun_sym_being_defined := 
                                           addFSymDefInfoAndCompile(P',env,eval_env,mod_path,
					                           false,false,assertion_pos,[],
								   assertion_name_string_opt);   
                                           (case equationalToRelational(P') of
                                               SOME(f,Q) => let val _ = (case MS.find(Prop.fsym_def_table,f) of
                                                                             SOME({eval_proc_name=ep_name,
									           eval_proc_name_with_full_mod_path=ep_name_full,
									           guard_syms=gsyms,occurring_syms=osyms,
									           needed_by=nb,obsolete_axioms=obs_axioms,red_code=red_code_cell,
                 			                                           code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
										   bicond_sources=bsources,
										   defining_equations_finished=def_eq_finished,
										   defining_equations=def_eqs}) => 
                                                                             MS.insert(Prop.fsym_def_table,f,
                                                                               {eval_proc_name=ep_name,
									        eval_proc_name_with_full_mod_path=ep_name_full,
										guard_syms=gsyms,occurring_syms=osyms,
									        needed_by=nb,obsolete_axioms=Q::obs_axioms,red_code=red_code_cell,
                 			                                        code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
										bicond_sources=bsources,
										defining_equations_finished=def_eq_finished,					
									        defining_equations=def_eqs})										   
                                                                          | _ => ())
                                                          in
                                                              addPropToGlobalAb(Q,mod_path,assertion_name_string_opt)
							  end
                                             | _ => ());
                                           if not(is_list) then addNameBinding(assertion_name,Semantics.propVal P') else ();
                                           P')
                                  | L => (myPrint("\nWarning: the asserted sentence\n"^
                                                   P.toPrettyString(0,P',varSortPrinter)^"\nhas free variables:\n"^
                                                   (Basic.printListStrCommas(L,
  					             fn v => AthTermVar.toString(v,varSortPrinter)))^"\n");
                                          if not(is_list) then addNameBinding(assertion_name,Semantics.propVal P') else ();
                                          addProp(P');
                                          addFSymDefInfoAndCompile(P',env,eval_env,mod_path,false,
					                           false,assertion_pos,[],assertion_name_string_opt); 
                                          (case equationalToRelational(P') of
                                              SOME(f,Q) => let val _ = (case MS.find(Prop.fsym_def_table,f) of
                                                                             SOME({eval_proc_name=ep_name,
									           eval_proc_name_with_full_mod_path=ep_name_full,
                                                                                   guard_syms=gsyms,occurring_syms=osyms,
									           needed_by=nb,obsolete_axioms=obs_axioms,red_code=red_code_cell,
                 			                                           code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
										   bicond_sources=bsources,
										   defining_equations_finished=def_eq_finished,
										   defining_equations=def_eqs}) => 
                                                                             MS.insert(Prop.fsym_def_table,f,
                                                                               {eval_proc_name=ep_name,eval_proc_name_with_full_mod_path=ep_name_full,
									        guard_syms=gsyms,occurring_syms=osyms,
									           needed_by=nb,obsolete_axioms=Q::obs_axioms,red_code=red_code_cell,
                 			                                           code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
										   bicond_sources=bsources,
										   defining_equations_finished=def_eq_finished,
										   defining_equations=def_eqs})										   
                                                                          | _ => ())
                                                           in 
                                                                addPropToGlobalAb(Q,mod_path,assertion_name_string_opt)
                                                           end
                                            | _ => ());
                                          P'))
                              in 
                                 (case (!fun_sym_being_defined) of 
				     SOME(f) => if last_value then
                                                let val _ = completeDefiningEquations(f)
                                                in
						   res 
                                                end
                                                else res
                                   | _ => res)
                              end
                 | _ => Semantics.evError("Only sentences can be asserted",SOME(assertion_pos)))
               end 
          in
              case v_opt of  
                 SOME(lval as Semantics.listVal([Semantics.listVal(blocks:Semantics.value list),Semantics.listVal(bindings)])) => 
(** 
   Each "block" is a two-element list [f,eqns] consisting of a function symbol f 
   and a list of equations eqns, which are defining equations for f.       
**) 
                   let val last_block_index = List.length blocks 
                       val all_eqns = ref([])
                       val no_error = ref(true)
		       val all_symbols = (map (fn (Semantics.listVal([symbol_val,Semantics.listVal(eqn_vals)]):Semantics.value) =>
     	   	               	          	           (case Semantics.coerceValIntoTermCon(symbol_val) of 
                                                               SOME(Semantics.regFSym(fsym)) => Data.fsymName(fsym)))
                                              blocks)
                       fun processBlock(Semantics.listVal([symbol_val,Semantics.listVal(eqn_vals)]):Semantics.value,block_index) = 
                         if !no_error then
                             let val sym = (case Semantics.coerceValIntoTermCon(symbol_val) of 
                                               SOME(Semantics.regFSym(fsym)) => Data.fsymName(fsym))
                                 val already_has_defining_equations = (case MS.find(Prop.fsym_def_table,sym) of
                                                                          SOME(_) => true | _ => false)
                                 val _ = if already_has_defining_equations andalso not(MS.modSymEq(sym,N.mequal_logical_symbol)) then
                                         evWarning("The assumption base already contains defining axioms for "^(MS.name(sym)),SOME(assertion_pos)) 
                                         else ()
                                 fun hasDTArg() = let val (arg_sorts,_,_,has_pred_based_sorts) = Data.getSignature(sym)
                                                      fun isDatatype(sort) = (case F.isApp(sort) of
                                                                                SOME(f,_) => Data.isStructure(f)
                                                                               | _ => false)
                                                  in 
                                                     List.exists isDatatype arg_sorts 
                                                  end 
                                 val _ = if  hasDTArg() then () 
                                         else Semantics.evError("Expecting a function symbol with a datatype as at least\none of its argument sorts; "^
                                                                (MS.name sym)^" is not such a symbol",SOME(assertion_pos))
                                 val eqns = List.map (fn v => case Semantics.coerceValIntoProp(v) of
                                                                SOME(P) => P
                                                              | _ => Semantics.evError("Only sentences can be asserted",SOME(assertion_pos)))
                                            eqn_vals 
                                 val last_eqn_index = List.length eqns 
                                 fun skipCompilation(block_index,eqn_index) =
                                           (eqn_index < last_eqn_index andalso not(already_has_defining_equations))
                                 val _ = Basic.appWithIndex((fn (p,eqn_index) => 
                                                                  let 
                                                                  in
                                                                   if !no_error then
                                                                   ((addProp(p);
                                                                     if named_assertion then all_eqns := p::(!all_eqns) else ();
                                                                     addFSymDefInfoAndCompile(p,env,eval_env,
								                              mod_path,true, 
                                                                                              skipCompilation(block_index,eqn_index),assertion_pos,all_symbols,assertion_name_string_opt);
                                                                     (case equationalToRelational(p) of
                                                                         SOME(f,Q) => 
									   let val _ =  (case MS.find(Prop.fsym_def_table,f) of
                                                                             SOME({eval_proc_name=ep_name,guard_syms=gsyms,occurring_syms=osyms,
									           eval_proc_name_with_full_mod_path=ep_name_full,
									           needed_by=nb,obsolete_axioms=obs_axioms,red_code=red_code_cell,
                 			                                           code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
										   bicond_sources=bsources,
										   defining_equations_finished=def_eq_finished,
										   defining_equations=def_eqs}) => 

                                                                             MS.insert(Prop.fsym_def_table,f,
                                                                               {eval_proc_name=ep_name,guard_syms=gsyms,occurring_syms=osyms,
									        eval_proc_name_with_full_mod_path=ep_name_full,
									           needed_by=nb,obsolete_axioms=Q::obs_axioms,red_code=red_code_cell,
                 			                                           code=code_cell,dcode=dcode_cell,evaluator_being_defined=ebd,
										   bicond_sources=bsources,
										   defining_equations_finished=def_eq_finished,
										   defining_equations=def_eqs})										   
                                                                          | _ => ())
                                                                     in
                                                                         addPropToGlobalAb(Q,mod_path,assertion_name_string_opt)
                                                                     end
                                                                      | _ => ())
                                                                     )
                                                                     handle Semantics.EvalError(msg,pos_opt) => 
                                                                     ((no_error := false;
                                                                       print("\n"^msg^"\n\nUndoing the effects of the assertion...\n");
                                                                       if named_assertion andalso not(null(!all_eqns)) then all_eqns := tl(!all_eqns) else ();
								       P.removeFromModuleAb(mod_path,p);
                                                                       top_assum_base := ABase.remove(!top_assum_base,p)) handle _ => ()))
                                                                   else ()
                                                                  end),eqns)
                            in
                               if !no_error then (checkFunDef(sym,eqns,SOME assertion_pos);()) else ()
                            end
                         else ()
                       fun addNameBinding(Semantics.listVal([tv,v])) = 
                               (case Semantics.coerceValIntoTerm(tv) of
                                   SOME(t) => (case AT.isIdeConstant(t) of
                                                  SOME(str) => (Semantics.updateTopValEnv(env,Symbol.symbol str,v,false);
                                                                Semantics.updateTopValEnv(eval_env,Symbol.symbol str,v,false))
                                                | _ => ())
                                 | _ => ())
                       val _ = Basic.appWithIndex(processBlock,blocks)
                       val _ = map addNameBinding bindings 
                       val _ = addTopNameBinding(Semantics.listVal(map Semantics.propVal (!all_eqns)))
                   in
                      ()
                   end 
               | SOME(lval as Semantics.listVal(vals)) => let fun mapIndex([],res) = rev(res)
                                                                | mapIndex([v],res) = let val r = Semantics.propVal(doVal(v,true,true))
                                                                                      in
                                                                                        rev(r::res)
                                                                                      end
                                                                | mapIndex(v::more,res) = let val r = Semantics.propVal(doVal(v,true,false))
                                                                                          in
   										            mapIndex(more,r::res)
                                                                                          end
                                                              val prop_vals = ((mapIndex(Basic.filterOut(vals,isMetaIdentifierBool),[]))
                                                                                 handle Semantics.EvalError(msg,pos_opt) => 
                                                                                 let val msg' = if length(ABase.getAll(!top_assum_base)) >  
                                                                                                   length(ABase.getAll(starting_ab)) 
                                                                                                then (top_assum_base := starting_ab;
                                                                                                      "\nUndoing previous assertions in this list.") 
												else ""
                                                                                 in
                                                                                   raise Semantics.EvalError(msg^msg',pos_opt)
                                                                                 end)
                                                          in
						            (case vals of
                                                                [] => (addNameBinding(assertion_name,Semantics.listVal prop_vals);
							               addMetaIdBindings(vals,env,eval_env,assertion_pos,close))
                                                              | _ => (addNameBinding(assertion_name,Semantics.listVal prop_vals);
							              addMetaIdBindings(vals,env,eval_env,assertion_pos,close)))
                                                          end
               | SOME(v) => (doVal(v,false,false);())
               | NONE => raise Semantics.EvalError(error_msg,error_pos)
          end

fun processAssertions(exps,env,eval_env,fids,mod_path,file,closed) = 
  List.app (fn a => processAssertion(a,env,eval_env,fids,mod_path,file,{assertion_name=NONE,close=closed})) exps;

fun processRetraction(e,env,eval_env,fids) = 
          let val ip = infixProcess(A.exp e,eval_env,fids)
              val fids = MS.add(Names.mite_symbol,fids)
              val (v_opt,error_msg) = (SOME(evalPhrase((ip,fids),top_val_env,!top_assum_base)),"")
                                        handle Semantics.EvalError(msg,_) => (NONE,"\n"^msg^"\n")
              fun retractError() = myPrint("\nOnly sentences can be retracted!\n")
              fun rmProp(p) = (let val fsym = isDefiningEquationForSomeFunSymNew(p,true)
				   fun removeBinding(env,name) = ((Semantics.removeEnvBinding(env,name)) handle _ => ())
	                           val _ = (case fsym of
                                               SOME({fsym=f,
					             defining_props=defining_props,...}) =>
						  (case MS.find(Prop.fsym_def_table,f) of
                                                      NONE => ()
                                                    | SOME({eval_proc_name=ep_name,obsolete_axioms=obs_axioms, 
						            eval_proc_name_with_full_mod_path=ep_name_with_mod_path,...}) => 
 					                let val red_proc_name = Symbol.symbol(TopEnv.getReduceProcName(f,eval_env))
							    val all_defining = defining_props @ obs_axioms 
                                                        in
   	 					          if Basic.isMemberEq(p,all_defining,Prop.alEq) then
						             let val _ = ((MS.removeHT(Prop.fsym_def_table,f);()) handle _ => ())
								 val proc_name = Symbol.symbol(ep_name)
							         val _ = removeBinding(env,proc_name)
							         val _ = removeBinding(eval_env,proc_name)
							         val _ = removeBinding(env,red_proc_name)
							         val _ = removeBinding(eval_env,red_proc_name)
                                                             in
                                                               ()
                                                             end
                                                          else ()			   
                                                        end)
                                             | _ => ())
                               in
			         ()
                               end;
                               top_assum_base := ABase.remove(!top_assum_base,p);
	                       P.removeFromAllModuleAbs(p);
                               myPrint("\nThe sentence "^"\n"^pprint(0,p)^"\nhas been removed from"^" the assumption base.\n"))
              fun doVal(v) = (case Semantics.coerceValIntoProp(v) of
                                 SOME(P) => (case ABase.isMember(P,!top_assum_base) of
                                                true => rmProp(P)
                                              | _ => myPrint("\nThe given sentence is not in "^"the assumption base.\n"))
                               | _ => retractError())
          in
              case v_opt of
                 SOME(Semantics.listVal(vals)) => List.app doVal vals
               | SOME(v) => doVal(v)
               | NONE => myPrint(error_msg)
          end

fun processRetractions(exps,env,eval_env,fids) = List.app (fn e => processRetraction(e,env,eval_env,fids)) exps

exception defError of string

fun processDefinitionLst(pats,list_name_option,pos,def_phrase,env,eval_env,fids,vars,file,is_private,mod_path) = 
  (case processPhraseAndReturn(def_phrase,env,eval_env,fids,mod_path) of 
      v as (Semantics.listVal vals) => 
                                    let val new_pat = A.listPats({member_pats=pats,pos=pos})
                                    in
                                     ((case Semantics.matchPat(v,new_pat,
                                                            (fn (e,binding_map) => 
                                                              (case binding_map of 
                                                                  NONE => Semantics.evalExp(e,eval_env,!top_assum_base)
                                                                | SOME(map) => let val (vmap,mmap) = getValAndModMaps(!eval_env)
                                                                                   val eval_env' = ref(SV.valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                                                               in
                                                                                  Semantics.evalExp(e,eval_env',!top_assum_base)
                                                                               end))) of 
                                       SOME(map,_) => let 
                                                        val pids = Symbol.listSymbols(A.patBindableIds(A.listPats({member_pats=pats,pos=pos})))
                                                        fun f(pid) = (case Symbol.lookUp(map,pid) of 
                                                                         SOME(v) => v 
                                                                       | _ => raise defError("\nError: Value for pattern identifier "^
                                                                                            (Symbol.name(pid))^" could not be obtained.\n"))
                                                        val vals = List.map f pids
                                                        val pids_and_vals = Basic.zip(pids,vals)
                                                        val _ = Semantics.updateTopValEnvLst(eval_env,pids_and_vals,false)
                                                        val _ = if is_private then () else Semantics.updateTopValEnvLst(env,pids_and_vals,false)
                                                    in 
                                                       if null(pids) then print("\nNo definitions.\n") else 
                                                       (List.app (fn (pid,v) => printDefinitionMessage(Symbol.name pid,v,mod_path,is_private)) pids_and_vals)
                                                       handle defError(str) => print(str)
                                                    end
                                     | _ => print("\nThe "^(Semantics.valLCTypeAndString(v))^" did not match the pattern "^
                                                  (A.printPat(A.listPats({member_pats=pats,pos=pos})))^".\n"));
                                     (case list_name_option of
                                        SOME(name) => (Semantics.updateTopValEnv(eval_env,name,v,false);
                                                       printDefinitionMessage(Symbol.name name,v,mod_path,is_private);
                                                       if is_private then () else Semantics.updateTopValEnv(env,name,v,false))
                                      | _ => ()))
                                    end
    | v => print("\nError, "^(A.posToString(A.posOfPhrase(def_phrase)))^": "^
                 Semantics.wrongArgKindInOneLine("",1,Semantics.listLCType,v)^".\n"))

fun processDefinitions(name_phrase_pairs,fids,env,eval_env,file,is_private,mod_path) = 
      let val names = map (fn ({name,...},phrase) => name) name_phrase_pairs
          val mnames = map A.mSym names 
          val _ = MS.setApp (fn msym => if boundMSym(msym,!eval_env) orelse Basic.isMemberEq(msym,mnames,MS.modSymEq) then ()
                                        else Semantics.evError("Unbound identifier: "^(MS.name(msym)),SOME(A.posOfExp(#2((hd(name_phrase_pairs)))))))
                            fids 
          fun getBindings([]) = []
            | getBindings((def_name:A.possibly_typed_param as {name,op_tag,...},def_exp)::more) = 
               let val dname = #name(def_name)
               in
                 ({bpat=A.idPat(def_name),
                   def=A.namePhrase(A.exp(def_exp),Symbol.name dname),
                   pos=dum_pos})::getBindings(more)
               end
          val bindings = getBindings(name_phrase_pairs)
          val body = A.listExp({members=(map (fn {bpat=A.idPat({name as def_name,...}),def,...} => 
                                              A.exp(A.idExp({msym=A.msym(def_name),sym=def_name,mods=[],no_mods=true,pos=dum_pos}))) bindings),
                                pos=dum_pos})
          val desugared_exp = A.letRecExp({bindings=bindings,body=body,pos=dum_pos})
          val _ = if (!Options.compilation_on) then
                  let val _ = printToCR("\n\n---------------------------- Athena Definition ------------------------------\n\n")
                      val _ = printToCR(A.unparseExp(desugared_exp)) handle _ => ()
                      val _ = printToCR("\n\n********* SML Translation: **********************\n\n")
                      val _ = compilePhrase(A.exp(desugared_exp))
                  in 
                     printToCR("\n\n---------------------------- End ------------------------------\n\n")
                  end
                  else ()
          val _ = (case processPhraseAndReturnInEnv(A.exp(desugared_exp),fids,env,eval_env,mod_path,NONE) of
                         Semantics.listVal(vals) => 
                                ((List.app (fn (name,v) => (Semantics.updateTopValEnv(eval_env,name,v,false);
                                                            if is_private then () else Semantics.updateTopValEnv(env,name,v,false)))
                                           (ListPair.zip(names,vals)));
                              let val names_as_strings = map (fn s => Symbol.name(s)) names
                              in
                                 List.app (fn (str,v) => printDefinitionMessage(str,v,mod_path,is_private))
                                          (ListPair.zip(names_as_strings,vals))
                              end)
                    | _ => Semantics.evError("\nA unexpected error occured; definition(s) not accepted.\n"^
                                             "Please try again",NONE))
      in
         ()
      end

fun processRuleDefinition(rule_name,rule_body,fids,env,eval_env) =
      let val e = A.desugarRuleDef(Symbol.name(rule_name),rule_body)
          val pfs = Names.private_force_symbol
          val mpfs = Names.mprivate_force_symbol
          val (v_opt,error_msg) = (SOME(evalExp((e,MS.add(mpfs,fids)),eval_env,!top_assum_base)),"")
                                       handle Semantics.EvalError(msg,pos_opt) => (NONE,"\n"^msg^"\n")
         fun doDefine(v) = (Semantics.updateTopValEnv(env,rule_name,v,false);
                            Semantics.updateTopValEnv(eval_env,rule_name,v,false))
      in
         (case v_opt of
            SOME(v as SV.methodVal(_)) => doDefine(v)
          | SOME(v as SV.primUMethodVal(_)) => doDefine(v)
          | SOME(v as SV.primBMethodVal(_)) => doDefine(v)
          | SOME(v as SV.closUMethodVal(_)) => doDefine(v)
          | SOME(v as SV.closBMethodVal(_)) => doDefine(v)
          | SOME(v as SV.closMethodVal(_)) => doDefine(v))
      end
 
fun isObType(t:SymTerm.term) = SymTerm.isLegal(t,fn sym => MS.lookUp(!structure_and_domain_arities,sym),
						 fn sym => false)

fun pathToString(path) = if null(path) then "[]" else Basic.printListStr(path,Symbol.name,".")

fun findPath(mod_name,paths,pos) = 
  let fun loop([]) = evError("Invalid open-module directive: no module by the name of "^(Symbol.name(mod_name))^" is visible here",SOME(pos))
        | loop(path::rest) =
             (case Semantics.lookUpModuleBasic(!SV.top_val_env,path,mod_name) of
                 SOME({env,...}:SV.module) => path 
               | _ => loop(rest))
  in
    loop(paths)
  end

fun findPathMS(mod_names,sym,paths,pos) = 
  let fun loop([]) = NONE
        | loop(path::rest) =
            let val path' = path@mod_names
            in
               (case Semantics.lookUpModuleBasic(!SV.top_val_env_backup,path',sym) of
                   SOME({env,...}:SV.module) => SOME(path)
                 | _ => loop(rest))
            end
  in
    loop(paths)
  end

fun processOpenModule(msym,
	              pos,
		      env as ref(SV.valEnv({val_map=env_val_map,mod_map=env_mod_map})),
                      eval_env as ref(SV.valEnv({val_map=eval_val_map,mod_map=eval_mod_map})),
		      mod_path) =   
 let fun setGivenEnv(new_env) = env := new_env
     val (mod_names,sym) = MS.split(msym)
     val path_opt = findPathMS(mod_names,sym,!(Paths.open_mod_paths),pos)
 in
    (case path_opt of
        SOME(path) => 
          let val new_path = path@mod_names@[sym]    
          in
           (case Semantics.lookUpModuleBasic(!eval_env,mod_names,sym) of
              SOME(module:SV.module as {mod_name,env as SV.valEnv({val_map=imported_val_map,mod_map=imported_mod_map}),open_mod_directives as omd,...}) => 
                 let val _ = Paths.open_mod_paths := new_path::(omd@(!(Paths.open_mod_paths)))
                     val _ = Paths.open_mod_directives := new_path::(omd@(!(Paths.open_mod_directives)))
                     val eval_env' = SV.valEnv({val_map=Symbol.augment(eval_val_map,imported_val_map),
                                                mod_map=Symbol.augment(eval_mod_map,imported_mod_map)})
                     val env' =  SV.valEnv({val_map=Symbol.augment(env_val_map,imported_val_map),
                                            mod_map=Symbol.augment(env_mod_map,imported_mod_map)})
                     val _ = (eval_env := eval_env';setGivenEnv(env'))
                 in
                   ok() 
                 end
            | _ => evError("Invalid open-module directive: no module by the name of "^(MS.name(msym))^" is visible here",SOME(pos)))
          end
    | NONE => 
           (case Semantics.lookUpModuleBasic(!eval_env,mod_names,sym) of
              SOME(module:SV.module as {mod_name,env as SV.valEnv({val_map=imported_val_map,mod_map=imported_mod_map}),open_mod_directives as omd,...}) => 
                 let val (L,s) = MS.split(mod_name)
                     val mod_name_path = L@[s]
                     val new_path' = if Basic.nonEmptyCommonprefixEq(mod_name_path,mod_path,Symbol.symEq) then
                                        mod_name_path
                                     else evError("Invalid open-module directive: no module by the name of "^(MS.name(msym))^" is visible here",SOME(pos))
                     val _ = Paths.open_mod_paths := new_path'::(omd@(!(Paths.open_mod_paths)))
                     val _ = Paths.open_mod_directives := new_path'::(omd@(!(Paths.open_mod_directives)))
                     val eval_env' = SV.valEnv({val_map=Symbol.augment(eval_val_map,imported_val_map),
                                                mod_map=Symbol.augment(eval_mod_map,imported_mod_map)})
                     val env' =  SV.valEnv({val_map=Symbol.augment(env_val_map,imported_val_map),
                                            mod_map=Symbol.augment(env_mod_map,imported_mod_map)})
                     val _ = (eval_env := eval_env';setGivenEnv(env'))
                 in
                   ok() 
                 end
            | _ => evError("Invalid open-module directive: no module by the name of "^(MS.name(msym))^" is visible here",SOME(pos))))
  end

fun processOpenModules(msyms_and_positions,env,eval_env,mod_path) =   
  List.app (fn (msym,pos) => processOpenModule(msym,pos,env,eval_env,mod_path)) msyms_and_positions

fun processSortDefinition(defined_name,A.exp(e),fids,mod_path,env:SV.value_environment ref,eval_env:SV.value_environment ref,file,is_private) = 
      (case A.isTermApp(e) of
          SOME(t) => let 
                         val t' = Terms.replaceSymTermConstants(t,fn sym => MS.find(Data.sort_abbreviations,sym))
                         val new = Terms.putBogusTags(t',A.dum_pos)
                         val t'' = SV.qualifySort(new)
                         val t''' = SymTerm.stripTags(t'')
                     in
                        if isObType(t''') then 
                        let 
                            val full_msym = SV.qualifyName(defined_name,mod_path)
                        in
                         (MS.insert(Data.sort_abbreviations,full_msym,t''');
                          myPrint("\nDefined sort abbreviation "^MS.name(full_msym)^".\n"))
                        end
                        else 
                          evError("\nInvalid sort abbreviation\n",SOME(A.posOfExp(e)))
                     end)

fun processDefinition(defined_name,A.exp(e),fids,mod_path,env:SV.value_environment ref,eval_env:SV.value_environment ref,file,is_private) = 
          processDefinitions([(A.makePTP defined_name,e)],fids,env,eval_env,file,is_private,mod_path)
  | processDefinition(name,phr as A.ded(d),fids,mod_path,env:SV.value_environment ref,eval_env,file,is_private) =   
         case processPhraseAndReturnInEnv(phr,fids,env,eval_env,mod_path,SOME(name))  of 
            v as Semantics.propVal(p) => (if is_private then () else Semantics.updateTopValEnv(env,name,Semantics.propVal(p),false);
                                          Semantics.updateTopValEnv(eval_env,name,Semantics.propVal(p),false);
                                          top_assum_base := ABase.augment(!top_assum_base,[p]);
                                          printVal(v,(true,NONE));
                                          printDefinitionMessage(Symbol.name name,v,mod_path,is_private))
          | _ => Semantics.evError("\nA very strange error occured; please try again",NONE);

fun getTerms(val_lst,pos_array,method_name) = 
  let fun msg(v) = "Argument of the wrong kind supplied to the method "^method_name^
                   "; the method requires terms as arguments, but here the argument was a "^
                   Semantics.valLCTypeAndString(v)      
       fun getTerms([],results,_) = rev results
         | getTerms(v::rest,results,i) = 
             (case Semantics.coerceValIntoTerm(v) of
                 SOME(t) => getTerms(rest,t::results,i+1)
               | _ => evError(msg(v),SOME(Array.sub(pos_array,i))))
  in 
    getTerms(val_lst,[],2)
  end;

fun getTermsNoPos(val_lst,method_name) = 
  let fun msg(v) = "Argument of the wrong kind supplied to the method "^method_name^
                   "; the method requires terms as arguments, but here the argument was a "^
                   Semantics.valLCTypeAndString(v)      
       fun getTerms([],results,_) = rev results
         | getTerms(v::rest,results,i) = 
             (case Semantics.coerceValIntoTerm(v) of
                 SOME(t) => getTerms(rest,t::results,i+1)
               | _ => primError(msg(v)))
  in 
    getTerms(val_lst,[],2)
  end

fun makeIntroElimMethods(sym_name,arg_vars,definiens_prop,env,eval_env,is_poly) = 
 let val evError = Semantics.evError
     val sym_name_str = MS.name(sym_name)
     val intro_method_name = sym_name_str^"-intro"
     val elim_method_name = sym_name_str^"-elim"
     val actual_arg_var_opts = map (fn v => Basic.findInList(Prop.freeVars(definiens_prop),fn v' => ATV.nameEq(v,v')))
                                    arg_vars
     val actual_arg_vars = map (fn opt => (case opt of
  					      SOME(v) => v
                                            | _ => ATV.fresh())) actual_arg_var_opts
     val new_arg_vars = map (fn actual_arg_var => ATV.freshWithSort(ATV.getSort(actual_arg_var))) actual_arg_vars
     val new_arg_vars_as_terms = map AthTerm.makeVar new_arg_vars
     val new_definiens = Prop.alphaRename(definiens_prop)
     val new_definiens2 = Prop.replaceLst(actual_arg_vars,new_arg_vars_as_terms,new_definiens)
     fun introMethod(arg_vals:Semantics.value list,env,ab) = 
       let val right_length = length(arg_vars)
           val actual_len = length(arg_vals)
           fun termIntro() = 
                 let val _ = if not(actual_len = right_length) then
                                primError("Wrong number of arguments ("^Int.toString(actual_len)^") \ngiven to "^
                                          intro_method_name^"---it requires exactly "^Int.toString(right_length)^
                                          " arguments")
                             else ()
                     val terms = getTermsNoPos(arg_vals,intro_method_name) 
                     val term_vars = AthTerm.getVarsLst(terms)
                     val instantiated_definiens = Prop.replaceLst(new_arg_vars,terms,new_definiens2)
                 in
                    if ABase.isMember(instantiated_definiens,ab) then
                       Semantics.propVal(Prop.makeAtom(AthTerm.makeApp(sym_name,terms)))
                    else
                       primError(intro_method_name^" requires the sentence\n"^
                                 pprint(0,instantiated_definiens)^"\nto be in the assumption base")
                 end
           fun premiseIntro(premise) = 
                 let val _ = (debugPrint("\nnew_definiens2: ");debugPrint(pprint(0,new_definiens2)))
                     val terms = (case Prop.matchRW(premise,new_definiens2,new_arg_vars) of
                                    SOME(sub) => map (fn v => let val t = AT.applySub(sub,AT.makeVar(v))
                                                                  val _ = debugPrint("\nThe matching sub maps variable "^(ATV.toStringDefault(v))^" to: "^
                                                                                     (AT.toStringDefault(t)))
                                                               in t end) new_arg_vars 
                                  | _ => primError("incorrect use of "^(intro_method_name)^": the given sentence\ndoes not match the definiens of "^sym_name_str
                                                 ))
                     val instantiated_definiens = Prop.replaceLst(new_arg_vars,terms,new_definiens2)
                     val _ = (debugPrint("\nactual_arg_vars: ");debugPrint(Basic.printListStrCommas(actual_arg_vars,fn v => ATV.toPrettyStringDefault(0,v))))
                     val _ = (debugPrint("\ninstantinated definiens:\n");debugPrint(pprint(0,instantiated_definiens)))
                 in
                    if ABase.isMember(instantiated_definiens,ab) then
                       Semantics.propVal(Prop.makeAtom(AthTerm.makeApp(sym_name,terms)))
                    else
                       primError(intro_method_name^" requires the sentence\n"^
                                 pprint(0,instantiated_definiens)^"\nto be in the assumption base"
                                )
                 end
       in
          if actual_len = 1 then
              ((case (Semantics.getProps(arg_vals,"the argument list given to "^intro_method_name,env) 
                      handle _ => [])
                of
                   [premise] => (premiseIntro(premise) handle Semantics.EvalError(msg,pos_opt) => 
                                                                (termIntro() handle _ => raise Semantics.EvalError(msg,pos_opt)))
                 | _ => termIntro()))
          else termIntro()
       end
     fun elimMethod(arg_vals,env,ab) =        
         let  val actual_len = length(arg_vals)
              fun termElim() = 
                let val right_length = length(arg_vars)
                    val _ = if not(actual_len = right_length) then
                              primError("Wrong number of arguments ("^Int.toString(actual_len)^") given to "^
                                       "the method "^elim_method_name^"---it requires exactly "^Int.toString(right_length)^
                                       " arguments")
                            else ()
                    val terms = getTermsNoPos(arg_vals,elim_method_name) 
                    val relation_holds = Prop.makeAtom(AthTerm.makeApp(sym_name,terms))
                in
                     if ABase.isMember(relation_holds,ab) then
                          let val term_vars = AthTerm.getVarsLst(terms)
                               val actual_arg_var_opts = map (fn v => Basic.findInList(Prop.freeVars(definiens_prop),
                                                                                       fn v' => ATV.nameEq(v,v')))
                                                         arg_vars
                                val actual_arg_vars = map (fn opt => (case opt of
                              			                     SOME(v) => v
                                                             | _ => ATV.fresh())) actual_arg_var_opts
                                val new_arg_vars = map (fn actual_arg_var => ATV.freshWithSort(ATV.getSort(actual_arg_var))) actual_arg_vars
                                val new_arg_vars_as_terms = map AthTerm.makeVar new_arg_vars
                                val new_definiens = Prop.alphaRename(definiens_prop)
                                val new_definiens2 = Prop.replaceLst(actual_arg_vars,new_arg_vars_as_terms,new_definiens)
                                val conclusion = Prop.replaceLst(new_arg_vars,terms,new_definiens2)
                                in
                                   Semantics.propVal(conclusion)
                                end
                     else primError(elim_method_name^" requires the sentence\n"^
                                    pprint(0,relation_holds)^"\nto be in the assumption base")
                end
              fun premiseElim(premise) = 
                      let val actual_arg_var_opts = map (fn v => Basic.findInList(Prop.freeVars(definiens_prop),
                                                                  fn v' => ATV.nameEq(v,v')))
                                                    arg_vars
                           val actual_arg_vars = map (fn opt => (case opt of
                           			                     SOME(v) => v
                                                             | _ => ATV.fresh())) actual_arg_var_opts
                           val new_arg_vars = map (fn actual_arg_var => ATV.freshWithSort(ATV.getSort(actual_arg_var))) actual_arg_vars
                           val new_arg_vars_as_terms = map AthTerm.makeVar new_arg_vars
                           val new_definiendum = Prop.makeAtom(AthTerm.makeApp(sym_name,new_arg_vars_as_terms))
                           val new_definiens = Prop.alphaRename(definiens_prop)
                           val new_definiens2 = Prop.replaceLst(actual_arg_vars,new_arg_vars_as_terms,new_definiens)
                           val terms = (case Prop.matchRW(premise,new_definiendum,new_arg_vars) of
                                          SOME(sub) => map (fn v => let val t = AT.applySub(sub,AT.makeVar(v))
                                                                        val _ = debugPrint("\nThe matching sub maps variable "^(ATV.toStringDefault(v))^" to: "^
                                                                                          (AT.toStringDefault(t)))
                                                                    in t end) new_arg_vars 
                                        | _ => primError("incorrect use of "^(elim_method_name)^": the given sentence\n"^
                                                       "does not match the definiendum of "^sym_name_str
                                                       ))
                            val term_vars = AthTerm.getVarsLst(terms)
                            val relation_holds = Prop.makeAtom(AthTerm.makeApp(sym_name,terms))
                            val conclusion = Prop.replaceLst(new_arg_vars,terms,new_definiens2)
                      in
                         if ABase.isMember(relation_holds,ab) then Semantics.propVal(conclusion)
                         else primError(elim_method_name^" requires the sentence\n"^
                                        pprint(0,relation_holds)^"\nto be in the assumption base")
                      end
         in
             if actual_len = 1 then
                ((case (Semantics.getProps(arg_vals,"the argument list given to "^elim_method_name,env) 
                        handle _ => [])
                  of
                     [premise] => (premiseElim(premise) handle Semantics.EvalError(msg,pos_opt) => 
		     	       	  			         (termElim() handle _ => raise Semantics.EvalError(msg,pos_opt)))
                   | _ => termElim()))
             else termElim() 
         end 
     in 
       (Semantics.updateTopValEnv(env,Symbol.symbol(intro_method_name),
                               Semantics.methodVal(introMethod,S.symbol intro_method_name),false);
        Semantics.updateTopValEnv(env,Symbol.symbol(elim_method_name),Semantics.methodVal(elimMethod,S.symbol(elim_method_name)),false);
        Semantics.updateTopValEnv(eval_env,Symbol.symbol(intro_method_name),
                               Semantics.methodVal(introMethod,S.symbol intro_method_name),false);
        Semantics.updateTopValEnv(eval_env,Symbol.symbol(elim_method_name),Semantics.methodVal(elimMethod,S.symbol(elim_method_name)),false))
 end

fun makeFunDefMethod(fun_name,arg_vars,eq_var,definiens_prop,env,eval_env,pos,is_poly) = 
 let val method_name = "apply"^MS.name(fun_name)^"-definition"
     fun defMethod(arg_vals,env,ab) = 
         let val right_length = length(arg_vars)  
             val actual_len = length(arg_vals)
             val _ = if not(actual_len = right_length) then
                        primError("Wrong number of arguments ("^Int.toString(actual_len)^") given to "^
                                  "the method "^method_name^"---it requires exactly "^Int.toString(right_length)^
                                  " arguments")
                     else ()
             val terms = getTermsNoPos(arg_vals,method_name) 
             val term_vars = AthTerm.getVarsLst(terms)
             val new_eq_var_and_arg_vars = (AthTermVar.fresh())::(AthTermVar.freshLst(arg_vars))
             val new_definiens = Prop.alphaRename(definiens_prop)
             val new_vars_as_terms = map AthTerm.makeVar new_eq_var_and_arg_vars
             val new_definiens2 = Prop.replaceLst(eq_var::arg_vars,new_vars_as_terms,new_definiens)
             val eq_var_replacement = AthTerm.makeApp(fun_name,terms)
             val instantiated_fun_definiens = Prop.replaceLst(new_eq_var_and_arg_vars,
                                                              eq_var_replacement::terms,
                                                              new_definiens2)
             in
                Semantics.propVal(instantiated_fun_definiens)
         end
     in
        (Semantics.updateTopValEnv(env,Symbol.symbol(method_name),Semantics.methodVal(defMethod,S.symbol method_name),false);
         Semantics.updateTopValEnv(eval_env,Symbol.symbol(method_name),Semantics.methodVal(defMethod,S.symbol method_name),false))
 end

fun makeConstantDefMethod(constant_name,eq_var,definiens_prop,env,eval_env,pos) = 
 let val method_name = "apply"^MS.name(constant_name)^"-definition"
     fun defMethod(arg_vals,env,ab) = 
         let val actual_len = length(arg_vals)
             val _ = if not(actual_len = 0) then
                        primError("Wrong number of arguments ("^Int.toString(actual_len)^") given to "^
                                  "the method "^method_name^"---it requires exactly zero arguments"
                                 )
                     else ()
             val eq_var_replacement = AthTerm.makeConstant(constant_name)
             val instantiated_definiens = Prop.replace(eq_var,eq_var_replacement,definiens_prop)
             in
                Semantics.propVal(instantiated_definiens)
         end
     in
        (Semantics.updateTopValEnv(env,Symbol.symbol(method_name),Semantics.methodVal(defMethod,S.symbol method_name),false);
         Semantics.updateTopValEnv(eval_env,Symbol.symbol(method_name),Semantics.methodVal(defMethod,S.symbol method_name),false))
 end

fun showVars([]) = ()
  | showVars(vars::rest) = (List.app (fn v => (print(ATV.toPrettyString(0,v,F.varToString));print("\n"))) vars;
			    if null(rest) then print("\n") else print("\nand\n");
			    showVars(rest))


val makePrivate = Semantics.makePrivate
val makePrivateLst = Semantics.makePrivateLst

fun processSymbolDefinition({name=sym_name,condition,pos,abbreviated}:A.absyn_symbol_definition,fids,mod_path,env,eval_env) = 
         (** The function legalDefCond below simply ensures that only term 
             constructors and sentence builders occur in the defining "condition".
             Note, in particular, that the newly defined symbol canNOT appear in the
             defining condition. Thus, recursive symbol definitions are, for now at least,
             not allowed. **)
     let val full_sym_name = qualifyName(sym_name,mod_path)
         fun legalDefCond(A.idExp({msym,...})) = isTermConstructorBool(msym) orelse MS.modSymEq(msym,full_sym_name)
           | legalDefCond(A.propConExp(_)) = true
           | legalDefCond(A.numExp(_)) = true
             | legalDefCond(A.quotedIdeExp(_)) = true
           | legalDefCond(A.termVarExp(_)) = true
           | legalDefCond(A.appExp({proc=A.exp(A.numExp(_)),args=[],...})) = true
           | legalDefCond(A.appExp({proc=A.exp(A.quotedIdeExp(_)),args=[],...})) = true
           | legalDefCond(A.appExp({proc=A.exp(A.idExp({msym,pos,...})),args,...})) =
               (A.isPropConMS(msym) orelse isTermConstructorBool(msym) orelse MS.modSymEq(msym,full_sym_name))
	       andalso Basic.forall(args,legalDefPhrase)
           | legalDefCond(A.appExp({proc=A.exp(A.propConExp(_)),args,...})) = Basic.forall(args,legalDefPhrase)
           | legalDefCond(_) = false
         and 
             legalDefPhrase(A.exp(e)) = legalDefCond(e)
           | legalDefPhrase(A.ded(_)) = false
         fun evaluateExp(e) = let val ip = infixProcess(A.exp e,eval_env,fids)
                                  val fids = MS.add(Names.mite_symbol,fids)
                              in  
                                 evalPhrase((ip,fids),eval_env,!top_assum_base)
                              end
         fun undoBindings(old_env,old_eval_env,new_fsym) = 
             (eval_env := old_eval_env;
              env := old_env; 
              Data.removeFSym(new_fsym))
         fun isSentCon(iexp,sent_con) = ((case evaluateExp(iexp) of
                                            SemanticValues.propConVal(pc) => pc = sent_con 
                                          | _ => false) handle _ => false)
         fun isAnySentCon(iexp) = ((case evaluateExp(iexp) of
                                    SemanticValues.propConVal(_) => true
                                          | _ => false) handle _ => false)
         fun error() = evError("Ill-formed symbol definition",SOME(pos))
         fun checkDistinct([]) = ()
           | checkDistinct(v::more_vars) = 
                if Basic.isMemberEq(v,more_vars,AthTermVar.nameEq) then
                   evError("Duplicate bound variable: "^(Names.variable_prefix)^(AthTermVar.name v)^"---all\n"^
                           "bound variables must be distinct in a symbol definition",NONE)
                else checkDistinct(more_vars)
         fun checkDistinctVars([],_) = ()
           | checkDistinctVars(v::more_vars,pos::more_pos) = 
                    if Basic.isMemberEq(v,more_vars,AthTermVar.athTermVarEq) then
                       evError("Duplicate variable: "^AthTermVar.name(v)^"---all the "^
                               "variables must be distinct in a symbol definition",SOME(pos))
                    else
                       checkDistinctVars(more_vars,more_pos)
           | checkDistinctVars(_) = raise Basic.Never 
         val flag = ref false 
         fun analyze(e as A.appExp({proc=A.exp(A.idExp({msym=faname,...})),
                                    args,...})) = 
               let fun getVars([],vars) = (rev vars,[])
                     | getVars((A.exp(A.termVarExp({term_var,...})))::rest,vars) = getVars(rest,term_var::vars)
                     | getVars(L as (A.exp(A.idExp({msym=id_name,...}))::rest),vars) = 
                               if MS.name(id_name) = "." then (rev vars,rest)
                               else (rev vars,L)
                     | getVars(L as (_::rest),vars) = (rev vars,L)
                   fun split(e as A.appExp({proc=A.exp(A.idExp({msym=name,...})),args,...}),vars) = 
			if MS.modSymEq(name,Names.mforall_symbol) then
		           let val (var_args,body_exps) = getVars(args,[])
                               val body = (case body_exps of
                                             [A.exp(first as (A.appExp(_)))] => first 
                                           | first::more => A.appExp({proc=first,args=more,alt_exp=ref(NONE),pos=A.posOfPhrase(first)})
                                           | _ => (evError("Ill-formed symbol definition",SOME(pos))))
                            in 
			       split(body,vars@var_args)
                            end
                         else (vars,e)
                     | split(b,vars) = (vars,b)
                   val (quant_vars,body) = split(e,[])
                   fun shrink(args) = (case args of
                                         [A.exp(e)] => e
                                       | p1::(more as p2::_) => A.appExp({proc=p1,args=more,alt_exp=ref(NONE),pos=A.posOfPhrase(p1)})
                                       | _ => error())
                   fun hasSententialConstructors(A.exp(iexp as A.idExp(_))) = isAnySentCon(iexp)
                     | hasSententialConstructors(A.exp(A.appExp({args,...}))) = Basic.exists(args,hasSententialConstructors)
                     | hasSententialConstructors(_) = false 
                   fun isFunctional(A.appExp({proc=A.exp(A.idExp({msym,...})),args=[_,_],...})) = MS.modSymEq(msym,Names.mequal_logical_symbol)
                     | isFunctional(_) = false 
                   fun makeRelational1(A.appExp({args=[A.exp e1,_],...})) = e1
                     | makeRelational1(e) = e 
                   fun makeRelational2(A.appExp({args=[_,A.exp e2],...})) = e2
                     | makeRelational2(e) = e 
                   in
		     if MS.modSymEq(faname,Names.mforall_symbol) then
                     (case body of
                         A.appExp({proc=A.exp(A.idExp({msym=iname,...})),
                            args=[A.exp(e1),A.exp(e2)],...}) => 
                              if MS.modSymEq(iname,Names.miff_symbol) then 
                                 (let val (c1,c2) = (hasSententialConstructors(A.exp e2),isFunctional(e1))
                                      val (e1',e2') = (makeRelational1 e1,makeRelational2 e2)
                                  in
                                     if c1 andalso c2 andalso abbreviated then 
                                         (flag := true;(quant_vars,e1',e2'))
                                     else (quant_vars,e1,e2)
                                  end)
			      else error()
                       | A.appExp({proc=e1 as A.exp(A.termVarExp(_)),args,...}) =>
                             (case args of
                                ((real_proc as A.exp(A.idExp({msym=name1,...})))::
                                 (e2 as A.exp(A.termVarExp(_)))::
                                 (e3 as A.exp(iexp_0 as (A.idExp({msym=eq_name,...}))))::
                                 (e4 as A.exp(A.termVarExp(_)))::
                                 (e5 as A.exp((iexp as A.idExp({msym=iname,...}))))::rest)
                                     => (if isSentCon(iexp_0,A.iffCon) then 
                                            let val first_exp = A.appExp({proc=real_proc,args=[e1,e2],alt_exp=ref(NONE),pos=A.posOfPhrase(real_proc)})
                                                val second_exp = shrink(e4::e5::rest)
                                            in
                                               (quant_vars,first_exp,second_exp)
                                            end
                                         else 
                                         (if MS.modSymEq(eq_name,Names.mequal_logical_symbol) andalso MS.modSymEq(name1,full_sym_name) andalso isSentCon(iexp,A.iffCon)  then 
                                          let val first_exp = A.appExp({proc=e3,args=[A.exp(A.appExp({proc=real_proc,args=[e1,e2],alt_exp=ref(NONE),
                                                                                    pos=A.posOfPhrase(real_proc)})),
                                                                                    e4],alt_exp=ref(NONE),pos=A.posOfPhrase(e3)
                                                                                    })
                                              val second_exp = shrink(rest)  
                                          in
                                             (quant_vars,first_exp,second_exp)
                                          end 
                                         else (error())))
                             | ((real_proc as A.exp(A.idExp({msym=name1,...})))::
                                 (e2 as A.exp(A.termVarExp(_)))::
                                 (e3 as A.exp((iexp as A.idExp({msym=iname,...}))))::rest)
                                 =>  if MS.modSymEq(name1,full_sym_name) andalso isSentCon(iexp,A.iffCon)  then 
                                         let val first_exp = A.appExp({proc=real_proc,args=[e1,e2],alt_exp=ref(NONE),
                                                                                   pos=A.posOfPhrase(real_proc)})
                                             val second_exp = shrink(rest)  
                                         in
                                            (quant_vars,first_exp,second_exp)
                                         end 
                                        else error())
                       | A.appExp({proc=A.exp(first as A.appExp(_)),
                                              args=(A.exp(A.idExp({msym=iname,...})))::rest_args,...}) =>
                              if not(MS.modSymEq(iname,Names.miff_symbol)) then 
                                 let val second_exp = shrink(rest_args)
                                     val first_exp = (case first of 
                                                        A.appExp({proc=e1 as A.exp(A.termVarExp(_)),args,...}) =>
                                                          (case args of
                                                              [real_proc as A.exp(A.idExp({msym=name1,...})),
                                                               e2 as A.exp(A.termVarExp(_))]
                                                             => if MS.modSymEq(name1,full_sym_name) then 
                                                                   A.appExp({proc=real_proc,args=[e1,e2],alt_exp=ref(NONE),pos=A.posOfExp(first)})
                                                                else (error())
                                                           | [real_proc as A.exp(A.idExp({msym=name1,...})),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     e2 as A.exp(A.termVarExp(_)), 
                                                              e3 as A.exp(A.idExp({msym=eq_name,...})),
                                                              e4 as A.exp(A.termVarExp(_))] 
                                                             => if MS.modSymEq(eq_name,Names.mequal_logical_symbol) andalso
                                                                   MS.modSymEq(name1,full_sym_name)
                                                                then 
                                                                    A.appExp({proc=e3,args=[A.exp(A.appExp({proc=real_proc,
                                                                                                            args=[e1,e2],alt_exp=ref(NONE),
                                                                                                            pos=A.posOfPhrase(real_proc)})),
                                                                                            e4],alt_exp=ref(NONE),pos=A.posOfPhrase(e3)})
                                                                else (error()))
                                                      | A.appExp({proc=A.exp(A.idExp({msym,...})),args,...}) => 
                                                          if MS.modSymEq(msym,full_sym_name) then first
                                                          else (error())
                                                      | _ => error())
                                 in
                                    (quant_vars,first_exp,second_exp)
                                 end
			      else (evError("Ill-formed symbol definition",SOME(pos)))
                       | _ => (evError("Ill-formed symbol definition",SOME(pos))))
		     else (evError("Ill-formed symbol definition",SOME(pos)))
               end
           | analyze(_) = (evError("Ill-formed symbol definition",SOME(pos)))
         datatype symbol_type = newConstant of {eq_var:AthTermVar.ath_term_var}
                              | newOperator of {arity:int,arg_vars:AthTermVar.ath_term_var list,
                                                arg_var_positions: A.position list,
                                                eq_var:AthTermVar.ath_term_var,eq_var_pos:A.position}
                              | newRelation of {arity:int,arg_vars:AthTermVar.ath_term_var list,
                                                arg_var_positions: A.position list}
         fun doEq([A.idExp({msym,...}),A.termVarExp({term_var,...})]) = 
                   if MS.modSymEq(msym,full_sym_name) then
                      newConstant({eq_var=term_var})
                   else evError("Ill-formed symbol definition",SOME(pos))
           | doEq([e1 as A.termVarExp({term_var,...}),e2 as A.idExp({msym,...})]) = doEq([e2,e1])
           | doEq([A.appExp({proc=A.exp(A.idExp({msym=name,...})),args,...}),A.termVarExp({term_var,pos=tv_pos,...})]) = 
                  if MS.modSymEq(name,full_sym_name) then 
                     let fun f([],var_lst,pos_lst) = (rev(var_lst),rev(pos_lst))
                           | f(A.exp(A.termVarExp({term_var,pos,...}))::more,var_lst,pos_lst) = 
                                     f(more,term_var::var_lst,pos::pos_lst)
                           | f(_) = evError("Ill-formed symbol definition",SOME(pos))
                         val (vars,pos_lst) = f(args,[],[])
                     in 
                        newOperator({arity=length(args),arg_vars=vars,arg_var_positions=pos_lst,
                                     eq_var=term_var,eq_var_pos=tv_pos})
                     end
                  else
                     evError("Ill-formed symbol definition",SOME(pos))
           | doEq([e1 as A.termVarExp({term_var,...}),e2 as A.appExp({proc=A.exp(A.idExp(name)),args,...})]) = 
                  doEq([e2,e1])
           | doEq(_) = evError("Ill-formed symbol definition",SOME(pos));
         fun analyzeDefiniendum(A.appExp({proc=A.exp(A.idExp({msym=name,...})),args,...})) = 
             if MS.modSymEq(name,full_sym_name) then
                let fun f([],var_lst,pos_lst) = (rev(var_lst),rev(pos_lst))
                      | f(A.exp(A.termVarExp({term_var,pos,...}))::more,var_lst,pos_lst) = 
                                   f(more,term_var::var_lst,pos::pos_lst)
                      | f(_) = evError("Ill-formed symbol definition",SOME(pos))
                    val (vars,pos_lst) = f(args,[],[])
                in
                    newRelation({arity=length(args),arg_vars=vars,arg_var_positions=pos_lst})
                end
             else
                if  MS.modSymEq(name,Names.mequal_logical_symbol) then
                    doEq(List.map (fn A.exp(e) => e | _ => 
                              evError("Ill-formed symbol definition",SOME(pos))) args)
                else
                    evError("Ill-formed symbol definition",SOME(pos))
           | analyzeDefiniendum(_) = evError("Ill-formed symbol definition",SOME(pos));
         fun makeUniqProp(arg_vars,eq_var,body) = 
             let fun makeProp([],p) = p 
                   | makeProp(v::more,p) = makeProp(more,Prop.makeUGen([v],p))
                 in
                   makeProp(rev(arg_vars),Prop.makeEGenUnique([eq_var],body))
             end;
         fun subsetVars(vars1,vars2) = 
             List.all (fn v => Basic.isMemberEq(v,vars2,AthTermVar.nameEq)) vars1
         fun checkSubsetVars(vars1,vars2) = 
                if subsetVars(vars1,vars2) then ()
                else
                evError("Definiendum variable is not universally quantified",SOME(pos));
         val (init_quant_vars,definiendum,definiens) = analyze(condition) 
         fun makeCondition(vars,left,right) = A.makeUnProp(vars,A.appExp({proc=A.exp(A.idExp({msym=N.miff_symbol,mods=[],no_mods=true,sym=N.iff_symbol,pos=dum_pos})),
                                                                          args=[A.exp(left),A.exp(right)],alt_exp=ref(NONE),pos=dum_pos}))

         fun leftArg(A.appExp({args,...})) = hd(args)
         fun rightArg(A.appExp({args,...})) = hd(tl(args))
         fun makeCondition(vars,left,right) = 
              A.makeUnProp(vars,A.appExp({proc=A.exp(A.idExp({msym=N.mequal_logical_symbol,mods=[],no_mods=true,sym=N.equal_logical_symbol,pos=dum_pos})),
                                          args=[leftArg(left),rightArg(right)],alt_exp=ref(NONE),pos=dum_pos}))

         val init_quant_vars = if !flag then rev(List.drop(rev init_quant_vars,1)) else init_quant_vars
         val condition = if !flag then makeCondition(rev init_quant_vars,definiendum,definiens) else condition 
         val _ = checkSubsetVars(A.getExpVars(definiendum),init_quant_vars)
         val _ = checkStrucConOrFSymRedef(full_sym_name,pos)
         val _ = checkNewFunSym(sym_name,pos) 
         val definiens_prop_val = let val ip = infixProcess(A.exp definiens,eval_env,fids)
                                      val fids = MS.add(Names.mite_symbol,fids)
                                  in
                                    evalPhrase((ip,fids),eval_env,!top_assum_base) handle _ => error()
                                  end 
         in                 
            (case analyzeDefiniendum(definiendum) of
                newRelation({arity,arg_vars,arg_var_positions}) => 
                   let val _ = checkDistinctVars(arg_vars,arg_var_positions)
                       val _ = checkSubsetVars(arg_vars,init_quant_vars)
                       val _ = if subsetVars(init_quant_vars,arg_vars) then ()
                               else evError("Extraneous variable is universally quantified "^ 
                                            "in definition header",SOME(pos))
                       in
                         (case Semantics.coerceValIntoPropVal(definiens_prop_val) of
                            SOME(Semantics.propVal(definiens_prop)) => 
				 
                              let val definiens_fvars = Prop.freeVars(definiens_prop)
				  val _ = if subsetVars(definiens_fvars,arg_vars)
                                          then () else
                                          evError("Definiens has extraneous free variable",SOME(pos))
				  val eq_v_opts = map (fn v => Basic.findInList(Prop.freeVars(definiens_prop),
						   	          fn v' => ATV.nameEq(v,v'))) arg_vars 
				  val var_types = map (fn eo => (case eo of
  						          SOME(ev) => ATV.getSort(ev)
						        | _ => F.makeFreshVar())) eq_v_opts 
                                  val is_poly = List.exists (fn t => not(FTerm.isGround(t))) var_types

                                  val involves_pred_based_sorts = F.findOutDynamicallyIfAnySortsHavePredicateBasedSortSymbols(var_types)

                                  val new_fsym = defined({name=full_sym_name,argument_types=var_types,assoc=ref(NONE),arity=arity,
                                                          bits=makeWord({poly=is_poly,pred_based_sig=involves_pred_based_sorts}),
                                                          prec=ref(Options.standard_bool_symbol_precedence),
                                                          range_type=boolean_object_type})
                                  val _ = addFSym(new_fsym)
                                  val old_eval_env = !eval_env
                                  val old_env = !env
                                  val fsymTermConstructorVal = Semantics.makeTermConVal(SV.regFSym(new_fsym))
                                  val _ =  Semantics.updateTopValEnv(env,sym_name,fsymTermConstructorVal,false)
                                  val _ =  Semantics.updateTopValEnv(eval_env,sym_name,fsymTermConstructorVal,false)

                                  val whole_prop_val = let val ip = infixProcess(A.exp condition,eval_env,fids)
                                                           val fids = MS.add(Names.mite_symbol,fids)
                                                       in 
                                                          evalPhrase((ip,fids),eval_env,!top_assum_base)
                                                       end
                                  val whole_prop = (case whole_prop_val of 
                                                       Semantics.propVal(p) => p | _ => raise Basic.Never)
                                  val _ = let val bvars = P.boundVars(whole_prop)
                                          in
                                             (checkDistinct bvars) handle ex => (undoBindings(old_env,old_eval_env,new_fsym);raise ex)
                                          end
                                  val _ = makeIntroElimMethods(full_sym_name,arg_vars,definiens_prop,env,eval_env,is_poly)
                                  val def_name_str = (Symbol.name sym_name)^"-definition"
                                  val def_name = Symbol.symbol(def_name_str)
                                  val _ = Semantics.updateTopValEnv(env,def_name,Semantics.propVal(whole_prop),false);
                                  val _ = Semantics.updateTopValEnv(eval_env,def_name,Semantics.propVal(whole_prop),false);

                                  val process = (!Semantics.processString)
                                  val proc_str = Semantics.getSafeName("get-defined-prop")
                                  val cmd = "(define " ^ def_name_str ^ " (" ^ proc_str ^ " " ^ def_name_str ^ "))"
                                  val _ = process(cmd,mod_path,env,eval_env)
                                  val _ = (top_assum_base := ABase.augment(!top_assum_base,[whole_prop]);
                                           top_assum_base := ABase.addAssertion(whole_prop,!top_assum_base);
                                           addFSymDefInfoAndCompile(whole_prop,env,eval_env,mod_path,false,false,pos,[],NONE))
                                  val _ = makePrivateLst([def_name_str])
                                  in
                                     (myPrint("\nNew symbol defined, "^Symbol.name(sym_name)^
                                            ": "^printFunType(var_types,boolean_object_type)^".\n");
                                      myPrint("\nThe following now holds: \n"^pprint(0,whole_prop)^"\n"))
                              end
                          | _ => evError("Definiens must be a sentence",SOME(pos)))
                   end    
              | newOperator({arity,arg_vars,arg_var_positions,eq_var,eq_var_pos}) => 
                   let val _ = checkDistinctVars(eq_var::arg_vars,eq_var_pos::arg_var_positions)
                       val _ = checkSubsetVars(arg_vars,init_quant_vars)
                       val _ = if subsetVars(init_quant_vars,eq_var::arg_vars) then ()
                               else evError("Extraneous variable universally quantified "^
                                            "in definition header",SOME(pos))
                       fun isVar(t) = (case AthTerm.isVarOpt(t) of NONE => false | _ => true)
                       fun trivialFunDef(eq_var,P) =
                        (case Prop.isAtom(P) of 
			   SOME(t) =>
                           (case AthTerm.isApp(t) of
                               SOME(fsym,[t1,t2]) => 
                                  if MS.modSymEq(fsym,Names.mequal_logical_symbol) then
                                     (case AthTerm.isVarOpt(t1) of 
                                        SOME(v) => let val cond1 = AthTermVar.nameEq(v,eq_var)                                                       
                                                       val cond2 = not(isVar(t2))
                                                   in 
                                                      cond1 andalso cond2
                                                   end
                                      | _ => let val _ = ()
                                             in
                                                (case AthTerm.isVarOpt(t2) of 
                                                    SOME(v) => AthTermVar.athTermVarEq(v,eq_var) andalso not(isVar(t1)) 
                                               | _ => false)
                                             end)
                                  else false
                             | _ => false)
                           | _ => false)
                       in
                         (case Semantics.coerceValIntoPropVal(definiens_prop_val) of
                            SOME(Semantics.propVal(definiens_prop)) => 
                              let val _ = if subsetVars(Prop.freeVars(definiens_prop),eq_var::arg_vars)
                                          then () else
                                          evError("Definiens has extraneous free variable",SOME(pos))
                                  val uniqueness_cond = makeUniqProp(arg_vars,eq_var,definiens_prop)
                                  val is_trivial = trivialFunDef(eq_var,definiens_prop)
                                  val all_vars = eq_var::arg_vars
				  val eq_v_opts = map (fn v => Basic.findInList(Prop.freeVars(definiens_prop),
						   	          fn v' => ATV.nameEq(v,v'))) all_vars 
				  val var_types = map (fn eo => (case eo of
  					 	                    SOME(ev) => ATV.getSort(ev)
 						                  | _ => F.makeFreshVar()))
                                                      eq_v_opts
                                  val (arg_types,ran_type) = (tl(var_types),hd(var_types))
                                  val all_types = (ran_type::arg_types)
                                  val is_poly = List.exists (fn t => not(FTerm.isGround(t)))
                                                            all_types
                                  val involves_pred_based_sorts = F.findOutDynamicallyIfAnySortsHavePredicateBasedSortSymbols(all_types)
                                  val _ = if is_poly andalso (List.exists (fn v => not (List.exists (fn t => FTerm.varOccursIn(v,t)) arg_types))
                                                                          (FTerm.getVars(ran_type)))
                                          then evError("The output sort contains sort variables\nthat do not appear in any input sort",SOME(pos)) 
                                          else ()
                                  val _ = makeFunDefMethod(full_sym_name,arg_vars,eq_var,definiens_prop,env,eval_env,pos,is_poly)
                                  val new_fsym = defined({name=full_sym_name,bits=makeWord({poly=is_poly,pred_based_sig=involves_pred_based_sorts}),
                                                          arity=arity,assoc=ref(NONE),
                                                          argument_types=arg_types,prec=ref(Options.defaultPrec(arity)),
                                                          range_type=ran_type})
                                  val _ = addFSym(new_fsym)
                                  val fsymTermConstructorVal = Semantics.makeTermConVal(SV.regFSym(new_fsym))
                                  val old_eval_env = !eval_env
                                  val old_env = !env
                                  val _ =  Semantics.updateTopValEnv(env,sym_name,fsymTermConstructorVal,false)
                                  val _ =  Semantics.updateTopValEnv(eval_env,sym_name,fsymTermConstructorVal,false)
                                  val whole_prop_val = let val ip = infixProcess(A.exp condition,eval_env,fids) 
                                                               val fids = MS.add(Names.mite_symbol,fids)
                                                       in evalPhrase((ip,fids),eval_env,!top_assum_base) end 
                                  val whole_prop = (case whole_prop_val of 
                                                       Semantics.propVal(p) => p | _ => raise Basic.Never)
                                  val _ = let val bvars = P.boundVars(whole_prop)
                                          in
                                             (checkDistinct bvars) handle ex => (undoBindings(old_env,old_eval_env,new_fsym);raise ex)
                                          end
                                  val _ = if ABase.isMember(uniqueness_cond,!top_assum_base) 
                                             orelse is_trivial
                                          then ()
                                          else 
                                            (undoBindings(old_env,old_eval_env,new_fsym);
                                             evError("The following uniqueness condition\nmust obtain "^
                                                    "for this function definition to be admissible:\n"^
                                                    Prop.toPrettyString(0,uniqueness_cond,F.makeVarSortPrinter()),
						    SOME(pos)))

                                  val def_name_str = (Symbol.name sym_name)^"-definition"
                                  val def_name = Symbol.symbol(def_name_str)
                                  val _ = Semantics.updateTopValEnv(env,def_name,Semantics.propVal(whole_prop),false);
                                  val _ = Semantics.updateTopValEnv(eval_env,def_name,Semantics.propVal(whole_prop),false);
                                  val process = (!Semantics.processString)
                                  val proc_str = Semantics.getSafeName("get-defined-prop")
                                  val cmd = "(define " ^ def_name_str ^ " (" ^ proc_str ^ " " ^ def_name_str ^ "))"
                                  val whole_prop_val' = (process(cmd,mod_path,env,eval_env);
                                                         ((!Semantics.evaluateStringFlexible) (def_name_str,eval_env))) handle _ => whole_prop_val
                                  val whole_prop' = (case Semantics.coerceValIntoProp(whole_prop_val') of
                                                        SOME(p) => p
                                                      | _ => whole_prop)
                                  val _ = (top_assum_base := ABase.augment(!top_assum_base,[whole_prop']);
                                           top_assum_base := ABase.addAssertion(whole_prop',!top_assum_base);
                                           addFSymDefInfoAndCompile(whole_prop',env,eval_env,mod_path,false,false,pos,[],NONE))
                                  val _ = Semantics.updateTopValEnv(env,def_name,Semantics.propVal(whole_prop'),false);
                                  val _ = Semantics.updateTopValEnv(eval_env,def_name,Semantics.propVal(whole_prop'),false);
                                  val _ = makePrivateLst([def_name_str])
                                  in
                                     (myPrint("\nNew symbol defined, "^Symbol.name(sym_name)^
                                            ": "^printFunType(arg_types,ran_type)^".\n");                                      
                                      myPrint("\nThe following now holds: \n"^pprint(0,whole_prop')^"\n"))
                              end
                          | _ =>  evError("Definiens must be a sentence",SOME(pos)))
                   end
              | newConstant({eq_var}) => 
                   let 
                       val _ = checkSubsetVars([eq_var],init_quant_vars)
                       val _ = if subsetVars(init_quant_vars,[eq_var]) then ()
                               else evError("Extraneous variable universally quantified "^
                                            "in definition header",SOME(pos))
                       in
                         (case Semantics.coerceValIntoPropVal(definiens_prop_val) of
                            SOME(Semantics.propVal(definiens_prop)) => 
                              let val _ = if subsetVars(Prop.freeVars(definiens_prop),[eq_var])
                                          then () else
                                          evError("Definiens has extraneous free variable",SOME(pos))
                                  val uniqueness_cond = makeUniqProp([],eq_var,definiens_prop)
				  val eq_v_opt = Basic.findInList(Prop.freeVars(definiens_prop),
						   	          fn v => ATV.nameEq(v,eq_var))
				  val var_type = (case eq_v_opt of
						     SOME(ev) => ATV.getSort(ev)
						   | _ => F.makeFreshVar())
                                  val var_types = [var_type]
                                  val constant_type = hd(var_types)
                                  val is_poly = not(FTerm.isGround(constant_type))
                                  val involves_pred_based_sorts = F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(constant_type)
                                  val _ = makeConstantDefMethod(full_sym_name,eq_var,definiens_prop,env,eval_env,pos)
                                  val new_fsym = defined({name=full_sym_name,bits=makeWord({poly=is_poly,pred_based_sig=involves_pred_based_sorts}),assoc=ref(NONE),
                                                          argument_types=[],arity=0,prec=ref(0),
                                                          range_type=constant_type})
                                  val _ = addFSym(new_fsym)
                                  val old_eval_env = !eval_env
                                  val old_env = !env
                                  val fsymTermConstructorVal = Semantics.makeTermConVal(SV.regFSym(new_fsym))
                                  val _ =  Semantics.updateTopValEnv(env,sym_name,fsymTermConstructorVal,false)
                                  val _ =  Semantics.updateTopValEnv(eval_env,sym_name,fsymTermConstructorVal,false)
                                  val whole_prop_val = let val ip = infixProcess(A.exp condition,eval_env,fids)
                                                           val fids = MS.add(Names.mite_symbol,fids)
                                                       in evalPhrase((ip,fids),eval_env,!top_assum_base) end
                                  val whole_prop = (case whole_prop_val of 
                                                       Semantics.propVal(p) => p | _ => raise Basic.Never)
                                  val _ = let val bvars = P.boundVars(whole_prop)
                                          in
                                             (checkDistinct bvars) handle ex => (undoBindings(old_env,old_eval_env,new_fsym);raise ex)
                                          end
                                  val _ = if ABase.isMember(uniqueness_cond,!top_assum_base) then ()
                                          else 
                                            (undoBindings(old_env,old_eval_env,new_fsym);
                                             evError("The following uniqueness condition\nmust obtain "^
                                                    "for this constant definition to be admissible:\n"^
                                                    Prop.toPrettyString(0,uniqueness_cond,F.makeVarSortPrinter()),
						    SOME(pos)))
                                  val def_name = Symbol.symbol(Symbol.name(sym_name)^"-definition")
                                  val _ = (Semantics.updateTopValEnv(env,def_name,Semantics.propVal(whole_prop),true))
                                  val _ = (Semantics.updateTopValEnv(eval_env,def_name,Semantics.propVal(whole_prop),true))

                                  val _ = (top_assum_base := ABase.augment(!top_assum_base,[whole_prop]);
                                           top_assum_base := ABase.addAssertion(whole_prop,!top_assum_base);
                                           addFSymDefInfoAndCompile(whole_prop,env,eval_env,mod_path,false,false,pos,[],NONE))
                                  in
                                     (myPrint("\nNew symbol defined, "^Symbol.name(sym_name)^
                                            ": "^Terms.printFTermSExp(constant_type)^".\n");
                                      myPrint("\nThe following now holds: \n"^pprint(0,whole_prop)^"\n"))
                              end
                          | _ =>  evError("Definiens must be a sentence",SOME(pos)))
                   end)
     end

fun setFlag(flag as {name,pos=flag_pos}:AbstractSyntax.param,value as (str,pos)) = 
 let val _ = ()
 in
  if Symbol.symEq(name,Names.print_var_sorts_flag_symbol) then 
     myPrint("\n"^Options.setPrintVarSortsFlag(str,pos)^"\n") else
  if Symbol.symEq(name,Names.print_qvar_sorts_flag_symbol) then 
     myPrint("\n"^Options.setPrintQVarSortsFlag(str,pos)^"\n") else
  if Symbol.symEq(name,Names.debug_mode_flag_symbol) then 
     myPrint("\n"^Options.setDebugModeFlag(str,SOME pos)^"\n") else 
  if Symbol.symEq(name,Names.infix_parsing_flag_symbol) then 
     myPrint("\n"^Options.setInfixParsingFlag(str,pos)^"\n") else 
  if Symbol.symEq(name,Names.infix_app_style_flag_symbol) then 
     myPrint("\n"^Options.setFunctionAppStyleFlag(str,pos)^"\n")  else 
  if Symbol.symEq(name,Names.check_fun_defs_symbol) then 
     myPrint("\n"^Options.setCheckFunAxiomsFlag(str,pos)^"\n") else
  if Symbol.symEq(name,Names.demons_active_flag_symbol) then 
     myPrint("\n"^Options.setDemonsFlag(str,pos)^"\n") else 
  if Symbol.symEq(name,Names.fundef_mlstyle_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.fundef_mlstyle_option,Names.fundef_mlstyle_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.proof_tracking_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.proof_tracking_option,Names.proof_tracking_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.simplify_fun_def_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.fundef_simplifying_option,Names.simplify_fun_def_flag,str,pos)^"\n") else

  if Symbol.name(name) = "compilation" then 
     myPrint("\n"^Options.setBooleanFlag(Options.compilation_on,"compilation",str,pos)^"\n") else

  if Symbol.symEq(name,Names.compile_mode_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.compile_mode_option,Names.compile_mode_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.call_stack_size_limit_flag_symbol) then 
     myPrint("\n"^Options.setIntFlag(Options.call_stack_size,Names.call_stack_size_limit_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.dom_as_dt_default_size_flag_symbol) then 
     myPrint("\n"^Options.setIntFlag(Options.dt_for_dom_default_size,Names.dom_as_dt_default_size_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.explicit_wildcard_patterns_flag_symbol) then 
     myPrint("\n"^Options.setIntFlag(Options.fundef_explicit_wildcard_patterns_option,Names.explicit_wildcard_patterns_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.init_call_stack_chunk_size_flag_symbol) then 
     myPrint("\n"^Options.setIntFlag(Options.first_call_stack_chunk_size_limit,Names.init_call_stack_chunk_size_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.top_call_stack_portion_size_flag_symbol) then 
     myPrint("\n"^Options.setIntFlag(Options.top_call_stack_portion_length,Names.top_call_stack_portion_size_flag,str,pos)^"\n") else

  if Symbol.symEq(name,Names.ATPs_in_chain_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.atps_in_chain_option,Names.ATPs_in_chain_flag,str,pos)^"\n")
  else 

  if Symbol.symEq(name,Names.option_valued_selectors_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.option_valued_selectors_option,Names.option_valued_selectors_flag,str,pos)^"\n")
  else 

  if Symbol.symEq(name,Names.auto_assert_dt_axioms_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.auto_assert_dt_axioms,Names.auto_assert_dt_axioms_flag,str,pos)^"\n")
  else 

  if Symbol.symEq(name,Names.auto_assert_selector_axioms_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.auto_assert_selector_axioms,Names.auto_assert_selector_axioms_flag,str,pos)^"\n")
  else 
  if Symbol.symEq(name,Names.silent_mode_flag_symbol) then 
     myPrint("\n"^Options.setBooleanFlag(Options.silent_mode,Names.silent_mode_flag_name,str,pos)^"\n")
  else myPrint("\n"^(Symbol.name(name))^" is not a flag.\n")
 end

fun checkFunDefPrimBFun(v1,v2,env,_) = 
       (case TopEnv.coerceValIntoTermConVal(v1) of 
          SOME(TopEnv.termConVal(TopEnv.regFSym(some_fsym))) =>
	      (case v2 of 
                 TopEnv.listVal(vals) => 
                    let val props = Semantics.getProps(vals,"the arguments given to "^N.check_fun_def_name,env)
		        val f = Data.fsymName(some_fsym)
			val (error,at_least_one_conditional_equation) = checkFunDef(f,props,NONE)
                    in
		       TopEnv.listVal([TopEnv.MLBoolToAth(error),
		                       TopEnv.MLBoolToAth(at_least_one_conditional_equation)])
                    end
               | _ => TopEnv.primError(TopEnv.wrongArgKind(N.check_fun_def_name,2,TopEnv.listLCType,v2)))
        | _ => TopEnv.primError(TopEnv.wrongArgKind(N.check_fun_def_name,1,TopEnv.termConLCType,v1)));

val _ = TopEnv.updateTopValEnvWithNewPrimBFun(N.check_fun_def_symbol,checkFunDefPrimBFun);

end (** of structure DefinitionProcessor **)
