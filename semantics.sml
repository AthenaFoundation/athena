(*=================================================================================

The implementation of Athena's operational semantics.

In particular, this file contains the definition of the main interpreter/evaluator
functions (evalExp, evalDed, etc.), pattern matching (matchPat), as well as value
equality (valEq), various conversions of values to strings (including pretty printers),
and a lot of auxiliary needed functionality.

=======================================================================*)

structure Semantics = 

struct

open StructureAnalysis

fun makeVarSortPrinter() = F.makeVarSortPrinter()  

val level = ref(0)

fun decrementLevel() = ()

structure SV = SemanticValues

structure MS = ModSymbol

fun msym(s) = ModSymbol.makeModSymbol([],s,s)

open SV

val evaluateString:(string -> value) ref = ref (fn _ => unitVal)
val evaluateStringFlexible:((string * value_environment ref) -> value) ref = ref (fn _ => unitVal)

val processString:((string * (Symbol.symbol list) * value_environment ref * value_environment ref) -> unit) ref = ref (fn _ => ())

val processAlreadParsedInputsRef :((A.user_input list * (Symbol.symbol list) * value_environment ref * value_environment ref) -> unit) ref = ref (fn _ => ())

val (ABaseInsert,ABaseAugment) = (ABase.insert,ABase.augment)

fun putValIntoAB(propVal(P),ab) = ABase.insert(P,ab)
  | putValIntoAB(_,ab) = ab

val getSafeName = Names.getSafeName

exception EvalError of string * (A.position option)
exception PrimError of string
exception AthenaError of string

fun getSameFilePositions(stack) = 
      if null(stack) then stack
      else let val top_pos as (_,{file=top_file,...}) = hd stack 
               fun loop([],res) = rev res
                 | loop((p as (_,{line,pos,file}))::more,res) = 
                        if file = top_file then loop(more,p::res) else rev(res)
           in
              loop(tl stack,[top_pos])
           end

fun builtIn(file) = 
  let val toks = String.tokens (fn c => let val code = Char.ord(c) 
                                        in code = 92 orelse code = 47
                                        end)
                               file
  in
    if null(toks) then false
    else let val name = hd(rev(toks))
         in
           Basic.isMember(name,Names.built_in_file_names)
         end
  end

fun makeErrorWithPosInfo(msg,SOME(pos)) = A.posToString(pos)^": Error: "^msg^"."
  | makeErrorWithPosInfo(msg,_) = msg 

fun evError(msg,pos_opt) = raise EvalError(msg,pos_opt)
fun primError(str) = raise PrimError(str)

fun printStack([]) = ()
  | printStack(p::more) = (print("\nPOSITION:"^(A.posToString(p)));
                           printStack(more))
fun getWord(name) = 
     (case MS.find(StructureAnalysis.constructor_table,name) of
         SOME({bits,...}) => bits
       | _ => (case MS.find(StructureAnalysis.fsym_table,name) of
                  SOME(declared({bits,...})) => bits
                | SOME(defined({bits,...})) => bits
                | _ => evError("Symbol not found: "^MS.name(name),NONE)))

val pprintProp = let val varSortPrinter = makeVarSortPrinter()
		 in
		   fn P => P.toPrettyString(0,P,varSortPrinter)
	 	 end

val propAlphaEq = P.alEq

type pos = A.pos

fun getPos(pos_ar,i) = Array.sub(pos_ar,i)

fun getPosOpt(pos_ar,i) = SOME(getPos(pos_ar,i))

fun warning(msg,pos) = print("\nWarning, "^A.posToString(pos)^": "^msg^".\n")

fun lookUpSym(valEnv({val_map,...}),id) = Symbol.lookUp(val_map,id)

fun lookUpStr(valEnv({val_map,...}),str) = Symbol.lookUp(val_map,Symbol.symbol str)

fun updateValMap(env_ref as ref(valEnv({val_map,mod_map})),global_name,v) = 
      (env_ref := valEnv({val_map = Symbol.enter(val_map,global_name,v),mod_map=mod_map}))

fun updateValMapFunctional(valEnv({val_map,mod_map}),global_name,v) = 
      valEnv({val_map = Symbol.enter(val_map,global_name,v),mod_map=mod_map})

fun nextAvailableEvalProcName(str,eval_env,seed_opt) = 
  let val gsuf = Char.toString(Names.standardEvalProcNameTailCharacter)
      val starting_suffix = Basic.copies(gsuf,1+(!Data.max_prime_suffix))
      val inc_suffix = gsuf
      val seed = (case seed_opt of SOME(w) => w | _ => "")
      fun loop(suffix) = let val str' = str^suffix
                         in 
                           (case (lookUpStr(!eval_env,str'),lookUpStr(!eval_env,Names.standardDeductiveEvalNamePrefix^str')) of
                              (SOME(_),_) => loop(inc_suffix^suffix)
                            | (_,SOME(_)) => loop(inc_suffix^suffix)
                            | _ => if str' = seed then loop(inc_suffix^suffix) else suffix)
                         end
  in 
     str^(loop starting_suffix)
  end

fun nextAvailableReduceProcName(str,eval_env,seed_opt) = 
  let val gsuf = Char.toString(Names.standardReduceProcNameTailCharacter)
      val starting_suffix = Basic.copies(gsuf,1+(!Data.max_prime_suffix))
      val inc_suffix = gsuf
      val seed = (case seed_opt of SOME(w) => w | _ => "")
      fun loop(suffix) = let val str' = str^suffix
                         in 
                           (case lookUpStr(!eval_env,str') of
                              SOME(_) => loop(inc_suffix^suffix)
                            | _ => if str' = seed then loop(inc_suffix^suffix) else suffix)
                         end
  in 
     str^(loop starting_suffix)
  end

fun updateTopValEnv(env,global_name:symbol,value,last_value_binding) =  
     let fun resetName(name) = if !name = "" then name := Symbol.name(global_name) else ()
         val value' = if not(last_value_binding) then
                         (case value of
                            SV.closUFunVal(body,s,env,{prec,name,...}) => resetName(name)
                          | SV.closBFunVal(body,s1,s2,env,{prec,name,assoc,...}) => resetName(name)
                          | SV.closFunVal(body,env,{prec,assoc,name,...}) => resetName(name)
                          | SV.closUMethodVal(body,s,env,name) => resetName(name)
                          | SV.closBMethodVal(body,s1,s2,env,name) => resetName(name)
                          | SV.closMethodVal(A.methodExp({params,body,pos,name,...}),env) => resetName(name)
                          | _ => ())
                      else ()
         val name_str = Symbol.name(global_name)
         val _ = (case Prop.isEvalProcName(name_str) of
                     SOME(f) => let val is_deductive = String.size(name_str) > 0 andalso (String.substring(name_str,0,1) = Names.standardDeductiveEvalNamePrefix)
                                in
                                 (case MS.find(Prop.fsym_def_table,f) of
                                    SOME({eval_proc_name=ep_name,eval_proc_name_with_full_mod_path=ep_name_with_mod_path,
				          evaluator_being_defined=ebd,occurring_syms=osyms,needed_by=nb,
				          obsolete_axioms=obs_axioms,red_code=red_code_opt,
					  code=code_opt,dcode=dcode_opt,guard_syms=gsyms,defining_equations=def_eqs,
					  defining_equations_finished = def_eq_finished,
					  bicond_sources=bslist}) => 
                                     if !ebd = true then ()
                                     else 
                                     (if not(ep_name = name_str orelse name_str = Names.standardDeductiveEvalNamePrefix^ep_name) 
                                      then ()
				      else let val ep_name' = nextAvailableEvalProcName(MS.name(f),env,SOME(name_str))
				               val new_full_name = (case A.splitForModules(ep_name_with_mod_path) of
                                                                      ([],_) => ep_name'
                                                                    | (mods,_) => (Basic.printListStr(mods,fn x => x,".")) ^ "." ^ ep_name')
                                               val d_ep_name' = Names.standardDeductiveEvalNamePrefix^ep_name'
                                               val d_global_name = S.symbol(Names.standardDeductiveEvalNamePrefix^name_str)
                                               val _ = MS.insert(Prop.fsym_def_table,f,{eval_proc_name=ep_name',
					                         eval_proc_name_with_full_mod_path=new_full_name,
					                         evaluator_being_defined=ebd,
								 obsolete_axioms=obs_axioms,
								 needed_by=nb,
								 guard_syms=gsyms,red_code=red_code_opt,
								 code=code_opt,dcode=dcode_opt,
                                                                 occurring_syms=osyms,defining_equations=def_eqs,
								 defining_equations_finished = def_eq_finished,
								 bicond_sources=bslist})
                                               val _ = HashTable.insert Prop.proc_name_table (ep_name',f)
                                               val flip_symbol = if is_deductive then Symbol.symbol(String.substring(name_str,1,String.size(name_str)-1))
                                                                 else d_global_name                                
                                               val (top_val_map,top_mod_map) = getValAndModMaps(!env) 
                                               val sym = Symbol.symbol(ep_name')
                                               val dsym = Symbol.symbol(d_ep_name')
                                               val _ = (case (lookUpSym(!env,global_name),lookUpSym(!env,flip_symbol)) of
                                                           (SOME(closure1),SOME(closure2)) =>
                                                             if is_deductive then 
                                                                let val new_vmap = Symbol.enter(top_val_map,dsym,closure1)
                                                                    val new_vmap' = Symbol.enter(new_vmap,sym,closure2)
                                                                in
                                                                   env := valEnv({val_map = new_vmap',mod_map=top_mod_map})
                                                                end
                                                            else 
                                                                let val new_vmap = Symbol.enter(top_val_map,sym,closure1)
                                                                    val new_vmap' = Symbol.enter(new_vmap,dsym,closure2)
                                                                in
                                                                   env := valEnv({val_map = new_vmap',mod_map=top_mod_map})
                                                                end
                                                        | _ => ())
                                           in
                                              ()
                                           end)
                                  | _ => ())
                                end
                   | _ => ())
     in
       updateValMap(env,global_name,value)
     end

fun updateTopValEnvLst(env,global_names_and_values,last_value_binding) = 
     List.app (fn (name,value) => updateTopValEnv(env,name,value,last_value_binding))
              global_names_and_values

fun removeTopValEnvBinding(name) = 
        (let val (val_map,mod_map) = getValAndModMaps(!top_val_env)
         in
           top_val_env := valEnv({val_map = #1(Symbol.removeBinding(val_map,name)),mod_map=mod_map})
         end) handle _ => ()

fun removeEnvBinding(env,name) = 
        (let val (val_map,mod_map) = getValAndModMaps(!env)
         in
           env := valEnv({val_map = #1(Symbol.removeBinding(val_map,name)),mod_map=mod_map})
         end) handle _ => ()

fun makePrivate(str) = 
  let val psym = Symbol.makePrivateSymbol(str)
      val (top_val_map,_) = getValAndModMaps(!top_val_env)
      val svalue = (case Symbol.lookUp(top_val_map,Symbol.symbol(str)) of 
                            SOME(v) => v 
                          | _ => (print("\nUnable to secure internal procedure names, specifically: "^str^".\n");Basic.fail("")))
      val _ = updateTopValEnv(top_val_env,psym,svalue,false)
  in
    () 
  end

fun makePrivateLst(names) = List.app makePrivate names

val term_parser: value option ref = ref(NONE)
val prop_parser: value option ref = ref(NONE)

val termType = "Term"
val termLCType = "term"
val constantTermType = "Constant"
val constantTermLCType = "constant"
val atomType = "Atom"
val atomLCType = "atom"
val numTermType = "Numeric term"
val numTermLCType = "numeric term"
val varType = "Variable"
val varLCType = "variable"
val termConType = "Symbol"
val termConLCType = "symbol"
val quantType = "Quantifier"
val quantLCType = "quantifier"
val propConType = "Sentential constructor"
val propConLCType = "sentential constructor"
val propType = "Sentence"
val propLCType = "sentence"
val listType = "List"
val listLCType = "list"
val functionType = "Procedure"
val functionLCType = "procedure"
val closFunType = "Procedure"
val closFunLCType = "procedure"
val closUFunType = "Procedure"
val closUFunLCType = "procedure"
val closBFunType = "Procedure"
val closBFunLCType = "procedure"
val methodType = "Method"
val methodLCType = "method"
val closMethodType = "Method"
val closMethodLCType = "method"
val ruleType = "Method"
val ruleLCType = "method"
val subType = "Substitution"
val subLCType = "substitution"
val unitType = "Unit"
val vectorType = "Vector"
val vectorLCType = "vector"
val unitLCType = "unit"
val cellType = "Cell"
val cellLCType = "cell"
val cellType = "Cell"
val charType = "Character"
val charLCType = "character"
val stringType = "String ("^charLCType^" list)"
val stringLCType = "string ("^charLCType^" list)"

fun getType(termVal(_)) = termType
  | getType(termConVal(_)) = termConType
  | getType(propConVal(A.forallCon)) = quantType
  | getType(propConVal(A.existsCon)) = quantType
  | getType(propConVal(A.existsUniqueCon)) = quantType
  | getType(propConVal(_)) = propConType
  | getType(propVal(_)) = propType 
  | getType(listVal(_)) = listType
  | getType(funVal(_)) = functionType
  | getType(primUFunVal(_)) = functionType
  | getType(primBFunVal(_)) = functionType
  | getType(closFunVal(_)) = closFunType
  | getType(closBFunVal(_)) = closBFunType
  | getType(closUFunVal(_)) = closUFunType
  | getType(primUMethodVal(_)) = methodType
  | getType(primBMethodVal(_)) = methodType
  | getType(methodVal(_)) = methodType
  | getType(closUMethodVal(_)) = closMethodType
  | getType(closBMethodVal(_)) = closMethodType
  | getType(closMethodVal(_)) = closMethodType
  | getType(subVal(_)) = subType
  | getType(tableVal(_)) = tableType
  | getType(mapVal(_)) = mapType
  | getType(unitVal) = unitType
  | getType(cellVal(_)) = cellType 
  | getType(charVal(_)) = charType
  | getType(vectorVal(_)) = vectorType

fun getLCType(termVal(_)) = termLCType
  | getLCType(termConVal(_)) = termConLCType
  | getLCType(propConVal(A.forallCon)) = quantLCType
  | getLCType(propConVal(A.existsCon)) = quantLCType
  | getLCType(propConVal(A.existsUniqueCon)) = quantLCType
  | getLCType(propConVal(_)) = propConLCType
  | getLCType(propVal(_)) = propLCType 
  | getLCType(listVal(_)) = listLCType
  | getLCType(primUFunVal(_)) = functionLCType
  | getLCType(primBFunVal(_)) = functionLCType
  | getLCType(funVal(_)) = functionLCType
  | getLCType(closFunVal(_)) = closFunLCType
  | getLCType(closUFunVal(_)) = closUFunLCType
  | getLCType(closBFunVal(_)) = closBFunLCType
  | getLCType(primUMethodVal(_)) = methodLCType
  | getLCType(primBMethodVal(_)) = methodLCType
  | getLCType(methodVal(_)) = methodLCType
  | getLCType(closUMethodVal(_)) = closMethodLCType
  | getLCType(closBMethodVal(_)) = closMethodLCType
  | getLCType(closMethodVal(_)) = closMethodLCType
  | getLCType(subVal(_)) = subLCType
  | getLCType(tableVal(_)) = tableLCType
  | getLCType(mapVal(_)) = mapLCType
  | getLCType(unitVal) = unitLCType
  | getLCType(vectorVal(_)) = vectorLCType
  | getLCType(cellVal(_)) = cellLCType 
  | getLCType(charVal(_)) = charLCType

val makeNewPWId =
 let val pw_id_index = ref(0)
 in
   fn () => (Basic.inc(pw_id_index);"!9"^(Int.toString(!pw_id_index)))
 end

fun updateTopValEnvLstOldAndFast(name_val_list) = 
  let val (top_val_map,top_mod_map) = getValAndModMaps(!top_val_env)
      fun loop([],vm) = vm
        | loop((name,value)::rest,vm) = loop(rest,Symbol.enter(vm,name,value))
      val vm = loop(name_val_list,top_val_map)
  in
    top_val_env := valEnv({val_map = vm,mod_map=top_mod_map})
  end

val true_term = AT.true_term
val false_term = AT.false_term
val true_val = termVal(true_term)
val false_val = termVal(false_term)

fun MLBoolToAthBoolVal(true) = true_val
  | MLBoolToAthBoolVal(false) = false_val

val MLBoolToAth = MLBoolToAthBoolVal

fun isStringVal(listVal(vals)) = List.all (fn v => (case v of charVal(_) => true | _ => false)) vals
  | isStringVal(_) = false

fun MLStringToAthString(str) = 
      let val int_lst = map ord (explode(str))
      in
         listVal(map charVal int_lst)
      end

fun MLNumStringToAthString(str) = 
      let val int_lst = map ord (explode(str))
          val new_int_lst = (case int_lst of
                                126::more => 45::more
                              | _ => int_lst)
      in
         listVal(map charVal new_int_lst)
      end

fun AthStringToMLString(listVal(vals)) = 
     let val char_list = map (fn v => (case v of charVal(i) => chr(i) | _ => 
                                       genError("String conversion error",NONE))) vals
     in        
        implode(char_list)
     end
  | AthStringToMLString(_) = genError("String conversion error",NONE)

fun isStringValConstructive(v) = SOME(AthStringToMLString(v)) handle _ => NONE

fun charValToString(c) = 
     (case c of
         0 => "^@"
       | 1 => "^A"
       | 2 => "^B"
       | 3 => "^C"
       | 4 => "^D"
       | 5 => "^E"
       | 6 => "^F"
       | 7 => "\\a"
       | 8 => "\\b"
       | 9 => "\\t"
       | 10 => "\\n"
       | 11 => "\\v"
       | 12 => "\\f"
       | 13 => "\\r"
       | 14 => "^N"
       | 15 => "^O"
       | 16 => "^P"
       | 17 => "^Q"
       | 18 => "^R"
       | 19 => "^S"
       | 20 => "^T"
       | 21 => "^U"
       | 22 => "^V"
       | 23 => "^W"
       | 24 => "^X"
       | 25 => "^Y"
       | 26 => "^Z"
       | 27 => "^["
       | 28 => "^/"
       | 29 => "^]"
       | 30 => "^^"
       | 31 => "^_"
       | 32 => "\\blank"
       | _ => (if c < 127 then Char.toString(chr(c)) else 
                  if c = 127 then "\\127" else
                     genError("Illegal character code passed to character output procedure",NONE)))

fun stringValToString([]) = ""
  | stringValToString(c::more) = charValToString(c)^stringValToString(more)

fun printStringVal([]) = ()
  | printStringVal(charVal(10)::more) = (print("\n");printStringVal(more)) 
  | printStringVal(charVal(9)::more) = (print("\t");printStringVal(more)) 
  | printStringVal(charVal(32)::more) = (print(" ");printStringVal(more))
  | printStringVal(charVal(c)::more) = (print(charValToString(c));printStringVal(more))
  | printStringVal(_::more) = genError("Wrong kind of argument encountered in the "^
                                       " list given to print",NONE)

fun valTypeAndString(v) = getType(v)^": "^valToString(v)

fun prettyValToStringNoTypes(propVal(P)) = 
	 let val x = !Options.print_var_sorts
	     val _ = Options.print_var_sorts := false 
	     val res = P.toPrettyString(0,P,makeVarSortPrinter())
	     val _ = Options.print_var_sorts := x
	 in
	   "\n"^res^"\n"
	 end
  | prettyValToStringNoTypes(termVal(t)) = 
	 let val x = !Options.print_var_sorts
	     val _ = Options.print_var_sorts := false 
	     val res = AT.toPrettyString(0,t,makeVarSortPrinter())
	     val _ = Options.print_var_sorts := x
	 in
	   if AT.height(t) > 0 then "\n"^res^"\n" else res 
	 end
  | prettyValToStringNoTypes(listVal(vals)) = "["^prettyValsToStringNoTypes(vals)^"]"
  | prettyValToStringNoTypes(v) = valToString(v) 
and
    prettyValsToStringNoTypes([]) = ""
  | prettyValsToStringNoTypes([v]) = prettyValToStringNoTypes(v)
  | prettyValsToStringNoTypes(v1::v2::more) = prettyValToStringNoTypes(v1)^" "^prettyValsToStringNoTypes(v2::more) 

fun printVal(v) = 
	let val sortVarPrinter = makeVarSortPrinter()
	    fun f(v as subVal(sub)) = (print("\n");print(subType^": ");Terms.printSub(sub);print("\n"))             
   	      | f(v as propVal(P)) = (print("\n");print(propType^": "^
              	                      P.toPrettyString(String.size(propType)+2,P,sortVarPrinter));
                   	              print("\n"))
	      | f(v as termVal(t)) = (print("\n");print(termType^": "^
				      AT.toPrettyStringDefault(String.size(termType)+2,t));
                                      print("\n"))
              | f(v as tableVal(tab)) = (print("\n");print(tableType^": "^(tableToString tab));print("\n"))
              | f(v as mapVal(m)) = (print("\n");print(mapType^": "^(mapToString m));print("\n"))
	      | f(v) = (print("\n"^getType(v));
            		       let val vs = (case v of listVal(_) => prettyValToStringNoTypes(v) | _ => valToString(v))
	                       in 
	                          if vs = "" then print("\n") else
            	                  (print(": ");print(vs);print("\n"))
	                       end)
	in
	   f v
	end

fun printValNoType(v as subVal(sub)) = Terms.printSub(sub)
  | printValNoType(v as propVal(P)) = print(P.toPrettyString(0,P,makeVarSortPrinter()))
  | printValNoType(v as termVal(t)) =   print(AT.toPrettyStringDefault(0,t))
  | printValNoType(v as tableVal(t)) = print(tableToString t)
  | printValNoType(v as mapVal(m)) = print(mapToString m)
  | printValNoType(v) =
                   let val vs = valToString(v) 
                   in 
                      if vs = "" then print("\n") else
                         print(vs)
                   end

fun printValWithTypedStrings(v as subVal(sub)) = (print(subType^": ");Terms.printSub(sub);print("\n"))
  | printValWithTypedStrings(v) =
                  (print(getType(v));
                   let val vs = valToString(v) 
                   in 
                      if vs = "" then print("\n") else
                         (print(": ");print(vs);print("\n"))
                   end)

fun valLCTypeAndString(v) = let val str = prettyValToString(v)
                            in
                               if Util.small(str,20) then getLCType(v)^": "^str 
                               else getLCType(v)^":\n"^str 
                            end

fun valTypeAndStringNoColon(v) = let val str = prettyValToString(v)
                                 in
                                    if Util.small(str,20) then getType(v)^": "^str 
                                    else getType(v)^":\n"^str 
                                 end 

fun valLCTypeAndStringNoColon(v) = let val str = prettyValToString(v)
                                   in
                                     if Util.small(str,20) then getLCType(v)^" "^str 
                                     else getLCType(v)^"\n"^str 
                                   end

fun ordinal(i) = let fun suffix(1) = "st"
                       | suffix(2) = "nd"
                       | suffix(3) = "rd"
                       | suffix(_) = "th"
                 in
                    (case i of 
                        1 => "first"
                      | 2 => "second"
                      | 3 => "third"
                      | 4 => "fourth"
                      | 5 => "fifth"
                      | 6 => "sixth"
                      | 7 => "seventh" 
                      | 8 => "eighth"
                      | 9 => "ninth"
                      | 10 => "tenth"
                      | _ => if (((i mod 100) = 11) orelse ((i mod 100) = 12)) then Int.toString(i)^"th"
                             else Int.toString(i)^suffix(i mod 10))
                 end
           
val try_space = "  "
val try_space_chars = String.explode(try_space)

fun processTryMessage(str) = 
        let val blank = #" "
            fun f(c) = if c = #"\n"  then c::try_space_chars else [c]
        in 
          String.implode(Basic.flatten(List.map f (String.explode(str))))
        end

fun desugarPW(A.pickWitnessesDed({ex_gen,var_ids as [vid],inst_id,body=main_body,pos}),env,ab,ev) = 
       A.pickWitnessDed({ex_gen=ex_gen,var_id=vid,inst_id=inst_id,body=main_body,pos=pos})
  | desugarPW(A.pickWitnessesDed({ex_gen,var_ids as vid::more_vars,inst_id,body=main_body,pos}),env,ab,ev) = 
      let val unique_name = Symbol.symbol(makeNewPWId())
          val ded1 = A.pickWitnessesDed(
                     {ex_gen=A.exp(A.idExp({msym=msym unique_name,mods=[],sym=unique_name,no_mods=true,pos=A.dum_pos})),var_ids=more_vars,inst_id=inst_id,
		      body=main_body,pos=pos})
          val ds1 = desugarPW(ded1,env,ab,ev)
      in
        A.pickWitnessDed({ex_gen=ex_gen,var_id=vid,inst_id=SOME(unique_name),
						  body=ds1,pos=pos})
      end
  | desugarPW(d,_,_,_) = d

fun dexpect(str1,P) = str1^" was expected, but the given sentence was \n"^P.propKind(P)^": "^
                      Util.decide(P.toPrettyString(0,P,makeVarSortPrinter()),50)

fun dwrongArgKind(name,i,str1,P) = "Wrong kind of sentence given as "^ordinal(i)^" argument\nto "^name^
                                      "---"^dexpect(str1,P)

fun expect(str,v) = let val vstr = valLCTypeAndString(v)
                    in
                       "a "^str^" was expected,\nbut the given argument was a "^Util.decide(vstr,20)
                    end

fun expectInOneLine(str,v) = "a "^str^" was expected, but the given value was a "^valLCTypeAndString(v)

fun expectUC(str,v) = "A "^str^" was expected, but the given value was a "^valLCTypeAndString(v)

fun termExpect(str,t) = "a "^str^" was expected, but the given term was of sort\n"^
			(F.toStringDefault(AT.getSort(t)))

fun expectExplain(str,expl,v) = "a "^str^" "^expl^" was expected,\nbut the given value "^
				"was a "^valLCTypeAndString(v)


fun wrongTermKind(name,i,str,t) = "Wrong sort of term given as "^ordinal(i)^" argument\nto "^name^
                                  "---"^termExpect(str,t)

fun wrongArgKindGeneric(name,str) = 
        "Wrong kind of value given as argument to "^name^"---a "^str^" was expected"

fun wrongArgKind(name,i,str,v) = "Wrong kind of value given as "^ordinal(i)^" argument\nto "^name^"---"^expect(str,v)
       
fun wrongArgKindExpectationOnly(str,v) = "Wrong kind of value found here---"^expect(str,v)

fun wrongArgKindInOneLine(name,i,str,v) = "Wrong kind of value found here---"^expectInOneLine(str,v)

fun argNumToString(i) = if i = 0 then "zero arguments are" else if i = 1 then "one argument is" else 
                        Int.toString(i)^" arguments are"

fun wrongArgNumber(name,given,required) = "Wrong number of arguments ("^Int.toString(given)^") given\nto "^
                                          name^"---exactly "^argNumToString(required)^" required"

fun wrongArgNumberFlex(name,given,nums) = 
     "Wrong number of arguments ("^Int.toString(given)^") given to "^
      name^"---either "^(Basic.printListStr(nums,Int.toString," or "))^" arguments are required"

fun propLstToAthPropLst(props) = listVal(map propVal props)

fun athTermVarToAth(v) = termVal(AT.makeVar(v))

fun listOfAthVarsToAth(l) = listVal(map athTermVarToAth l)

fun makeTermConVal(x as regFSym(some_fsym)) = 
        let val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
        in 
           if (arity > 0) then termConVal(x)
           else termVal(AT.makeConstant(name))
        end 

fun makeTermConValFromStructureConstructor(acon as {name,arity:int,range_type,bits:Word8.word,...}:D.ath_struc_constructor) = 
	if (arity > 0) then termConVal(regFSym(D.struc_con(acon)))
        else 
          let val poly = Data.isPolyWord(bits)
          in
	     termVal(AT.makeSortedConstantAux(name,range_type,poly))
          end

fun coerceTermConValIntoTermVal(v) = (case coerceFunSymbolIntoTerm(v) of
                                       SOME(t) => SOME(termVal(t))
                                     | _ => NONE)

fun coerceTermIntoTermConVal(t) = (case coerceTermIntoTermCon(t) of
                                    SOME(fsym) => SOME(termConVal(fsym))
                                  | _ => NONE)

fun coerceTermValIntoTermConVal(termVal(t)) = coerceTermIntoTermConVal(t)
  | coerceTermValIntoTermConVal(v as termConVal(_)) = SOME(v)
  | coerceTermValIntoTermConVal(v as propVal(P)) = 
      (case P.isAtom(P) of
	  SOME(t) => coerceTermIntoTermConVal(t)
        | _ => NONE)
  | coerceTermValIntoTermConVal(_) = NONE

fun isGeneralApp(t) = 
      (case AT.isApp(t) of
          SOME(fsym,args) => (case D.isTermConstructorAsFSymOption(fsym) of 
                                    SOME(afunsym) => SOME(regFSym afunsym,args)
                                  | _ => NONE)
        | _ => (case AT.isNumConstantOpt(t) of
                   SOME(anum) => SOME(athNumFSym(anum),[])
                 | _ => (case AT.isIdeConstant(t) of
                            SOME(str) => SOME(metaIdFSym(str),[])
                          | _ => NONE)))

fun applyTermConstructor(name,arity,term_args,pos) = 
                   AT.makeApp(name,term_args) 
		   handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))

fun applyBinaryTermConstructor(name,term_arg_1,term_arg_2,pos) = 
                  (AT.makeAppBinary(name,term_arg_1,term_arg_2) 
		   handle Basic.FailLst(msgs) => 
                    (let val msg = Basic.failMsgsToStr(msgs)
                     in
                        evError(msg,SOME(pos))
                     end))

fun applyUnaryTermConstructor(name,term_arg,pos) = 
                   AT.makeAppUnary(name,term_arg) 
		   handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))

fun applyTermConstructorNoPos(name,term_args) = 
                   AT.makeApp(name,term_args) 
		   handle Basic.FailLst(msgs) => primError(Basic.failMsgsToStr(msgs))

fun isBooleanTerm(t) = (case AT.isApp(t) of 
                           SOME(fsym,_) =>  hasBooleanRangeType(fsym)
                         | _ => (case AT.isVarOpt(t) of
                                    SOME(_) => true
                                  | _ => false))

fun coerceValIntoTerm(termVal(t)) = SOME(t)
  | coerceValIntoTerm(v as termConVal(_)) = 
       (case coerceFunSymbolIntoTerm(v) of  
           SOME(t) => SOME(t)
         | _ => NONE) 
  | coerceValIntoTerm(propVal(P)) = P.isAtom(P)
  | coerceValIntoTerm(_) = NONE

fun coerceValIntoTermCon(v as termConVal(tc)) = SOME(tc)
  | coerceValIntoTermCon(v as termVal(t)) = coerceTermIntoTermCon(t) 
  | coerceValIntoTermCon(v as propVal(P)) = (case P.isAtom(P) of 
					       SOME(t) => coerceTermIntoTermCon(t)
					     | _ => NONE)
  | coerceValIntoTermCon(_) = NONE

fun coerceValIntoPropVal(v) = (case coerceValIntoProp(v) of
                                 SOME(P) => SOME(propVal(P))
                               | _ => NONE)

fun coerceValIntoTermVal(v) = case coerceValIntoTerm(v) of
                                 SOME(t) => SOME(termVal(t))
                               | _ => NONE

fun coerceValIntoTermConVal(v) = case coerceValIntoTermCon(v) of
                                    SOME(tc) => SOME(termConVal(tc))
                                  | _ => NONE

fun isApplicable(closFunVal(_)) = (true,false)
  | isApplicable(closUFunVal(_)) = (true,false)
  | isApplicable(closBFunVal(_)) = (true,false)
  | isApplicable(funVal(_)) = (true,false)
  | isApplicable(primUFunVal(_)) = (true,false)
  | isApplicable(primBFunVal(_)) = (true,false)
  | isApplicable(propConVal(_)) = (true,false)
  | isApplicable(subVal(_)) = (true,false)
  | isApplicable(v) = (case coerceValIntoTermCon(v) of
                         SOME(regFSym(some_fsym)) => let val arity = D.fsymArity some_fsym in (arity > 0,arity = 0)  end
                       | _ => (false,false))

fun appSubToTerm(sub,t,pos) = termVal(AT.applySub(sub,t))

fun appSubToTermNoPos(sub,t) = termVal(AT.applySub(sub,t))

fun appSubToProp(sub,p,pos) = propVal(P.applySub(sub,p))

fun appSubToPropNoPos(sub,p) = propVal(P.applySub(sub,p))

fun applySubToValPosLst(sub,arg_val_pos_lst) = 
  let fun applySub(arg_val_pos_lst) = 
            let fun f([],res) = rev(res)
                  | f((v,pos)::more,res) = 
                      (case coerceValIntoTerm(v) of
                          SOME(t) => f(more,appSubToTerm(sub,t,pos)::res)
                        | _ => (case coerceValIntoProp(v) of
                                   SOME(P) => f(more,appSubToProp(sub,P,pos)::res)
                                 | _ => evError("Wrong kind of value found in the argument list of "^
                                                "a substitution application; "^expect(termLCType,v),SOME(pos))))
            in 
              listVal(f(arg_val_pos_lst,[]))
            end
 in
    applySub(arg_val_pos_lst)
 end
  
fun applySubToValLst(sub,arg_vals,pos) = 
  let fun applySub(arg_val_lst) = 
            let fun f([],res) = rev(res)
                  | f(v::more,res) = 
                      (case coerceValIntoTerm(v) of
                          SOME(t) => f(more,appSubToTerm(sub,t,pos)::res)
                        | _ => (case coerceValIntoProp(v) of
                                   SOME(P) => f(more,appSubToProp(sub,P,pos)::res)
                                 | _ => evError("Wrong kind of value found in the argument list of "^
                                                "a substitution application; "^expect(termLCType,v),SOME(pos))))
            in 
              listVal(f(arg_val_lst,[]))
            end
  in
    applySub(arg_vals)
  end

fun applySubToValLstNoPos(sub,arg_vals:value list) = 
  let fun applySub(arg_val_lst) = 
            let fun f([],res) = rev(res)
                  | f(v::more,res) = 
                      (case coerceValIntoTerm(v) of
                          SOME(t) => f(more,appSubToTermNoPos(sub,t)::res)
                        | _ => (case coerceValIntoProp(v) of
                                   SOME(P) => f(more,appSubToPropNoPos(sub,P)::res)
                                 | _ => evError("Wrong kind of value found in the argument list of "^
                                                "a substitution application; "^expect(termLCType,v),NONE)))
            in 
              listVal(f(arg_val_lst,[]))
            end
  in
    applySub(arg_vals)
  end
  
fun coerceValIntoProps(tvals) = map coerceValIntoProp tvals     
val coerceProp = P.isAtom
fun coercibleTermVal(v) = (case coerceValIntoProp(v) of NONE => false | _ => true)
fun coercibleProp(p) = (case coerceProp(p) of NONE => false | _ => true)

val (isTrueTerm,isFalseTerm) = (AT.isTrueTerm,AT.isFalseTerm)

fun isTrueTermFromProp(p) = 
        (case P.isAtom(p) of 
            SOME(t) => isTrueTerm(t)
          | _ => false)

fun isFalseTermFromProp(p) = 
        (case P.isAtom(p) of 
            SOME(t) => isFalseTerm(t)
          | _ => false)

fun isFalseTerm(t) = (case AT.isConstant(t) of SOME(fsym) => MS.modSymEq(fsym,N.mfalse_logical_symbol)
 					    | _ => false)

fun getBool(v) =  case coerceValIntoTerm(v) of
                     SOME(t) => if isTrueTerm(t) then SOME(true)
                                else if isFalseTerm(t) then SOME(false) 
                                else NONE
                   | _ => NONE

fun logError("and",pos,v) = 
      evError("Non-boolean term given to the short-circuit 'and' operator &&, namely: " ^ valToString(v),SOME(pos))
  | logError("or",pos,v) = 
      evError("Non-boolean term given to the short-circuit 'or' operator &&",SOME(pos))
  | logError(_) = raise Basic.Never

fun valEq(termVal(s),v) = (case coerceValIntoTerm(v) of
                                SOME(t) => AT.termEq(s,t)
                              | _ => false)
  | valEq(propVal(P),v) = (case coerceValIntoProp(v) of
                                 SOME(Q) => P.alEq(P,Q)
                               | _ => false)
  | valEq(termConVal(fsym),v) = (case coerceValIntoTermCon(v) of
                                       SOME(fsym') => funSymEq(fsym,fsym')
                                     | _ => false)
  | valEq(propConVal(con1),propConVal(con2)) = (con1 = con2) 
  | valEq(listVal(vl1),listVal(vl2)) = valEqLst(vl1,vl2)
  | valEq(unitVal,unitVal) = true
  | valEq(vectorVal(v1),vectorVal(v2)) = (v1 = v2)
  | valEq(cellVal(v1),cellVal(v2)) = (v1 = v2)
  | valEq(charVal(i),charVal(j)) = (i = j) 
  | valEq(subVal(sub1),subVal(sub2)) = AT.subEq(sub1,sub2)
  | valEq(tableVal(tab1),tableVal(tab2)) = tableEq(tab1,tab2)
  | valEq(mapVal(m1),mapVal(m2)) = mapEq(m1,m2)
  | valEq(_,_) = false 
and
    valEqLst([],[]) = true
  | valEqLst(v1::more1,v2::more2) = if valEq(v1,v2) then valEqLst(more1,more2) else false
  | valEqLst(_,_) = false
and tableEq(t1,t2) = 
       let val dom1 = map (fn (x,_) => x) (HashTable.listItemsi t1)
           val dom2 = map (fn (x,_) => x) (HashTable.listItemsi t2)
           fun sameVal(key) = (case ((HashTable.find t1 key),(HashTable.find t2 key)) of
                                  (SOME(v1),SOME(v2)) => valEq(v1,v2)
                                | _ => false)
       in
         (List.all sameVal dom1) andalso (List.all sameVal dom2)
       end
and mapEq(t1,t2) = 
       let val dom1 = map (fn (x,_) => x) (Maps.listKeyValuePairs t1)
           val dom2 = map (fn (x,_) => x) (Maps.listKeyValuePairs t2)
           fun sameVal(key) = (case (Maps.find(t1,key),Maps.find(t2,key)) of
                                  (SOME(v1),SOME(v2)) => valEq(v1,v2)
                                | _ => false)
       in
         (List.all sameVal dom1) andalso (List.all sameVal dom2)
       end

(*** Handling of structure equality: **********)

fun strucValEq0(t1,t2) =    
        (case FTerm.isApp(AT.getSort(t1)) of
           SOME(struc_name,sort_args) => 
             if isNonFreeDT(struc_name) then 
                (case MS.find(Prop.structure_equality_table,struc_name) of
                    SOME(f) => let val p = f(t1,t2)
                                   val evalString = !evaluateString
                                   val pstr = Prop.toStringDefault(p)
				   val eval1_safe_name = getSafeName("eval1")
                                   val str = "(" ^ eval1_safe_name ^ " " ^ pstr ^ ")"
                                   val res = evalString(str) 
                               in
                                  (case res of
                                      termVal(t) => isTrueTerm(t)
                                    | _ => (print("\nHere we are!\n");raise Basic.Never))
                               end
                 | _ => AT.termEq(t1,t2))
             else genTermEq(t1,t2)
          | _ => AT.termEq(t1,t2))
and strucValEqLst([],[]) = true
  | strucValEqLst(t1::more1,t2::more2) = strucValEq0(t1,t2) andalso strucValEqLst(more1,more2)
  | strucValEqLst(_) = false
and genTermEq(t1,t2) = 
      (case (AT.isApp(t1),AT.isApp(t2)) of
          (SOME(f1,args1),SOME(f2,args2)) => 
              if null(args1) orelse null(args2) then AT.termEq(t1,t2) 
              else MS.modSymEq(f1,f2) andalso strucValEqLst(args1,args2)
        | _ => AT.termEq(t1,t2))

fun strucValEq(v1 as (termVal(t1)),v2 as (termVal(t2))) = strucValEq0(t1,t2)
  | strucValEq(v1,v2) = valEq(v1,v2)
     
fun env2HTVal(valEnv({val_map,mod_map})) = 
      let val ht1: val_hash_table = HashTable.mkTable(SemanticValues.hashVal, valEq) (!(Options.default_table_size),Data.GenEx("Failed table creation"))
          val ht2: val_hash_table = HashTable.mkTable(SemanticValues.hashVal, valEq) (!(Options.default_table_size),Data.GenEx("Failed table creation"))
          fun makeValEntry(pair as (name_sym,value)) = 
                 let val name_str = Symbol.name(name_sym)
                 in
                    HashTable.insert ht1 (MLStringToAthString(name_str),value)
                 end
          fun makeModEntry(name_sym,m:module as {env,...}) = 
         	 let val name_str = Symbol.name(name_sym)
                 in
                    HashTable.insert ht2 (MLStringToAthString(name_str),env2HTVal(env))
                 end
          val _ = List.app makeValEntry (Symbol.listSymbolsAndImages val_map)
          val _ = List.app makeModEntry (Symbol.listSymbolsAndImages mod_map)
      in 
         listVal([tableVal(ht1),tableVal(ht2)])
      end

datatype term_num = inum of int | rnum of real

local exception Ex in
fun areStringVals(vals) = 
      let fun f([],strings) = rev(strings)
            | f(v::more,strings) = (case isStringValConstructive(v) of
                                       SOME(str) => f(more,str::strings)
                                     | _ => raise Ex)
      in
         SOME(f(vals,[])) handle Ex => NONE
      end
end

fun withAtom(P,f,sort_sub) = 
     (case P.isAtom(P) of
	 SOME(t) => SOME(f t,sort_sub)
       | _ => NONE)

fun makeQuantProp(SOME(A.forallCon),vars,body) = P.makeUGen(vars,body)
  | makeQuantProp(SOME(A.existsCon),vars,body) = P.makeEGen(vars,body)
  | makeQuantProp(SOME(A.existsUniqueCon),vars,body) = P.makeEGenUnique(vars,body)
  | makeQuantProp(_,_,P) = P


(***************************************************************************************
                                I N T E R P R E T E R
***************************************************************************************)

fun isBinaryProp(P) = 
  (case P.isConj(P) of 
     SOME(props) => SOME(propConVal(A.andCon),map propVal props)
   | _ => (case P.isDisj(P) of                     
	      SOME(props) => SOME(propConVal(A.orCon),map propVal props)
            | _ => (case P.isCond(P) of
	               SOME(p1,p2) => SOME(propConVal(A.ifCon),[propVal(p1),propVal(p2)])
                     | _ => (case P.isBiCond(P) of
 	                        SOME(p1,p2) => SOME(propConVal(A.iffCon),[propVal(p1),propVal(p2)])
                               | _ => NONE))))

fun isQuant(P) = 
  (case P.isUGen(P) of 
     SOME(v,p) => SOME(propConVal(A.forallCon),termVal(AT.makeVar(v)),propVal(p))
   | _ => (case P.isEGen(P) of 
	      SOME(v,p) => SOME(propConVal(A.existsCon),termVal(AT.makeVar(v)),propVal(p))
            | _ => (case P.isEGenUnique(P) of
                       SOME(v,p) => SOME(propConVal(A.existsUniqueCon),termVal(AT.makeVar(v)),propVal(p))
                     | _ => NONE)))

fun patStringEq(v,int_lst) = 
      let fun f([],[]) = true
            | f(charVal(i)::more1,j::more2) = if i = j then f(more1,more2) else false
            | f(_,_) = false
      in
         case v of
            listVal(vals) => f(vals,int_lst)
          | _ => false
      end
         
fun unifySorts(arg_sort,param_sort) = 
              let val U = F.chooseUnificationProcedureForSorts(param_sort,arg_sort)
                  val res = SOME(U([arg_sort],[param_sort],~1)) handle _ => NONE
              in
                  res
              end

fun consolidateSubs(init_sub,dom1,val_map,dom2,list_val_map) = 
   let val sub' = Symbol.augment(init_sub,val_map)
       fun loop([],m) = m                                                   
         | loop(s::rest,m) = 
             let val values = (case Symbol.lookUp(list_val_map,s) of
                                  SOME(v) => v)
             in
               loop(rest,Symbol.enter(m,s,listVal(values)))
             end
   in
     loop(dom2,sub')
   end

fun getSignedInt(i,neg) = if neg then Int.~(i) else i
fun getSignedReal(r,neg) = if neg then Real.~(r) else r

fun getValCode(charVal(c)) = Real.fromInt(c)
  | getValCode(v) = (case coerceValIntoTerm(v) of
                        SOME(t) => (case AT.getNumVal(t) of
                                       SOME(A.int_num(i,_),neg) => Real.fromInt(getSignedInt(i,neg))
                                     | SOME(A.real_num(r,_),neg) => getSignedReal(r,neg)
                                     | _ => Real.fromInt(~1))
                     | _ => Real.fromInt(~1))

structure RE = MakeRE(type pat = AbstractSyntax.pattern 
                      type value = SemanticValues.value
		      type constraint = AbstractSyntax.expression
                      val patToString = AbstractSyntax.printPat
                      val constraintToString = AbstractSyntax.unparseExp 
                      val valToString = prettyValToStringNoTypes
                      val getValCode = getValCode 
		      val valEq = valEq
                      val getListValues = (fn listVal(vals) => SOME(vals) | _ => NONE)
                      val patBindableIds = (fn p => Symbol.listSymbols(AbstractSyntax.patBindableIds(p)))
                      val isValOfPat = A.isValOfPat
		      val constraintFreeIds = A.freeVarsExpAsList)
		      
fun matchPat(ath_value,pattern,evaluateExp) = 
     let fun lookUpInOuterEnv(id) = (SOME(evaluateExp(A.idExp{msym=msym id,mods=[],no_mods=true,sym=id,pos=A.dum_pos},NONE))) handle _ => NONE
         fun decide(true,sub,sort_sub) = SOME(sub,sort_sub)
           | decide(false,_,_) = NONE  
         fun opConstraintOk((i,j),v) = 
               if i < 0 then true 
               else let val j' = if j < 0 then Options.defaultPrec(i) else j
                    in
                      (case v of 
                          closFunVal(A.functionExp({params,body,pos=fexp_pos,...}),clos_env,{prec,assoc,...}) =>
                             length(params) = i andalso (j < 0 orelse (!prec) = j')
                        | closUFunVal(_) => i = 1 andalso j < 0
                        | closBFunVal(_) => i = 1 andalso j < 0
                        | primUFunVal(f,{prec,...}) => i = 1 andalso (j < 0 orelse (!prec) = j')
                        | primBFunVal(f,{prec,...}) => i = 2 andalso (j < 0 orelse (!prec) = j')
                        | funVal(f,name,{arity,prec,...}) => arity = i andalso (j < 0 orelse (!prec) = j')
                        | propConVal(con) => true
                        | _ =>  (case coerceValIntoTermCon(v) of
                                    SOME(regFSym(some_fsym)) => 
                                       let val (arity,prec) = (D.fsymArity(some_fsym),!(D.fsymPrec(some_fsym)))
                                       in
                                          arity = i andalso (j < 0 orelse prec = j')
                                       end
                                  | _ => false))
                    end
         fun matchPatVar(v,var_name,sort_as_fterm,op_tag,pos,sub:value Symbol.mapping,sort_sub) = 
             (case Symbol.lookUp(sub,var_name) of
                 SOME(v') => (case sort_as_fterm of
                                 NONE => decide(valEq(v,v'),sub,sort_sub)
                               | SOME(sort) => let val sort' = F.applySub(sort_sub,sort)
                                               in 
                                                 (case (coerceValIntoTerm v,coerceValIntoTerm v') of
                                                    (SOME t,SOME t') => 
                                                      let val t_new = AT.applySortSub(sort_sub,t)
                                                      in
                                                       (case unifySorts(AT.getSort(t_new),sort') of
                                                           SOME(sort_sub') => 
                                                              let val t1 = AT.applySortSub(sort_sub',t_new)
                                                                  val t1' = AT.applySortSub(sort_sub',t')
                                                              in
                                                                if AT.termEq(t1,t1') then 
                                                                   SOME(Symbol.enter(sub,var_name,termVal(t1)),F.composeSubs(sort_sub',sort_sub))
                                                                else NONE
                                                              end
                                                         | _ => NONE)
                                                      end
                                                  | _ => NONE)
                                               end)
               | NONE => (case sort_as_fterm of
                             NONE => (case (coerceValIntoTerm v) of
                                         NONE => SOME(Symbol.enter(sub,var_name,v),sort_sub)
                                       | SOME(t) => let val t' = AT.applySortSub(sort_sub,t)
                                                    in         
                                                       SOME(Symbol.enter(sub,var_name,termVal(t')),sort_sub)
                                                    end)
                           | SOME(sort) => (case (coerceValIntoTerm v) of 
                                                 (SOME t) => 
                                                   let val term_sort = AT.getSort(t)
                                                       val sort' = F.applySub(sort_sub,sort)
                                                   in
                                                     (case unifySorts(term_sort,sort') of
                                                         SOME(sort_sub') =>  
                                                            let val sort_sub'' = F.composeSubs(sort_sub',sort_sub)
                                                                val t' = AT.applySortSub(sort_sub'',t)
                                                            in         
                                                              SOME(Symbol.enter(sub,var_name,termVal(t')),sort_sub'')
                                                            end
                                                       | _ => NONE)
                                                   end
                                               | _ => NONE)))
         fun valMatch(v,A.idPat({name,pos,sort_as_fterm,op_tag,...}),sub,sort_sub) = 
	     	      matchPatVar(v,name,sort_as_fterm,op_tag,pos,sub,sort_sub)
           | valMatch(v,A.funSymPat({name,sort_opt,arity,pos,...}),sub,sort_sub) = 
                 (case coerceValIntoTermConVal(v) of
                     SOME(v' as termConVal(regFSym(some_fsym))) =>
                                 (case sort_opt of 
                                     NONE => (let val (fsym_name,fsym_arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
                                                  val cond1 = MS.modSymEq(fsym_name,name)
                                              in
                                                 if cond1 andalso (arity = fsym_arity) then SOME(sub,sort_sub) else NONE
                                              end)
                                   | SOME(sort) => 
                                       (case coerceValIntoTerm(v) of 
                                           SOME(t) => 
                                              (case unifySorts(AT.getSort(AT.applySortSub(sort_sub,t)),sort) of
                                                  SOME(sort_sub') => 
                                                      if MS.modSymEq(D.fsymName(some_fsym),name) andalso arity = D.fsymArity(some_fsym) then
                                                         SOME(sub,F.composeSubs(sort_sub',sort_sub))
                                                      else NONE
                                                | _ => NONE)
                                         | _ => NONE))
                   | _ => NONE)
           | valMatch(propConVal(pc),A.propConPat({pcon,...}),sub,sort_sub) = decide(pc = pcon,sub,sort_sub)
           | valMatch(v,A.numPat({ath_num=anum,...}),sub,sort_sub) = 
               (case coerceValIntoTerm(v) of
                   SOME(t) => (case AT.isNumConstantOpt(t) of 
                                     SOME(anum') => decide(A.athNumEquality(anum,anum'),sub,sort_sub)
                                   | _ => NONE)
                 | _ => NONE)

(*----------------------          CONSTANT PATTERNS:           ----------------------*)
           | valMatch(_,A.anyPat(_),sub,sort_sub) = SOME(sub,sort_sub) 
           | valMatch(v,A.constantTermVarPat({term_var,...}),sub,sort_sub) = 
               (case coerceValIntoTerm(v) of
                   SOME(t) => (case AT.isVarOpt(t) of
                                  SOME(var) => 
                                      (case unifySorts(ATV.getSort(ATV.applySortSub(sort_sub,var)),ATV.getSort(ATV.applySortSub(sort_sub,term_var))) of
                                         SOME(sort_sub') => decide(AthTermVar.athTermVarEq(ATV.applySortSub(sort_sub',var),
        				                                                   ATV.applySortSub(sort_sub',term_var)),sub,sort_sub')
                                       | NONE => NONE)
                                | _ => NONE)
                 | _ => NONE)
           | valMatch(v,A.constantMetaIdPat({name,...}),sub,sort_sub) = 
               (case coerceValIntoTerm(v) of
                   SOME(t) => (case AT.isIdeConstant(t) of
                                  SOME(str) => decide(S.symEq(S.symbol(str),name),sub,sort_sub)
                                | _ => NONE)
                 | _ => NONE)
           | valMatch(v,A.constantCharPat({ch,...}),sub,sort_sub) = 
                 (case v of
                     charVal(c) => decide(c = ch,sub,sort_sub)
                   | _ => NONE)
           | valMatch(v,A.constantStringPat({str,pos}),sub,sort_sub) = decide(patStringEq(v,str),sub,sort_sub)

(*-------------------------       SOME-SUCH PATTERNS:           ----------------------*)

           | valMatch(v,A.someVarPat({id,...}),sub,sort_sub) = 
               (case coerceValIntoTerm(v) of
                   SOME(t) => decide(AT.isVar(t),doName(sub,id,v),sort_sub)
                 | _ => NONE)
           | valMatch(v,A.somePropConPat({id,...}),sub,sort_sub) =
               (case v of
                   propConVal(pc) => decide(not(A.isQuantPropCon(pc)),doName(sub,id,v),sort_sub)
                 | _ => NONE)
           | valMatch(v,A.someQuantPat({id,...}),sub,sort_sub) = 
               (case v of
                   propConVal(pc) => decide(A.isQuantPropCon(pc),doName(sub,id,v),sort_sub)
                 | _ => NONE)
           | valMatch(v,A.someTermPat({id,...}),sub,sort_sub) = 
                (case coerceValIntoTermVal(v) of
                    SOME(v') => SOME(doName(sub,id,v'),sort_sub)
                  | _ => NONE)
           | valMatch(v,A.somePropPat({id,...}),sub,sort_sub) = 
                (case coerceValIntoPropVal(v) of
                    SOME(v') => SOME(doName(sub,id,v'),sort_sub)
                  | _ => NONE)
           | valMatch(v,A.someAtomPat({id,...}),sub,sort_sub) = 
                (case coerceValIntoProp(v) of
                    SOME(P) => withAtom(P,fn _ => doName(sub,id,propVal(P)),sort_sub)
                  | _ => NONE)
           | valMatch(v,A.someSymbolPat({id,...}),sub,sort_sub) = 
                (case coerceValIntoTermConVal(v) of
                    SOME(v') => SOME(doName(sub,id,v'),sort_sub)
                  | _ => NONE)
           | valMatch(v,A.someListPat({id,...}),sub,sort_sub) =               
                 (case v of
                     listVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someFunctionPat({id,...}),sub,sort_sub) = 
                 (case v of
                     funVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | primUFunVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | primBFunVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | closFunVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | closUFunVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | closBFunVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someMethodPat({id,...}),sub,sort_sub) = 
                 (case v of
                     methodVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | primUMethodVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | primBMethodVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | closMethodVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | closUMethodVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | closBMethodVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someVectorPat({id,...}),sub,sort_sub) = 
                 (case v of
                     vectorVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someCharPat({id,...}),sub,sort_sub) = 
                 (case v of
                     charVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someSubPat({id,...}),sub,sort_sub) = 
                 (case v of
                     subVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someCellPat({id,...}),sub,sort_sub) = 
                 (case v of
                     cellVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someTablePat({id,...}),sub,sort_sub) = 
                 (case v of
                     tableVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)
           | valMatch(v,A.someMapPat({id,...}),sub,sort_sub) = 
                 (case v of
                     mapVal(_) => SOME(doName(sub,id,v),sort_sub)
                   | _ => NONE)

(*----------------------           LIST PATTERNS:                ----------------------*)

           | valMatch(v,pat as A.listPats({member_pats,pos}),sub,sort_sub) = 
               (case v of
                   listVal(vals) => valMatchLst(vals,member_pats,sub,sort_sub)
                 | _ => NONE)

           | valMatch(v,sp as A.splitPat({pats,code,re_form,...}),sub,sort_sub) =

(*** New re-based code for split patterns: ***
                 (case v of 
                     listVal(vals) => 
                                 let fun evaluateConstraint(e,(dom1,m1,dom2,m2)) = evalConstraint(e,sub,(dom1,m1,dom2,m2))
                                 in
                                    (case RE.match(re_form,code,vals,sub,valMatchTermSubOnly(sub,sort_sub),evaluateConstraint,lookUpInOuterEnv) of
                                          SOME((dom1,val_map,dom2,list_val_map),time_elapsed) => 
                                               let val res_sub = consolidateSubs(sub,dom1,val_map,dom2,list_val_map)
                                               in
                                                  SOME(res_sub,sort_sub)
                                               end
                                        | _ => NONE)
                                 end  
                  | _ => NONE)
***)

(*** Old code for split patterns currently active: ***)

              (case pats of 
                [pat1,pat2] => 
                 (case v of 
                     listVal(vals) => 
                        let fun trySplits(vals1,vals2 as v::more_vals) = 
                                 (case valMatchLst([listVal(vals1),listVal(vals2)],[pat1,pat2],sub,sort_sub) of
                                     NONE => trySplits(vals1@[v],more_vals)
                                   | res => res)
                             | trySplits(vals1,[]) = valMatchLst([listVal(vals1),listVal([])],[pat1,pat2],sub,sort_sub)
                        in
                           trySplits([],vals)
                        end
                   | _ => NONE)
               | _ => NONE)

(*----------------------       START REGEX PATS:                ----------------------*)

           | valMatch(v,star as A.reRepPat({pat,code,times,re_form,pos,...}),sub,sort_sub) = 
                 (case v of 
                     listVal(vals) => 
                                 let fun evaluateConstraint(e,(dom1,m1,dom2,m2)) = evalConstraint(e,sub,(dom1,m1,dom2,m2))
                                 in 
                                    (case RE.match(re_form,code,vals,sub,valMatchTermSubOnly(sub,sort_sub),evaluateConstraint,lookUpInOuterEnv) of
                                          SOME((dom1,val_map,dom2,list_val_map),time_elapsed) => 
                                               let val res_sub = consolidateSubs(sub,dom1,val_map,dom2,list_val_map)
                                               in
                                                  SOME(res_sub,sort_sub)
                                               end
                                        | _ => NONE)
                               end
                | _ => NONE)

           | valMatch(v,star as A.reStarPat({pat,code,re_form,...}),sub,sort_sub) = 
                 (case v of 
                     listVal(vals) => 
                                 let (***
                                        val _ = print("\nMatching this re-star pattern: " ^ (A.printPat star))
                                        val _ = print("\n\nThe regular expression for this pattern is: " ^ (RE.reToString(re_form)) ^ "\n\n\n")
                                     ***)
				     fun evaluateConstraint(e,(dom1,m1,dom2,m2)) = evalConstraint(e,sub,(dom1,m1,dom2,m2))
                                 in 
                                    (case RE.match(re_form,code,vals,sub,valMatchTermSubOnly(sub,sort_sub),evaluateConstraint,lookUpInOuterEnv) of
                                          SOME((dom1,val_map,dom2,list_val_map),time_elapsed) => 
                                               let (* val _ = print("\nRE match succeeded in " ^ (Real.toString(time_elapsed)) ^ " seconds...\n")  *)
                                                   val res_sub = consolidateSubs(sub,dom1,val_map,dom2,list_val_map)
                                               in
                                                  SOME(res_sub,sort_sub)
                                               end
                                        | _ => NONE)
                               end
                | _ => NONE)

           | valMatch(v,star as A.rePlusPat({pat,code,re_form,...}),sub,sort_sub) = 
                 (case v of 
                     listVal(vals) => 
                                 let val _ = print("\nMatching this re-plus pattern: " ^ (A.printPat star))
                                     val _ = print("\nThe regular expression for this pattern is: " ^ (RE.reToString(re_form)))
				     fun evaluateConstraint(e,(dom1,m1,dom2,m2)) = evalConstraint(e,sub,(dom1,m1,dom2,m2))
                                 in 
                                    (case RE.match(re_form,code,vals,sub,valMatchTermSubOnly(sub,sort_sub),evaluateConstraint,lookUpInOuterEnv) of
                                          SOME((dom1,val_map,dom2,list_val_map),time_elapsed) => 
                                               let val res_sub = consolidateSubs(sub,dom1,val_map,dom2,list_val_map)
                                               in
                                                  SOME(res_sub,sort_sub)
                                               end
                                        | _ => NONE)
                               end
                | _ => NONE)
           | valMatch(v,star as A.reRangePat({from_pat,to_pat,lo,hi,pos,...}),sub,sort_sub) = 
	        let val c = getValCode(v) 
                in
                    if (c <= hi andalso c >= lo) then
                       SOME(sub,sort_sub)
                    else
                       NONE 
                end
           | valMatch(v,star as A.reOptPat({pat,code,re_form,...}),sub,sort_sub) = 
                 (case v of 
                     listVal(vals) => 
                                 let val _ = print("\nMatching this re-opt pattern: " ^ (A.printPat star))
                                     val _ = print("\nThe regular expression for this pattern is: " ^ (RE.reToString(re_form)))
				     fun evaluateConstraint(e,(dom1,m1,dom2,m2)) = evalConstraint(e,sub,(dom1,m1,dom2,m2))
                                 in 
                                    (case RE.match(re_form,code,vals,sub,valMatchTermSubOnly(sub,sort_sub),evaluateConstraint,lookUpInOuterEnv) of
                                          SOME((dom1,val_map,dom2,list_val_map),time_elapsed) => 
                                               let val res_sub = consolidateSubs(sub,dom1,val_map,dom2,list_val_map)
                                               in
                                                  SOME(res_sub,sort_sub)
                                               end
                                        | _ => NONE)
                               end
                | _ => NONE)

(** end regex pats **)

           | valMatch(v,A.listPat({head_pat,tail_pat,pos}),sub,sort_sub) = 
               (case v of
                   listVal(head_val::more_vals) => 
                        valMatchLst([head_val,listVal(more_vals)],[head_pat,tail_pat],sub,sort_sub)
                 | _ => NONE)

(*----------------------          NAMED PATTERNS:                ----------------------*)

           | valMatch(v,A.namedPat({name,pat,...}),sub,sort_sub) = 
               (case valMatch(v,pat,sub,sort_sub) of 
                   SOME(sub',sort_sub') => SOME(Symbol.enter(sub',name,v),sort_sub')
                 | _ => NONE)

(*----------------------         VAL-OF PATTERNS:                ----------------------*)

           | valMatch(v,A.valOfPat({id={name,pos},lex_ad,...}),sub,sort_sub) = 
                (case lookUpInOuterEnv(name) of
                   SOME(v') => decide(valEq(v,v'),sub,sort_sub)
                 | _ => evError("Matching error: the identifier "^S.name(name)^" is unbound in the "^
                                "environment of the patterns",SOME(pos)))
           | valMatch(v,A.valOfPat1({id={name,pos},num,...}),sub,sort_sub) = 
                (case lookUpInOuterEnv(name) of
                   SOME(v') => decide(valEq(v,v'),sub,sort_sub)
                 | _ => (case coerceValIntoTerm(v) of
                            SOME(t) => (case AT.isNumConstantOpt(t) of 
                                           SOME(anum') => decide(A.athNumEquality(num,anum'),sub,sort_sub)
                                         | _ => NONE)
                          | _ => NONE))

(*----------------------        DISJUNCTIVE PATTERNS:                ----------------------*)

           | valMatch(v,A.disjPat({pats,pos}),sub,sort_sub) = 
                 let fun tryPats([]) = NONE
                       | tryPats(pat::more_pats) = 
                           (case valMatch(v,pat,sub,sort_sub) of
                               NONE => tryPats(more_pats)
                             | res => res)
                 in
                    tryPats(pats)
                 end
(*----------------------        WHERE PATTERNS:                ----------------------*)
           | valMatch(v,A.wherePat({pat,guard,pos}),sub,sort_sub) = 
                  (case pat of 
                      A.splitPat({pats,...}) => 
                       (case pats of
                         [pat1,pat2] => 
                          (case v of 
                             listVal(vals) => 
                                 let fun trySplits(vals1,vals2 as v::more_vals) = 
                                           (case valMatchLst([listVal(vals1),listVal(vals2)],[pat1,pat2],sub,sort_sub) of
                                               NONE => trySplits(vals1@[v],more_vals)
                                             | res as SOME(sub',sort_sub') => (case evaluateExp(guard,SOME(sub')) of
                                                                                  termVal(t) => if isTrueTerm(t) then res  else trySplits(vals1@[v],more_vals) 
                                                                                | propVal(p) => if isTrueTermFromProp(p) then res else trySplits(vals1@[v],more_vals) 
                                                                                | _ => res))
                                       | trySplits(vals1,[]) = (case valMatchLst([listVal(vals1),listVal([])],[pat1,pat2],sub,sort_sub) of
                                                                   res as SOME(sub',sort_sub') => 
                                                                        (case evaluateExp(guard,SOME(sub')) of
                                                                           termVal(t) => if isFalseTerm(t) then NONE else res
                                                                         | propVal(p) => if isFalseTermFromProp(p) then NONE else res
                                                                                | _ => res)
                                                                 | _ => NONE)
                                 in
                                    trySplits([],vals)
                                 end
                           | _ => NONE)
                        | _ => NONE)
                    | _ => (case valMatch(v,pat,sub,sort_sub) of
                              SOME(sub',sort_sub') => (case evaluateExp(guard,SOME(sub')) of
                                                          termVal(t) => if isTrueTerm(t) then SOME(sub',sort_sub') else NONE
                                                        | propVal(p) => if isTrueTermFromProp(p) then  SOME(sub',sort_sub') else NONE
                                                        | _ => SOME(sub',sort_sub'))
                            | _ => NONE))
                                                                          
(*----------------------        COMPOUND PATTERNS:                ----------------------*)

           | valMatch(v as termVal(t),pat as A.compoundPat({head_pat,rest_pats,pos}),sub,sort_sub) = 
               if A.quantVarListPat(pat) then
                  (case coerceValIntoProp(v) of 
                      SOME(p) => doListQuantVars(p,head_pat,hd(rest_pats),tl(rest_pats),sub,sort_sub)
                    | _ => NONE) 
               else
                 (case isGeneralApp(AT.applySortSub(sort_sub,t)) of
                     SOME(fsym,args) =>  
                             let val ath_functor = termConVal(fsym)
                             in
                               if length(rest_pats) = 1 andalso A.isListPat(hd(rest_pats)) then
                                  valMatchLst([ath_functor,listVal(map termVal args)],head_pat::rest_pats,sub,sort_sub)
                               else
                                  valMatchLst(ath_functor::(map termVal args),head_pat::rest_pats,sub,sort_sub)
                             end
                   | _ => NONE)
           | valMatch(v as termConVal(_),pat as A.compoundPat(_),sub,sort_sub) = 
                (case coerceFunSymbolIntoTerm(v) of
                    SOME(t) => valMatch(termVal(t),pat,sub,sort_sub)
                  | _ => NONE)
           | valMatch(propVal(p),pat,sub,sort_sub) = 
	      (case pat of 
		A.compoundPat({head_pat,rest_pats,pos}) => 
                 (if A.quantVarListPat(pat) then doListQuantVars(p,head_pat,hd(rest_pats),
                                                                 tl(rest_pats),sub,sort_sub)
                  else
                    let val pat_list = head_pat::rest_pats
                    in
                      (case P.isAtom(p) of
                          SOME(t) => valMatch(termVal(t),pat,sub,sort_sub)
		        | _ => (case P.isNeg(p) of 
			         SOME(p') => 
				    (case rest_pats of
				       [lpat] => if A.isListPat(lpat) then
						    valMatchLst(
							propConVal(A.notCon)::[listVal([propVal(p')])],
							pat_list,sub,sort_sub)
						 else valMatchLst(
							[propConVal(A.notCon),propVal(p')],pat_list,sub,sort_sub)
				      | _ =>  valMatchLst([propConVal(A.notCon),propVal(p')],pat_list,sub,sort_sub))
                              | _ => 
                                  (case isBinaryProp(p) of
                                     SOME(op_val,args) => 
				      (case rest_pats of
				         [lpat] => if A.isListPat(lpat) then
					  	      valMatchLst(op_val::[listVal(args)],pat_list,sub,sort_sub)
						   else
						      valMatchLst(op_val::args,pat_list,sub,sort_sub)
				        | _ =>  valMatchLst(op_val::args,pat_list,sub,sort_sub))
                                    | _ => (case isQuant(p) of 
                                               SOME(quant_val,var_val,body_val) => 
                                                    valMatchLst([quant_val,var_val,body_val],pat_list,sub,sort_sub)
                                             | _ => NONE))))
                    end)
                | _ => (case P.isConj(p) of
			  SOME(props) => (if A.isListPat(pat) then 
					    valMatch(listVal(map propVal props),pat,sub,sort_sub)
			  		  else NONE)
                        | _ => (case P.isDisj(p) of
				  SOME(props) => if A.isListPat(pat) then 
						    valMatch(listVal(map propVal props),pat,sub,sort_sub)
				  		 else NONE
                                | _ => NONE)))
           | valMatch(_,A.compoundPat(_),_,sort_sub) = NONE                  
           | valMatch(unitVal,A.unitValPat(_),sub,sort_sub) = SOME(sub,sort_sub)
           | valMatch(_,A.unitValPat(_),_,sort_sub) = NONE
           | valMatch(cellVal(v),A.cellPat({pat,...}),sub,sort_sub) = valMatch(!v,pat,sub,sort_sub)
           | valMatch(_,A.cellPat({pat,...}),sub,sort_sub) = NONE 
           | valMatch(_,_,_,_) = NONE
         and valMatchLst([],[],sub,sort_sub) = SOME(sub,sort_sub)
           | valMatchLst(v::more_vals,p::more_pats,sub,sort_sub) =  
               (case valMatch(v,p,sub,sort_sub) of
                   SOME(sub',sort_sub') => let val sort_sub'' = F.composeSubs(sort_sub',sort_sub) 
                                           in
                                             valMatchLst(more_vals,more_pats,sub',sort_sub'')
                                           end
                 | _ => NONE)
           | valMatchLst(_,_,_,_) = NONE
        and valMatchTermSubOnly(sub,sort_sub) =
                   (fn (pat,v) =>
                      (case valMatch(v,pat,sub,sort_sub) of
                          SOME(sub',sort_sub') => SOME(sub')
                          | _ => NONE))
	and doName(sub,A.someParam({name,...}),v) = Symbol.enter(sub,name,v)
          | doName(sub,A.wildCard(_),_) = sub 
        and evalConstraint(e,sub,(dom1,m1,dom2,m2)) = 
                              let val sub' = consolidateSubs(sub,dom1,m1,dom2,m2)
                              in
                                 (case evaluateExp(e,SOME(sub')) of
                                     termVal(t) => isTrueTerm(t)
                                   | propVal(p) => isTrueTermFromProp(p)
                                   | _ => false)
                              end
         and doListQuantVars(p,quant_pat,vars_pat,[body_pat],sub,sort_sub) =
               let val (quant_opt,vars,body) = P.splitVars(p)
                   val var_count = List.length(vars)
                   val ath_term_val_uvar_lst = Basic.doubleMap(termVal,AT.makeVar,vars)
                   fun tryVars(var_vals,count,sub,sort_sub) = 
                       let fun tryVarsAux([],tail_count) = (valMatch(listVal([]),vars_pat,sub,sort_sub),tail_count)
                             | tryVarsAux(var_lst,tail_count) = 
                                   (case valMatch(listVal(var_lst),vars_pat,sub,sort_sub) of 
                                       NONE => tryVarsAux(List.take(var_lst,List.length(var_lst)-1),tail_count+1)
                                     | SOME(sub',sort_sub') => (SOME(sub',sort_sub'),tail_count))
                       in
                          tryVarsAux(var_vals,count)
                       end
                   fun doVarsOn(sub,sort_sub) = 
                          (case tryVars(ath_term_val_uvar_lst,0,sub,sort_sub) of 
                             (SOME(sub',sort_sub'),tail_count) =>
                                let val rest_vars = List.drop(vars,var_count-tail_count)
                                    val newp = makeQuantProp(quant_opt,rest_vars,body)
                                in
                                   valMatch(propVal(newp),body_pat,sub',sort_sub')
                                end
                           | _ => NONE)
               in 
                 (case quant_opt of
                     SOME(q) => (case valMatch(propConVal(q),quant_pat,sub,sort_sub) of
                                    SOME(sub',sort_sub') => doVarsOn(sub',sort_sub')
                                  | _ => NONE)
                   | _ => if A.isSomeNamedQuantPat(quant_pat) then NONE else doVarsOn(sub,sort_sub))
               end
           | doListQuantVars(_,_,_,_,_,_) = NONE 
         fun notEmpty(str) = not(str = "")
     in
        (case valMatch(ath_value,pattern,Symbol.empty_mapping,F.empty_sub) of
            SOME(sub,sort_sub) => if F.isEmptySub(sort_sub) then SOME(sub,sort_sub) 
                                  else let fun f(termVal(t)) = termVal(AT.applySortSub(sort_sub,t))
                                             | f(propVal(p)) = propVal(P.applySortSub(sort_sub,p))
                                             | f(v) = v
                                       in SOME(Symbol.map(SV.recurse f,sub),sort_sub)
                                       end
          | NONE => NONE)
     end

exception IndError of string

fun provesTheRightInductiveCase(res,uvar,body,pat_term,pat_vars,fresh_vars,ded_kind) =
     let val varSortPrinter = makeVarSortPrinter()
	 fun pprint(P) = P.toPrettyString(0,P,varSortPrinter)
	 val starter = if ded_kind = "inductive" then "An " else "A "
         fun emsg(req,gotten) = starter^ded_kind^" subdeduction failed "^ 
                                "to establish\nthe right conclusion. The required conclusion was:\n"^
                                pprint(req)^"\nbut the derived one was: \n"^pprint(gotten)^
                                (if null(pat_vars) then "" else
                                  (if (length(pat_vars) = 1) then
                                      "\n(where the fresh variable "^(ATV.toStringWithSort(hd(fresh_vars)))^
                                      " has replaced the pattern variable "^Symbol.name(hd(pat_vars))^")"
                                   else
                                "\n(where the fresh variables "^Basic.printListStrCommas(fresh_vars,ATV.toStringWithSort)^
                                " have replaced the pattern variables "^
                                Basic.printListStrCommas(pat_vars,fn sym => Symbol.name(sym))^", respectively)"))
         val pat_term' = AT.renameSortVars(pat_term)			
         val required =  P.replace(uvar,pat_term',body)
         val gotten = res
         val result = if P.alEq(required,gotten) then NONE else SOME(emsg(required,gotten))
     in
       result 
     end

fun makePatIntoAthenaTerm(p,uvar_sort,evSortExp) = 
    let val is_named_pat = ref(false)
        val dummy_count = ref(0)
        fun makePat(A.idPat({name,pos,sort_as_exp=NONE,sort_as_fterm,...}),map) = 
              (case Symbol.lookUp(map,name) of
                  NONE => let val v = (case sort_as_fterm of 
                                          NONE => AthTermVar.freshWithPrefix(Symbol.name(name)^"_")
                                        | SOME(sort) => AthTermVar.freshWithSortAndPrefix(Symbol.name(name)^"_",sort))
                          in
                             (AT.makeVar(v),Symbol.enter(map,name,(name,v)))
                          end
                | SOME((_,v)) => evError("Duplicate variable found in constructor pattern: "^
                                         Symbol.name(name),SOME(pos)))

         | makePat(A.idPat({name,pos,sort_as_exp=SOME(se),...}),map) = 
              (case Symbol.lookUp(map,name) of
                  NONE => let val sort_string:string = AthStringToMLString(evSortExp(se))
                              fun isVar(str) = let val str_lst = explode str
	    	        	   	       in not(null(str_lst)) andalso 
					           hd(str_lst) = Names.sort_variable_prefix_as_char
 					       end
                              val v = (case Terms.parseSymTerm(sort_string,isVar) of 
                                          SOME(sort_as_sym_term) => let val fsort = Terms.carbonSymTermToFTerm(sort_as_sym_term)
                                                                    in ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",fsort)
                                                                    end)
                          in
                             (AT.makeVar(v),Symbol.enter(map,name,(name,v)))
                          end
                | SOME((_,v)) => evError("Duplicate variable found in constructor pattern: "^
                                         Symbol.name(name),SOME(pos)))

	  | makePat(A.anyPat(_),map) = let val v = ATV.fresh()
                                           val dum_sym = Symbol.symbol(S.name(A.dummy_sym)^(Int.toString(Basic.incAndReturn(dummy_count))))
                                       in
                                           (AT.makeVar(v),Symbol.enter(map,dum_sym,(dum_sym,v)))
                                       end
	  | makePat(A.namedPat({pat,...}),map) = let val _ = is_named_pat := true
                                                 in
                                                    makePat(pat,map)
                                                 end
          | makePat(A.funSymPat({name,sort_opt=NONE,sort_as_exp=NONE,arity=0,pos,...}),map) = (AT.makeApp(name,[]),map)
          | makePat(A.funSymPat({name,sort_opt=SOME(sort),arity=0,pos,...}),map) = (AT.makeSortedConstant(name,sort),map)
          | makePat(A.funSymPat({name,sort_opt=NONE,sort_as_exp=SOME(se),arity=0,pos,...}),map) = 
              let val sort_string:string = AthStringToMLString(evSortExp(se)) 
                  fun isVar(str) = let val str_lst = explode str
  	        	   	   in not(null(str_lst)) andalso 
			              hd(str_lst) = Names.sort_variable_prefix_as_char
                                   end
                  val sort = (case Terms.parseSymTerm(sort_string,isVar) of 
                                 SOME(sort_as_sym_term) => Terms.carbonSymTermToFTerm(sort_as_sym_term))
               in
                 (AT.makeSortedConstant(name,sort),map)
               end
          | makePat(A.numPat({ath_num,...}),map) = (AT.makeNumTerm(ath_num),map)
          | makePat(A.constantMetaIdPat({name:symbol,...}),map) = (AT.makeIdeConstant(Symbol.name(name)),map)
          | makePat(A.compoundPat({head_pat=A.funSymPat({name,pos,...}),rest_pats,...}),map) =
               let val (terms,map') = makePatLst(rest_pats,[],map)
                   val (res,theta) = AT.makeAppAndReturnSortSub(name,terms)
               in                   
                  (res,map')
               end
         | makePat(_,_) = evError("Invalid constructor pattern",SOME(A.posOfPat(p)))
        and  
            makePatLst([],terms,map) = (rev(terms),map)
          | makePatLst(p::more,terms,map) = 
                let val (t,map') = makePat(p,map)
                in
                  makePatLst(more,t::terms,map')
                end
    in
      let val res as (t,map) = makePat(p,Symbol.empty_mapping)  
				handle Basic.FailLst([_,msg]) => 
				  evError("Could not infer a sort for this pattern:\n"^
					   A.printPat(p)^".\n\n"^(Basic.lparen)^(msg)^(Basic.rparen),
					  SOME(A.posOfPat(p)))
          val _ = if not(F.isInstanceOf(uvar_sort,AT.getSort(t))) then 
                     evError("The pattern: `"^(A.printPat(p))^"' is of sort "^(F.toStringDefault(AT.getSort(t)))^
                             ".\nA pattern of sort "^(F.toStringDefault(uvar_sort))^" was expected instead",
                             SOME(A.posOfPat(p)))
                   else ()
	  val fvars = AT.getVars(t)
	  val pat_ids_paired_with_fvars = Symbol.listImages(map)
	  val pat_ids = List.map #1 pat_ids_paired_with_fvars
	  val new_fvars = List.map (fn (pid,v) => 
					(case Basic.findInList(fvars,fn v' => ATV.nameEq(v,v')) of
					   SOME(v') => v'
					 | _ => genError("Unable to find a fresh variable in an inductive pattern.",
							 SOME(A.posOfPat(p))))) pat_ids_paired_with_fvars
	  val pat_ids_paired_with_fvars' = Basic.zip(pat_ids,new_fvars)
      in
          (t,pat_ids_paired_with_fvars',!is_named_pat)
      end
    end

type iarm_type = {uvar:AthTermVar.ath_term_var,
     	       	  uvar_sort:FTerm.term,
		  uprop:P.prop,
                  uv_pattern:AT.term} 

fun getInductiveHypotheses(iarm_stack,ath_vars,current_goal,current_pat_term) = 
      let fun f(stack,res) =
            if LStack.isEmpty(stack) then 
	       res
            else
               let val iarm:iarm_type as {uvar,uvar_sort,uprop,uv_pattern} = LStack.top(stack)  
                   val tail_stack = LStack.pop(stack)
                   val real_uprop = P.replace(uvar,uv_pattern,uprop)
                   val new_pat_term = uv_pattern
                   fun checkSub(sub,pat_term) = 
                         let val supp = AT.supp(sub)
                             val pat_vars = AT.getVars(uv_pattern)
                             val cond1 = List.all (fn v => Basic.isMemberEq(v,pat_vars,ATV.athTermVarEq)) supp
                             val cond2 = List.all (fn v => AT.termEq(AT.applySub(sub,AT.makeVar(v)),current_pat_term)) supp
                         in 
                            cond1 andalso cond2
                         end
                   fun doVars([],res) = res
                     | doVars(v::more,res) = 
                            let val vsort = ATV.getSort(v) 
			        val var_sort = vsort 
                            in                   
			      if FTerm.isInstanceOf(var_sort,uvar_sort) then
                                 (case P.match(current_goal,real_uprop) of 
                                     SOME(sub) => if checkSub(sub,current_pat_term) then 
                                                     let val ihyp = P.replace(uvar,AT.makeVar(v),uprop)
 				                                    handle Basic.FailLst(msgs) => 
 						                           Basic.failLst(("A fresh variable that replaced the universally "^
						   	                                  "quantified variable in the inductive goal was "^
						   	                                  "not of the correct sort")::msgs)
                                                     in
		 		                        doVars(more,ihyp::res)
				                     end
                                                  else doVars(more,res)
                                  | _ => doVars(more,res))
			      else
				 doVars(more,res)
			    end
                   val ind_hypotheses = doVars(ath_vars,[])
               in
                  f(tail_stack,res@ind_hypotheses)
               end       
      in
         if LStack.isEmpty(iarm_stack) then [] else f(LStack.pop(iarm_stack),[])
      end

fun enterLst(table,sym_list,val_list) = 
       let fun f([],[],tab) = tab
             | f(s::more1,v::more2,tab) = f(more1,more2,Symbol.enter(tab,s,v))
             | f(_,_,_) = Basic.fail("Incorrect use of enterLst")
       in
          f(sym_list,val_list,table)
       end        

fun reportException(ex) = 
 (case ex of
    EvalError(msg,pos_opt) => print(msg)
   | A.SyntaxError(msg,SOME(pos)) => print((A.posToString pos)^": Error, "^msg^".")
   | A.SyntaxError(msg,NONE) => print("Error, "^msg^".")
   | A.LexError(msg,SOME pos) => print((A.posToString pos)^": Error, "^msg^".")
   | A.LexError(msg,NONE) => print("Error, "^msg^".")
   | Basic.Fail(msg) => print(msg) 
   | Basic.FailLst(msgs) => print(Basic.failMsgsToStr(msgs))
   | Data.GenEx(str) => print(str)
   | Data.ObTypeCheckFailure => print("\nIndeterminate sort error.\n")
   | _ => print("\nIndeterminate error.\n"))

fun enterParamValLst(table,param_list,val_list) = 
       let fun f([],[],tab) = tab
             | f((A.someParam({name,...}))::more1,v::more2,tab) = f(more1,more2,Symbol.enter(tab,name,v))
             | f((A.wildCard(_))::more1,_::more2,tab) = f(more1,more2,tab)
             | f(_,_,_) = primError("Wrong number of arguments given")
       in
          f(param_list,val_list,table)
       end        

fun enterParamValLstWithPositionalErrorChecking(table,param_list,val_list,msg,pos) = 
       let fun f([],[],tab) = tab
             | f((A.someParam({name,...}))::more1,v::more2,tab) = f(more1,more2,Symbol.enter(tab,name,v))
             | f((A.wildCard(_))::more1,_::more2,tab) = f(more1,more2,tab)
             | f(_,_,_) = evError("Wrong number of arguments ("^Int.toString(length(val_list))^
                                   ") given "^msg^"---exactly "^argNumToString(length(param_list))^" required",
                                  SOME(pos))
       in
          f(param_list,val_list,table)
       end        


(*******************************************************************************************)
(*                                                                                         *)
(*                        Evaluator without expansion                                      *)
(*                                                                                         *)
(*******************************************************************************************)

fun lookUpBasic(e,mod_names,sym) = 
    let fun look([],valEnv({val_map,...})) = Symbol.lookUp(val_map,sym)
          | look(mod_name::rest,valEnv({mod_map,...})) = 
              let val res = (case Symbol.lookUp(mod_map,mod_name) of
                               SOME({env,...}:module) => look(rest,env)
                              | _ => NONE)
              in
                res 
              end
    in
       look(mod_names,e)
    end

fun flookUp(valEnv({val_map,...}),msym) = Symbol.lookUp(val_map,MS.lastName(msym))

fun lookUp(e as valEnv({val_map,...}),mod_names,sym_name) = 
      (case mod_names of
           msym::rest => if Symbol.symEq(msym,Names.top_module_symbol) then lookUpBasic(!top_val_env_backup,rest,sym_name)
                         else lookUpBasic(e,mod_names,sym_name)
        | _ => Symbol.lookUp(val_map,sym_name))

fun lookUp(e as valEnv({val_map,...}),mod_names,sym_name) = 
      if not(null(mod_names)) andalso Symbol.symEq(hd mod_names,Names.top_module_symbol) then lookUpBasic(!top_val_env_backup,tl mod_names,sym_name)
      else lookUpBasic(e,mod_names,sym_name)

fun lookUpModuleBasic(e,mod_names,sym_name) = 
  let fun look([],valEnv({mod_map,...})) = Symbol.lookUp(mod_map,sym_name)
        | look(mod_name::rest,valEnv({mod_map,...})) = 
              (case Symbol.lookUp(mod_map,mod_name) of
                  SOME({env,...}:module) => look(rest,env)
                | _ => NONE)
  in
     look(mod_names,e)
  end

fun lookUpModule(e,msym) = 
  let val (mod_names,sym_name) = MS.split(msym)
  in
     lookUpModuleBasic(e,mod_names,sym_name)
  end

fun noTopReferences(msym) = 
      if (List.exists (fn sym => S.symEq(sym,Names.top_module_symbol)) (MS.modules msym)) 
      then evError("Invalid Top reference.",NONE) else () 
      
      
fun makeEnv0(msyms:MS.mod_symbol list,env) = 
  let fun partition(msyms) = 
             let fun loop([],res) = res
                   | loop(msym::more,res as (syms,mapping)) = 
                        let val (mods,sym) = MS.split(msym)
                        in
                          (case mods of
                              [] => loop(more,(sym::syms,mapping))
                            | mod_name::more_mods => 
                                let val mod_sym = MS.makeModSymbol(more_mods,sym,Symbol.symbol ((Basic.printListStr(more_mods,Symbol.name,"."))^(Symbol.name sym)))
                                in
                                   (case Symbol.lookUpWD(mapping,mod_name) of
                                       SOME(mod_syms) => loop(more,(syms,Symbol.enterWD(mapping,mod_name,MS.add(mod_sym,mod_syms))))
                                     | _ => loop(more,(syms,Symbol.enterWD(mapping,mod_name,MS.singleton(mod_sym)))))
                                end)
                        end
             in
               loop(msyms,([],Symbol.empty_mappingWD))
             end
      val (msyms_without_mods,mapping) = partition(msyms)
      val msym_lists_with_mods = List.map (fn (sym,sym_set) => (sym,MS.listModSymbols(sym_set))) (Symbol.listSymbolsAndImagesWD mapping)
      val (vmap,mod_map) = getValAndModMaps(env)
      fun processMsymListWithMods(module_name:Symbol.symbol,msym_list) = 
              let val _ = List.app noTopReferences msym_list 
              in
                    (case Symbol.lookUp(mod_map,module_name) of
                        SOME(m:SV.module as {env=env',...}) => 
                           let val new_env:SV.value_environment = makeEnv0(msym_list,env')
                           in
                              (module_name,new_env)
                           end
                       | _ => if Symbol.symEq(module_name,Names.top_module_symbol) then
                                  (module_name,makeEnv0(msym_list,!top_val_env_backup))
                              else Basic.fail("\nUnable to look up the following module: "^(Symbol.name module_name)^"\n"))
              end
      fun makeValMap([],res) = res
        | makeValMap(sym::more,res) = 
              (case Symbol.lookUp(vmap,sym) of
                  SOME(v) => makeValMap(more,Symbol.enter(res,sym,v))
                | _ => makeValMap(more,res))
      val vm = makeValMap(msyms_without_mods,Symbol.empty_mapping)
      fun makeModMap([],res) = res
        | makeModMap((module_name,module_env)::more,res) =   
           makeModMap(more,Symbol.enter(res,module_name,{mod_name=A.msym(module_name),open_mod_directives=[],env=module_env}))
  in
     SV.valEnv({val_map=vm,mod_map=mod_map})
  end

fun makeEnv(msyms:MS.set,env) = 
          (if MS.isMember(N.mlookUpEnvBindingFun_symbol,msyms) then ref(env)
           else if (List.exists (fn m => MS.isMember(m,msyms)) Names.module_fun_msymbols)
                then (case (makeEnv0(MS.listModSymbols(msyms),env),!top_val_env_backup) of
                         (valEnv({val_map=vm,mod_map}),valEnv({val_map,mod_map=mm})) => ref(valEnv({val_map=vm,mod_map=mm})))
                else ref(makeEnv0(MS.listModSymbols(msyms),env))) handle _ => (ref env)


fun makeEnv(msyms:MS.set,env) = 
          (if MS.isMember(N.mlookUpEnvBindingFun_symbol,msyms) then ref(env)
           else  ref(makeEnv0(MS.listModSymbols(msyms),env))) handle _ => (ref env)

fun updateLastValueAndReturn(v) = (updateTopValEnv(top_val_env,N.last_value_symbol,v,true);v)

fun errorMsgForABCheck(P,meth_name,pos_opt) = 
  let val str = Prop.toPrettyString(0,P,makeVarSortPrinter())
      val msg_tail = if Util.small(str,40) then str^" is not in the assumption base"
                     else str^"\nis not in the assumption base"
      val msg = "Failed application of "^meth_name^"---the sentence\n"^msg_tail
  in
     evError(msg,pos_opt)
  end

fun checkAbMembers(prop_and_pos_lst,ab,meth_name) = 
      let fun f([]) = ()
            | f((P,pos)::more) = if ABase.isMember(P,ab) then f(more) else errorMsgForABCheck(P,meth_name,SOME pos)
      in
         f(prop_and_pos_lst)
      end

fun checkAbMembersNoPosGeneral(props,g,meth_name) = 
      let fun f([]) = ()
            | f(P::more) = if g(P) then f(more) else errorMsgForABCheck(P,meth_name,NONE)
      in
         f(props)
      end

fun checkAbMembersNoPos(props,ab,meth_name) = checkAbMembersNoPosGeneral(props,fn p => ABase.isMember(p,ab),meth_name)

(** This could be easily implemented as checkOneAbMemberNoPos([P],ab,meth_name) but here we avoid forming the singleton list: **)

fun checkOneAbMemberNoPos(P,ab,meth_name) = if ABase.isMember(P,ab) then () else errorMsgForABCheck(P,meth_name,NONE)
      
fun checkAbMembersOnePos(props,pos,ab,meth_name) = 
      let fun f([]) = ()
            | f(P::more) = if ABase.isMember(P,ab) then f(more) else errorMsgForABCheck(P,meth_name,SOME pos)
      in
         f(props)
      end
      
datatype lambda = FunClos of {clos_name:string,def_pos:pos,def_file:string} |
                  MethClos of {clos_name:string,def_pos:pos,def_file:string} |
                  PrimMethClos of {clos_name:string,def_pos:pos,def_file:string} |
                  FunVal of {name:string} |
                  MethVal of {name:string}

datatype stack_frame = frame of {call_pos:pos,call_file:string,lambda:lambda} | 
                       detailedFrame of {call_pos:pos,call_file:string,lambda:lambda,arg_vals:value list}

fun locString(pos,file) = (A.posToString pos)

fun callString(FunClos({clos_name,def_pos,def_file})) = 
      "calling procedure "^clos_name^" (defined at "^A.posToString(def_pos)^")"
  | callString(MethClos({clos_name,def_pos,def_file})) = 
      "calling method "^clos_name^" (defined at "^A.posToString(def_pos)^")"
  | callString(PrimMethClos({clos_name,def_pos,def_file})) = 
      "calling primitive method "^clos_name^" (defined at "^A.posToString(def_pos)^")"
  | callString(FunVal({name})) = "calling procedure "^name 
  | callString(MethVal({name})) = "calling method "^name 

fun printStackFrame(fr) = 
  let fun printArgs([],_) = ()
        | printArgs(v::more,i) = 
            (print("ARGUMENT "^Int.toString(i)^": ");printValWithTypedStrings(v);printArgs(more,i+1))
      fun printSep() = print("=================================================================================")
      fun f(frame({call_pos,call_file,lambda})) = 
             (print("\n");print(locString(call_pos,call_file)^", "^callString(lambda)))
        | f(detailedFrame({call_pos,call_file,lambda,arg_vals})) = 
           (print("\n");print(locString(call_pos,call_file)^", "^callString(lambda)^" WITH:\n");
            printArgs(arg_vals,1);printSep())
  in
     f(fr)
  end           

fun printFrameLst(frame_lst) = 
      let fun f([]) = ()
            | f(fr::more) = (printStackFrame(fr);f(more))
      in
         f(frame_lst)
      end

val call_stack: stack_frame LStack.stack ref = ref(LStack.empty)

fun getDisjuncts(P) = case P.isDisj(P) of
			SOME(props) => props
		      | _ => []

fun foldConditionals(assumptions,conclusion) = 
  let fun doIfs([]) = conclusion
        | doIfs(p1::rest) = P.makeConditional(p1,doIfs(rest))
  in
        doIfs(assumptions)
  end

fun makeBinaryProp(pcon,p1,p2) = 
    (case pcon of
        A.ifCon => P.makeConditional(p1,p2)
      | A.iffCon => P.makeBiConditional(p1,p2)
      | _ => Basic.fail("makeBinaryProp error"))


fun getFrontQuantVars(P) = 
 let fun f(P,"a",res) =
	       (case P.isUGen(P) of 
		  SOME(v,Q) => f(Q,"a",v::res)
	        | _ => res)
       | f(P,"e",res) =
	       (case P.isEGen(P) of 
		  SOME(v,Q) => f(Q,"e",v::res)
	        | _ => res)
       | f(P,"u",res) =
	       (case P.isEGenUnique(P) of 
		  SOME(v,Q) => f(Q,"u",v::res)
	        | _ => res)
       | f(_,_,res) = res
 in
   (case P.isQuant(P) of
       SOME(A.forallCon,_,_) => f(P,"a",[])
     | SOME(A.existsCon,_,_) => f(P,"e",[])
     | SOME(A.existsUniqueCon,_,_) => f(P,"u",[])
     | _ => [])
 end

fun isBooleanFalse(P) =
  (case P.isAtom(P) of
      SOME(t) => AT.termEq(t,false_term)
    | _ => false)

fun addFrame(f:stack_frame) = call_stack := LStack.push(f,!call_stack)

fun printCallStack() = printFrameLst(LStack.list(!call_stack))

fun testEnv(env) = 
let val test = Symbol.lookUp(!env,Symbol.symbol("add"))
in
  (case test of 
      SOME(_) => ()
     | _ => print("\nNOTBOUND\n"))
end

fun getTermsWithCoercion(val_lst,errorMsg,coerceValIntoTerm) = 
  let fun getTerms([],_,results) = rev results
        | getTerms((v,pos)::rest,i,results) = 
            (case coerceValIntoTerm(v) of
                SOME(t) => (case AT.isConstant(t) of 
			       SOME(name) =>  let val (_,sort,is_poly,involves_pred_based_sorts) = Data.getSignature(name)
					      in
						if FTerm.termEq(sort,AT.getSort(t)) then 
						   let val t' = AT.makeSortedConstantAux(name,sort,is_poly)
						   in
 						      getTerms(rest,i+1,t'::results)
						   end
						else
						   getTerms(rest,i+1,t::results)
					       end
                             | _ => getTerms(rest,i+1,t::results))
              | _ => evError(errorMsg(i,v),SOME(pos)))
  in 
    getTerms(val_lst,1,[])
  end

fun getTermVars(vals,con,pos) = 
  let fun f([],res,_) = rev(res)
        | f(v::more,res,i) = (case coerceValIntoTerm(v) of
                                      SOME(t) => (case AT.isVarOpt(t) of
                                                     SOME(var) => f(more,var::res,i+1)
 						   | _ => evError(wrongArgKind(A.propConToString(con),i,varLCType,v),
							          SOME(pos)))
                                    | _ => evError(wrongArgKind(A.propConToString(con),i,varLCType,v),SOME(pos)))
   in
      f(vals,[],1)
   end

fun getTermVar(v) = 
  (case coerceValIntoTerm(v) of
     SOME(t) => case AT.isVarOpt(t) of
                    SOME(var) => var)

fun deleteFile(fname) = OS.FileSys.remove(fname) 

fun augmentWithMap(valEnv({val_map,mod_map}),map) =  
    valEnv({val_map=Symbol.augment(val_map,map),mod_map=mod_map})

fun augmentWithBothMaps(valEnv({val_map,mod_map}),mod_map',val_map') =  
    valEnv({val_map=Symbol.augment(val_map,val_map'),
            mod_map=Symbol.augment(mod_map,mod_map')})

fun checkOpConstraint((actual_arity,actual_prec),(arity,prec),error) = 
     if actual_arity = arity then ()
     else error()

fun makeError(msg,NONE) = primError(msg)
  | makeError(msg,p) = evError(msg,p)

type call_site = string * A.position

fun callSiteToString(name,pos) = 
     if name = "" then "Calling (anonymous closure) at "^(A.posToString(pos))
     else "Calling " ^ name ^ " at "^(A.posToString(pos))

structure Drop_List = MakeList(type element = call_site)

val _ = Drop_List.setCapacity(!(Options.first_call_stack_chunk_size_limit))

val empty_pos:A.position = {file="",line=(~1),pos=(~1)}

val empty_call_site = ("",empty_pos)

fun makeEmptyPosStack() = Drop_List.makeList(empty_call_site,!(Options.call_stack_size))

val pos_stack = makeEmptyPosStack()

fun resetPosStack() = Drop_List.assign(pos_stack,makeEmptyPosStack())

fun addPos(site:call_site) = Drop_List.prepend(site,pos_stack)

fun chooseAthenaErrorPositionAux(stack as (call_site as (name,(p as {line,pos,file})))::rest) = 
       if line < 0 orelse builtIn(file) then chooseAthenaErrorPositionAux(rest)
       else 
           let val same_file_positions = getSameFilePositions(stack)
               val sorted_positions = Basic.mergeSort(same_file_positions,fn ((_,p1),(_,p2)) => not(Pos.lexCompare(p1,p2)))
           in
              (case sorted_positions of
                  p::_ => p
                | _ => empty_call_site)
           end
  | chooseAthenaErrorPositionAux([]) = empty_call_site

fun chooseAthenaErrorPosition() = 
    let val stack' = Drop_List.toList(pos_stack,{with_first_part=true})
    in
      chooseAthenaErrorPositionAux(stack')
    end

fun getSmallCallStack(stack) = 
  let val first_chunk = Drop_List.firstPart(stack)
      val top_portion_len = !(Options.top_call_stack_portion_length)
      fun allBasic(results) = List.all (fn (_,{file,line,pos}) => builtIn(file)) results
  in
    if not(Drop_List.firstPartFilled(stack)) then ([],[],false,first_chunk)
    else let val stack' = Drop_List.toList(stack,{with_first_part=false})
             fun loop(stack as (call_site as (name,(p as {line,pos,file})))::rest,results,flag as {skip_basic:bool}) = 
                   if line < 0 then loop(rest,results,flag)
                   else if builtIn(file) then 
                           (if skip_basic then loop(rest,results,flag) else loop(rest,call_site::results,flag))
                        else loop(rest,call_site::results,flag)
              | loop([],results,_) = rev(results)
             val stack'' = loop(stack',[],{skip_basic=false})
             val (main_results,remainder) = Basic.takeAndSplit(stack'',top_portion_len)
             val (main_results',middle,middle_gap) = 
                                if allBasic(main_results) then
                                    let val low_stack = Basic.take(loop(stack'',[],{skip_basic=true}),!(Options.top_call_stack_portion_length))
                                    in
                                      (case low_stack of
                                         p1::p2::rest => if null(rest) then (Basic.take(main_results,top_portion_len-2),[p1,p2],false)
                                                         else (Basic.take(main_results,top_portion_len-2),[p1,p2],true)
                                       | p1::rest => if null(rest) then (Basic.take(main_results,top_portion_len-1),[p1],false)
                                                     else (Basic.take(main_results,top_portion_len-1),[p1],true)
                                       | _ => (main_results,[],false))
                                    end
                                 else 
                                      if length(remainder) >= top_portion_len then
                                         (main_results,[],false)
                                      else (main_results@remainder,[],false)
         in
            (main_results',middle,middle_gap,first_chunk)
         end
  end

fun summarizeCallStack(pos_stack) = 
  let val (main,middle,middle_gap,first) = getSmallCallStack(pos_stack)
  in
     if null(main) andalso null(first) then ""
     else
      let val main_str = Basic.printListStr(main,callSiteToString,"\n")
          val first_str = Basic.printListStr(first,callSiteToString,"\n")
          val middle_str = Basic.printListStr(middle,callSiteToString,"\n")
          val dots = "\n...\n"
          val title = "\nCall stack summary (more recent calls at the top):\n\n"
      in
        if null(main) then 
           let val title' = "\nCall stack:\n\n"
           in 
              title'^first_str^"\n"
           end 
        else if null(middle) then title^main_str^dots^first_str^"\n"
             else let val dots' = if middle_gap then dots else ""
                  in
                     title^main_str^dots^middle_str^dots'^first_str^"\n"
                  end
      end
  end

fun summarizeTopCallStack() = summarizeCallStack(pos_stack)

fun massage(t) = 
  (case AT.isConstant(t) of 
      SOME(name) =>  let val (_,sort,is_poly,_) = Data.getSignature(name)
                         val is_lifted_fsym = D.isLiftedFSym(name)
                         val first_res = if is_lifted_fsym then SOME(name) else NONE
                     in
                       if FTerm.termEq(sort,AT.getSort(t)) then (first_res,AT.makeSortedConstantAux(name,sort,is_poly))
                       else (first_res,t)
                     end
    | _ => (NONE,t))

fun liftArg(arg_val,expected_arity,pos_opt) = 
   (case coerceValIntoTermCon(arg_val) of
       SOME(regFSym(fsym)) => 
         if D.fsymArity(fsym) = expected_arity then 
            (* Lift fsym to its reified version fsym^ as a constant term *)
            let val fsym_name = D.fsymName(fsym)
                val lifted_fsym_name = D.liftMSName(fsym_name)
                val lifted_term_constant = AT.makeConstant(lifted_fsym_name)
            in 
              lifted_term_constant
            end
         else evError(wrongArgKindExpectationOnly(termLCType,arg_val),pos_opt)
     | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val),pos_opt))

fun exceptionToString(e) =
 let fun f(ErrorMsg.ParseError((l,p),str)) = ("\n"^A.posToString({line=l,file=(!Paths.current_file),pos=p})^": Parsing error, "^str^".\n")
       | f(A.LexError(str,SOME(pos))) = ("\n"^A.posToString(pos)^": Lexical error, "^str^".\n")
       | f(A.LexError(str,NONE)) = ((!Paths.current_file)^": Lexical error at end of file, "^str^".\n")
       | f(A.SyntaxError(str,SOME(pos))) = ("\n"^(A.posToString pos)^": Syntax error: "^str^".\n")
       | f(A.SyntaxError(str,NONE)) = ("\n"^(!Paths.current_file)^": Syntax error: "^str^".\n")
       | f(AthenaError(msg)) = ("\n"^msg^"\n")
       | f(EvalError(x)) = makeErrorWithPosInfo(x)
       | f(Data.GenEx(str)) = str^"\n"
       | f(GenEx(x as (msg,pos_opt))) = makeErrorWithPosInfo(x)
       | f(Basic.Fail(str)) = "\n"^str^"\n"
       | f(Basic.FailLst(strings)) = "\n"^(Basic.printListStr(strings,fn x => x, "\n"))^"\n" 
       | f(_) = "\nUnknown error: "^(exnMessage e)
 in
   f e
 end
     
val (lp,rp,space) = ("(",")"," ")

          fun prefix() = "Invalid first argument given to the by-induction-on form. "^
                         "In every deduction\nof the form (by-induction F D), the "^
                         "value of F must be a univerally quantified sentence (forall v P)"  
          fun msg1(n,var_str,P_str,obtype) = prefix()^".\nIn addition, the sort of v in P must be a structure."^ 
                                   " But here\n"^"v and P are "^var_str^" and "^P_str^
                                   ", respectively, where "^var_str^" in "^P_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a structure"
          fun msg2(str1,str2) = "Ill-formed induction---the given patterns do not exhaust\nthe "^
                                "structure "^str1^". Here is a counter-example: "^str2
          fun msg3(v) = ". But here F was a "^valLCTypeAndString(v)

(** Main interpreter: **)

val (evalExp,
     evalDed,
     evalPhrase,
     evalClosure,
     evalMethodClosure,
     evalMethodApp,
     makeEvalExpFunction,
     doSupposeAbsurd,
     evalDCheckClauses,
     coercePositionlessValsIntoProps,
     coercePositionedValsIntoProps,
     coercePositionedValsIntoPropsAndPositionCopies) =
let 
    val iarm_stack:iarm_type LStack.stack ref = ref(LStack.empty)
    fun initIndStack() = iarm_stack := LStack.empty
    fun initCallStack() = call_stack := LStack.empty 
    fun evExp(expression,env,ab) = 
      (case expression of
        A.idExp(id as {sym,no_mods,...}) => 
           (case !env of
             (e as (valEnv({val_map,...}))) => 
                 let val res = if no_mods then Symbol.lookUp(val_map,sym) else lookUp(e,#mods(id),sym)
                 in
                   (case res of
                       SOME(v) => v
                      | _ => evError("Could not find a value for "^(MS.name (#msym(id))),SOME(#pos(id))))
                 end)
     | A.unitExp(_) => unitVal
     | app_exp as A.BAppExp({proc,arg1,arg2,pos}) => 
      let val head_val = evPhrase(proc,env,ab)
      in
        (case head_val of
             closBFunVal(body,p1,p2,clos_env as ref(valEnv({val_map,mod_map,...})),{name,...}) =>                         
                   let val v1 = evPhrase(arg1,env,ab)
                       val v2 = evPhrase(arg2,env,ab)
                       val vm = Symbol.enter(Symbol.enter(val_map,p1,v1),p2,v2)
                       val _ = addPos (!name,pos)
                   in 
                      evExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab)                   
                   end
           | termConVal(regFSym(some_fsym)) =>
                   (let val name = D.fsymName(some_fsym)
                        val arg_val1 = evPhrase(arg1,env,ab)              
                        val arg_val2 = evPhrase(arg2,env,ab)
			val (expected_arg_sorts,result_sort,is_poly,_) = Data.getSignature(name)
                        val [arg_1_expected_sort,arg_2_expected_sort] = 
			    let val N = length(expected_arg_sorts)
                            in
 			       if N = 2 then 
                                  [hd(expected_arg_sorts), hd(tl(expected_arg_sorts))] 	     
                               else evError(wrongArgNumber(MS.name(D.fsymName(some_fsym)),2,N),SOME(pos))
                            end
                        val term_arg2 =  (case coerceValIntoTerm(arg_val2) of
                                             SOME(t) => (case AT.isConstant(t) of 
                 			                   SOME(name) =>  if FTerm.termEq(result_sort,AT.getSort(t)) then 
 					                                     AT.makeSortedConstantAux(name,result_sort,is_poly)
                                                                          else t
                                                         | _ => t)                                 
                                            | _ => (case D.funSortArity(arg_2_expected_sort) of 
                                                        SOME(K) => liftArg(arg_val2,K,SOME pos)
  	  					      | _ =>  evError(wrongArgKindExpectationOnly(termLCType,arg_val2),SOME(pos))))
                    in 
                      if MS.modSymEq(name,Names.app_fsym_mname) then  
                           (*** Binary "app" case: (app E1 E2). If E1 is EITHER a regular function symbol f:[S] -> T OR a constant of the form f^:(Fun S T), 
                                then just return (f E2). Otherwise, assuming that E1 evaluates to a term t1 of sort (Fun 'S 'T), which could even be some 
				term variable ?foo:(Fun 'S 'T), and that E2 evaluates to a term t2 of sort 'S, return the term (app t1 t2).  qqq 
                            ***)
                           (case coerceValIntoTerm(arg_val1) of
                               SOME(t) => let val (lifted_fsym_opt,term_arg1) = massage(t)
                                             (**** If term_arg1 is a term constant of sort (Fun S T) that is lifted, i.e., of the form f^, then we should just return (f term_arg2)  ****)
                                              val _ = (case F.isApp(AT.getSort(t)) of 
                                                        SOME(_,expected_functor_arg_sorts) => 
                                                             let val expected_arity = length(expected_functor_arg_sorts)-1
                                                             in
                                                               if not(expected_arity = 1) then
                                                                    let val msg = "Unable to infer a sort for the term: \n"^(AT.fauxTermToPrettyString(0,name,[term_arg1,term_arg2]))
                                                                    in
                                                                       evError(msg,SOME(pos))
                                                                    end
                                                               else ()
						             end
                                                      | _ => evError("Expected a functional sort with arity 1 here.",SOME(A.posOfPhrase(arg1))))
					      val term_res = (case lifted_fsym_opt of 
                                                                 SOME(fsym) => applyUnaryTermConstructor(MS.unlift(fsym),term_arg2,pos)
							       | _ => applyBinaryTermConstructor(name,term_arg1,term_arg2,pos))
                                          in
                                             termVal(term_res)
                                          end 
                             | _ => (case coerceValIntoTermCon(arg_val1) of 
                                         SOME(regFSym(fsym)) => 
                                                termVal(applyUnaryTermConstructor(D.fsymName(fsym),term_arg2,pos))
                                        | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val1),SOME(pos))))
                      else
                         let val term_arg1 = let 
                                             in 
                                                (case coerceValIntoTerm(arg_val1) of
                                                    SOME(t) => #2(massage(t))
                                                  | _ => let 
                                                         in
                                                           (case D.funSortArity(arg_1_expected_sort) of 
                                                               SOME(K) => liftArg(arg_val1,K,SOME pos)
                                                             | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val1),SOME(pos)))
                                                         end)
                                             end
                             val term_res = applyBinaryTermConstructor(name,term_arg1,term_arg2,pos)
                         in
                           termVal(term_res)
                         end
                  end)
           | propConVal(con) => 
                  if A.isQuantPropCon(con) then
 	             let val pval = evPhrase(arg2,env,ab)
 	             in
	               (case coerceValIntoProp(pval) of
 	                  SOME(p) => (let val var_val = evPhrase(arg1,env,ab)
	                                  val term_var = (getTermVar var_val) handle _ => evError(wrongArgKind(A.propConToString(con),1,varLCType,var_val),SOME(pos))
	                                  val res_prop = makeQuantProp(SOME con,[term_var],p)
						           handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
	                              in
	                                propVal(res_prop) 
	                              end)
	                 | _ => evError(wrongArgKind(A.propConToString(con),2,propLCType,pval),SOME(A.posOfPhrase(arg2))))
	             end
                  else
 	                 let val arg_val1 = evPhrase(arg1,env,ab)
                             val arg_val2 = evPhrase(arg2,env,ab)
                             val prop1 = (case coerceValIntoProp(arg_val1) of  
                                             SOME(P) => P
                                           | _ => evError(wrongArgKind(valLCTypeAndStringNoColon(propConVal(con)),1,propLCType,arg_val1),SOME(A.posOfPhrase(arg1))))
                             val prop2 = (case coerceValIntoProp(arg_val2) of  
                                             SOME(P) => P
                                           | _ => evError(wrongArgKind(valLCTypeAndStringNoColon(propConVal(con)),2,propLCType,arg_val2),SOME(A.posOfPhrase(arg2))))
                             val res = (case con of
                                          A.andCon => P.makeConjunction([prop1,prop2])
                                        | A.orCon => P.makeDisjunction([prop1,prop2])
                                        | A.ifCon => P.makeConditional(prop1,prop2)
                                        | A.iffCon => P.makeBiConditional(prop1,prop2)
                                        | _ => evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),2,1),SOME(pos)))
                                           handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                         in
                           propVal(res)
	                 end
           | primBFunVal(f,_) => (f(evPhrase(arg1,env,ab),evPhrase(arg2,env,ab),env,ab)
                                      handle PrimError(msg) => evError(msg,SOME(pos)) 
                                 )
           | funVal(f,name,_) => 
                           (let val arg_val_1 = evPhrase(arg1,env,ab) 
                                val arg_val_2 = evPhrase(arg2,env,ab)
                            in
		               f([arg_val_1,arg_val_2],env,ab)
                            end handle PrimError(msg) => evError(msg,SOME(pos)))
           | termVal(hol_fun_term) => 	        
                  (case F.isApp(AT.getSort(hol_fun_term)) of 
                      SOME(root,sorts) => if MS.modSymEq(root,Names.fun_name_msym) andalso length(sorts) = 3 
                                          then 
                                             let val args' = [arg1,arg2]							   
						 val arg_vals_and_positions = map (fn p => (evPhrase(p,env,ab),A.posOfPhrase(p)))
  										  args'
                                                  val arg_vals_and_positions = (head_val,A.posOfPhrase(proc))::arg_vals_and_positions
                                                  fun errorMsg(i,v) = wrongArgKindExpectationOnly(termLCType,v)
                                                  val term_args = getTermsWithCoercion(arg_vals_and_positions,errorMsg,coerceValIntoTerm)
						  val term_res = applyTermConstructor(Names.app_fsym_mname,3,term_args,pos)
                                             in
						 termVal(term_res)
                                             end
                                          else evalApp(proc,[arg1,arg2],pos,env,ab)
		    | _ => evalApp(proc,[arg1,arg2],pos,env,ab))
           | _ => (evalApp(proc,[arg1,arg2],pos,env,ab)))
      end 
  | app_exp as A.UAppExp({proc,arg,pos}) => 
      let val head_val = evPhrase(proc,env,ab)
      in
        (case head_val of
             closUFunVal(body,p1,clos_env as ref(valEnv({val_map,mod_map,...})),{name,...}) =>
                   let val vm = Symbol.enter(val_map,p1,evPhrase(arg,env,ab))
                       val _ = addPos(!name,pos)
		       val  (dyn_vmap,dyn_mod_map) = getValAndModMaps(!env)
		       val  (clos_vmap,clos_mod_map) = getValAndModMaps(!clos_env)
                   in 
                      evExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab)                   
                   end
           | primUFunVal(f,_) => (f(evPhrase(arg,env,ab),env,ab)
                                     handle PrimError(msg) => evError(msg,SOME(pos)) 
                                 )
           | termConVal(regFSym(some_fsym)) =>
                           (*** TODO: Unary "app" case: (app E). If E is EITHER a regular constant symbol f:[] -> T OR a constant of the form f^:(Fun T), 
                                then just return (E). Otherwise, assuming that E evaluates to a term t of sort (Fun 'T), which could even be some 
				term variable ?foo:(Fun 'T), return the term (app t).  qqq
                            ***)
                    (let val name = D.fsymName(some_fsym)
                         val arg_val = evPhrase(arg,env,ab)
                     in
                        if MS.modSymEq(name,Names.app_fsym_mname) then  
                           (*** TODO: Unary "app" case: (app E). If E is EITHER a regular constant symbol f:[] -> T OR a constant of the form f^:(Fun T), 
                                then just return f. Otherwise, assuming that E evaluates to a term t of sort (Fun 'T), which could even be some 
				term variable ?foo:(Fun 'T), return the term (app t). 
                            ***)
                             (case coerceValIntoTerm(arg_val) of
                                  SOME(t) => let val _ = (case F.isApp(AT.getSort(t)) of 
                                                             SOME(_,expected_functor_arg_sorts) => 
                                                                let val expected_arity = length(expected_functor_arg_sorts)-1
                                                                in
                                                                  if not(expected_arity = 0) then
                                                                       let val msg = "Unable to infer a sort for the term: \n"^(AT.fauxTermToPrettyString(0,name,[t]))
                                                                       in
                                                                         evError(msg,SOME(pos))
                                                                       end
                                                                  else ()
			   	  		                end
                                                           | _ => evError("Expected a functional sort with arity 0 here.",SOME(A.posOfPhrase(arg))))
                                             in 
                                              if AT.isGeneralConstant(t) then 
                                                let val (lifted_fsym_name_opt,_) = massage(t)
                                                in
                                                   (case lifted_fsym_name_opt of
                                                      SOME(fsym) => termVal(AT.makeConstant(MS.unlift(fsym)))
						    | _ => termVal(t))
                                                end
                                              else (case F.isApp(AT.getSort(t)) of 
                                                      SOME(sort,sort_args) =>  
                                                           if Data.isFunSort(sort) then termVal(applyUnaryTermConstructor(name,t,pos))
                                                           else evError(wrongArgKindExpectationOnly(constantTermLCType,arg_val),SOME(pos))
						    | _  => termVal(applyUnaryTermConstructor(name,t,pos)))
                                             end
			        | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val),SOME(pos)))
                        else (*** Regular, non-app case ***)
                          let val term_arg =  (case coerceValIntoTerm(arg_val) of
                                                 SOME(t) => (case AT.isConstant(t) of 
                 		   	                      SOME(name) =>  let val (_,sort,is_poly,bits) =  Data.getSignature(name)
 					                                     in
					   	                               if FTerm.termEq(sort,AT.getSort(t)) then 
						                                  AT.makeSortedConstantAux(name,sort,is_poly)
                                                                               else t
                                                                             end
                                                            | _ => t)
                                               | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val),SOME(pos)))
                              val term_res = applyTermConstructor(name,1,[term_arg],pos)
                          in
                            termVal(term_res)
                          end
                     end)
           | propConVal(con) => 
                     (case con of
                         A.notCon => let val res_prop = 
                                               (let val nav = (case evPhrase(arg,env,ab) of	
					                          listVal(vl) => 
                                                                    (case vl of
                                                                        [v] => v
                                                                      | _ => let val n = Int.toString(length(vl))
  					                                     in
							                       evError("Wrong number of arguments ("^n^") given to\n"^
								                       (valLCTypeAndStringNoColon(propConVal(con)))^
                                                                                       ". Exactly one argument is required",SOME(pos))
							                     end)
 				                                | v => v)
                                               in
                                                  case coerceValIntoProp(nav) of
                                                      SOME(p) => P.makeNegation(p) 
                                                     | _ => evError(wrongArgKind(S.name(N.not_symbol),1,propLCType,nav),SOME(pos))
                                               end)
                                    in 
                                      propVal(res_prop)
                                    end
                    | _ => let val arg_val = evPhrase(arg,env,ab)
                           in
                             (case con of
                                 A.andCon => let val arg_vals = (case arg_val of 
  			 	                                   listVal(vl) => if null(vl) then 
                                                                                     evError("Empty list of arguments given to "^
                                                                                             (valLCTypeAndStringNoColon(propConVal(con))),SOME(pos))
                                                                                  else vl 
                                                                  | _ => [arg_val])
                                                 val plst = coerceSolePositionedValsIntoProps(arg_vals,pos,"sentential constructor and")
                                                 val res = (P.makeConjunction plst) handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                                             in
                                               propVal(res) 
                                             end
                               | A.orCon => let val arg_vals = (case arg_val of 
  			 	                                   listVal(vl) => if null(vl) then 
                                                                                     evError("Empty list of arguments given to "^N.or_name,SOME(pos))
                                                                                  else vl 
                                                                  | _ => [arg_val])
                                                val plst = coerceSolePositionedValsIntoProps(arg_vals,pos,"sentential constructor or")
                                                val res = (P.makeDisjunction plst) handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                                             in
                                                propVal(res)
                                             end
                              | _ => (case arg_val of
                                         listVal(vals as [v1,v2]) => 
                                             let val [p1,p2] = coerceSolePositionedValsIntoProps(vals,pos,valLCTypeAndStringNoColon(propConVal(con)))
                                                 val res_prop = (if con = A.ifCon then P.makeConditional(p1,p2)  
                                                                 else if con = A.iffCon then P.makeBiConditional(p1,p2)
                                                                 else evError("Wrong number of arguments (1) given to "^(A.propConToString(con)),SOME(pos)))
                                                                 handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                                             in 
                                                propVal(res_prop)
                                             end
                                       | _ => let val arg_num = (case arg_val of
                                                                    listVal(vals) => length(vals)  
                                                                  | _ => 1)
                                              in
                                                if A.isQuantPropCon(con) then
                                                   evError("Wrong number of arguments ("^(Int.toString(arg_num))^") given to\n"^
                                                           (valLCTypeAndStringNoColon(propConVal(con)))^". At least two arguments are required",SOME(pos))
                                                else evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),arg_num,1),SOME(pos))
                                              end))
                           end)
           | subVal(sub) => (case evPhrase(arg,env,ab) of
                                         v as termVal(t) =>  
                                                 (case applySubToValPosLst(sub,[(v,pos)]) of
                                                     listVal([tv]) => tv)
                                       | v as propVal(p) => 
                                                 (case applySubToValPosLst(sub,[(v,pos)]) of
                                                     listVal([pv]) => pv)
                                       | v as listVal(vals) => applySubToValLst(sub,vals,pos)
                                       | v => (case coerceValIntoTerm(v) of
                                                  SOME(t) => 
                                                    (case applySubToValPosLst(sub,[(termVal(t),pos)]) of
                                                       listVal([tv]) => tv)
                                                | _ => (case coerceValIntoProp(v) of
                                                          SOME(P) => (case applySubToValPosLst(sub,[(v,pos)]) of
		                                                        listVal([pv]) => pv)
							| _ => evError("Wrong kind of argument supplied to a "^
                                                               "substitution application; "^expect(termLCType,v),
                                                               SOME(A.posOfPhrase(arg))))))
           | mapVal(m) => (case evPhrase(arg,env,ab) of
                              v => (case Maps.find(m,v) of
                                        SOME(res) => res
                                           | _ => evError("Failed map application: no such key in the map: " ^ (valLCTypeAndString v),SOME(A.posOfPhrase(arg)))))
           | funVal(f,name,_) => 
                           (let val arg_val = evPhrase(arg,env,ab) 
                            in
		               f([arg_val],env,ab)
                            end                          
                                    handle PrimError(msg) => evError(msg,SOME(pos)) 
                            )
           | termVal(hol_fun_term) => 	        
                  (case F.isApp(AT.getSort(hol_fun_term)) of 
                      SOME(root,sorts) => if MS.modSymEq(root,Names.fun_name_msym) andalso length(sorts) = 2
                                          then 
                                             let val arg_val_and_position = (evPhrase(arg,env,ab),A.posOfPhrase(arg))
                                                 val arg_vals_and_positions = [(head_val,A.posOfPhrase(proc)),arg_val_and_position]
                                                 fun errorMsg(i,v) = wrongArgKindExpectationOnly(termLCType,v)
                                                 val term_args = getTermsWithCoercion(arg_vals_and_positions,errorMsg,coerceValIntoTerm)
				    	         val term_res = applyTermConstructor(Names.app_fsym_mname,2,term_args,pos)
                                             in
						 termVal(term_res)
                                             end
                                          else evalApp(proc,[arg],pos,env,ab)
		    | _ => evalApp(proc,[arg],pos,env,ab))

           | _ => (evalApp(proc,[arg],pos,env,ab)))
      end
  | A.matchExp({discriminant,clauses,pos}) => 
      let val discrim_value = evPhrase(discriminant,env,ab)
	  val e_fun = makeEvalExpFunction (env,ab)
          fun tryClauses([]:A.match_clause list) =  
                  evError("match failed---the "^valLCTypeAndStringNoColon(discrim_value)^
                          "\ndid not match any of the given patterns",SOME(pos))
            | tryClauses({pat,exp}::more) = 
                 (case matchPat(discrim_value,pat,e_fun) of
                     SOME(map,sort_sub) => 
                        let val new_env = ref(augmentWithMap(!env,map))
                            in
                              (case evExp(exp,new_env,ab) of
                                  termVal(t) => termVal(AT.applySortSub(sort_sub,t))
                                | propVal(p) => propVal(P.applySortSub(sort_sub,p))
                                | res => res)

                        end
                   | _ => tryClauses(more))
          in
            tryClauses(clauses)
      end                
  | (ev_e as A.letExp({bindings,body,pos})) => 
       let fun doLetExp([]:A.binding list,env1) = evExp(body,env1,ab)
             | doLetExp({bpat,def,pos}::more,env1) = 
                  let val val1 = evPhrase(def,env1,ab)
                  in
                     (case matchPat(val1,bpat,makeEvalExpFunction (env1,ab)) of 
                        SOME(map,_) => let val tval = (case Symbol.lookUp(map,Symbol.symbol("bar")) of
                                                        SOME(v) => v | _ => unitVal)
                                           val (vmap,mod_map) = getValAndModMaps(!env1)
                                           val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                       in
                                         doLetExp(more,new_env)
                                       end 
                      | _ => evError("Let pattern: "^(A.printPat(bpat))^
                                      " failed to match\nthe corresponding value, the "^
                                     (valLCTypeAndStringNoColon val1),
                                     SOME(A.posOfPat(bpat))))
                  end
           in
              doLetExp(bindings,env)
       end
  | app_exp as A.appExp({proc=proc_phrase,args,pos,alt_exp}) => evalApp(proc_phrase,args,pos,env,ab)
  | A.listExp({members,pos}) => listVal(map (fn p => evPhrase(p,env,ab)) members)
  | A.termVarExp({term_var,...}) => termVal(AT.makeVar(term_var))
  | A.taggedConSym({name,sort_as_tagged_symterm,sort_as_fterm=SOME(tagged_sort),pos,...}) => termVal(AT.makeSortedConstant(name,tagged_sort))
  | A.taggedConSym({name,sort_as_tagged_symterm,sort_as_fterm=NONE,pos,...}) => raise Basic.Never
  | A.numExp({number=num,pos}) => termVal(AT.makeNumTerm(num))        
  | A.checkExp({clauses,pos}) => 
         (case evalCheckClauses(clauses,env,ab) of
             SOME(e) => evExp(e,env,ab)
           | _ => evError("check error: all alternatives failed",SOME(pos)))
  | A.logicalOrExp({args,pos}) => 
      let fun f([]) = false_val
            | f(p::more) = let val v = evPhrase(p,env,ab)
                           in
                            (case getBool(v) of
                                 SOME(true) => true_val              
                               | SOME(false) => f(more)
                               | _ => logError("or",A.posOfPhrase(p),v))
                            end
      in
         f(args)
      end
  | A.logicalAndExp({args,pos}) => 
      let fun f([]) = true_val
            | f(p::more) = let val v = evPhrase(p,env,ab)
                           in 
                             (case getBool(v) of
                               SOME(true) => f(more)
                             | SOME(false) => false_val
                             | _ => logError("and",A.posOfPhrase(p),v))
                           end
      in
         f(args)
      end
  | exp as A.functionExp({params,pos,body,...}) =>
          (case params of
               [p1,p2] => closBFunVal(body,A.pwpToSym(p1),A.pwpToSym(p2),env,{name=ref(""),prec=ref(Options.lowest_fsymbol_precedence),assoc=ref(NONE)})
             | [p] => closUFunVal(body,A.pwpToSym(p),env,{name=ref(""),prec=ref(Options.lowest_fsymbol_precedence)})
             | _ => closFunVal(exp,env,{name=ref(""),prec=ref(Options.defaultPrec(length params)),assoc=ref(NONE)}))
  | A.tryExp({choices,pos}) =>
       let fun tryExps([]) = NONE
             | tryExps(e::more) = 
                     (case (SOME(evExp(e,env,ab)) handle _ => NONE) of
                         NONE => tryExps(more)
                       | r => r)
           in
             (case tryExps(choices) of
                 NONE => evError("Try expression error; all alternatives failed.",SOME(pos))
               | (SOME v) => v)
       end
  | exp as A.methodExp({params,body,pos,...}) => 
          (case params of
               [p1,p2] => closBMethodVal(body,A.pwpToSym(p1),A.pwpToSym(p2),env,ref(""))
             | [p]     => closUMethodVal(body,A.pwpToSym(p),env,ref(""))
             | _       => closMethodVal(exp,env))
  | A.quotedIdeExp({name,pos}) => termVal(AT.makeIdeConstant(name))
  | A.stringExp({mem_index,...}) => RSA.sub(SV.string_literals,mem_index)
  | A.charExp({code,...}) => charVal(code)
  | A.letRecExp({bindings,body,pos}) => 
       let val rec_env = ref(!env)
           fun getVals([],map) = map 
             | getVals((b:A.binding as {bpat,def,pos})::more,map) = 
                let val mv = evPhrase(def,rec_env,ab)
                in
                  (case matchPat(mv,bpat,makeEvalExpFunction (rec_env,ab)) of 
                      SOME(map',_) => getVals(more,Symbol.augment(map,map'))
                    | _ => evError("Letrec pattern failed to match the corresponding value, the\n"^ 
                                   (valLCTypeAndStringNoColon mv),
                                   SOME(A.posOfPat(bpat))))
                end
           val pmap = getVals(bindings,S.empty_mapping)
           val (vmap,mod_map) = getValAndModMaps(!env)
           val new_env = valEnv({val_map=Symbol.augment(vmap,pmap),mod_map=mod_map})
           val _ = rec_env := new_env
           in
              evExp(body,ref(new_env),ab)
       end
  | A.whileExp({test,body,pos}) =>
       let fun evPh(p) = evPhrase(p,env,ab)
       in
         (while (let val v = evPh(test) 
                 in 
                   (case coerceValIntoTerm(v) of
                           SOME(b) => if isTrueTerm(b) then true
                                      else if AT.termEq(b,false_term) then false
                                      else evError("Test phrase of while loop failed to produce true or false",
                                                   SOME(pos))
                        | _ => evError("The test phrase of a while loop must produce either true or false---"^
                                       "here it produced a "^valLCTypeAndString(v),
                                       SOME(A.posOfPhrase(test))))
                 end)
          do evPh(body);
         unitVal)
       end
  | A.beginExp({members,pos}) => 
       let fun f([]) = unitVal
             | f([p]) = evPhrase(p,env,ab)
             | f(p1::p2::more) = let val _ = evPhrase(p1,env,ab)
                                 in f(p2::more) end 
       in
          f(members)
       end
  | A.refExp({cell_exp,pos}) =>
          (case evExp(cell_exp,env,ab) of
              cellVal(v) => !v
            | _ => evError("Attempt to dereference a non-cell value",SOME(pos)))
  | A.setCellExp({cell_exp,set_phrase,pos}) => 
        (case evExp(cell_exp,env,ab) of
            cellVal(cv) => (cv := evPhrase(set_phrase,env,ab);unitVal)
          | _ => evError("Attempt to modify a non-cell value",SOME(pos)))
  | A.cellExp({contents,pos}) => cellVal(ref(evPhrase(contents,env,ab)))
  | A.opExp({op_exp,pos}) => evExp(op_exp,env,ab)
  | A.vectorInitExp({length_exp,init_val,pos}) => 
      let val msg = "Given term does not represent a valid vector size"
      in
          (case (coerceValIntoTerm(evExp(length_exp,env,ab))) of
              SOME(t) => (case (AthTerm.getNumVal t) of 
                             SOME(A.int_num(n,_),false) => 
                                if n < 0 then 
  			  	   evError(msg,SOME(A.posOfExp(length_exp)))
    		                else 
                                   vectorVal(Array.array(n,evPhrase(init_val,env,ab)))
                           | _ => evError("Wrong sort of term given as the length (first) argument "^ 
                                          "to vector initialization", 
 				          SOME(A.posOfExp(length_exp))))
            | _ => evError("Wrong kind of value given as first argument to vector initialization",
			    SOME(A.posOfExp(length_exp))))
      end
  | A.vectorSetExp({vector_exp,index_exp,new_val,pos}) => 
         (case evExp(vector_exp,env,ab) of
             vectorVal(vec) => 
               (case (coerceValIntoTerm(evExp(index_exp,env,ab))) of
                  SOME(t) => (case (AthTerm.getNumVal t) of 
                                 SOME(A.int_num(n,_),false) => 
                                    if n < 0 orelse n >= Array.length(vec) then
                                       evError("Vector subscript out of bounds",SOME(A.posOfExp(index_exp)))
                                    else 
                                       (Array.update(vec,n,evPhrase(new_val,env,ab));unitVal)
                               | _ =>  evError("Given term does not represent a valid vector subscript",SOME(A.posOfExp(index_exp))))
                | _ => evError("Wrong kind of value given as subscript to vector-set!",SOME(A.posOfExp(index_exp))))
           | _ => evError("Attempt to vector-set! a non-vector value",SOME(A.posOfExp(vector_exp))))
  | A.vectorSubExp({vector_exp,index_exp,pos}) => 
         (case evExp(vector_exp,env,ab) of
             vectorVal(vec) => 
               (case (coerceValIntoTerm(evExp(index_exp,env,ab))) of
                   SOME(t) => (case  (AthTerm.getNumVal t) of 
                                 SOME(A.int_num(n,_),false) => 
                                      if n < 0 orelse n >= Array.length(vec) then
                                         evError("Vector subscript out of bounds",SOME(A.posOfExp(index_exp)))
                                      else Array.sub(vec,n)
                               | _ => evError("Wrong kind of value given as a vector subscript",SOME(A.posOfExp(index_exp))))
                 | _ =>  evError("Given term does not represent a valid vector subscript",SOME(A.posOfExp(index_exp))))
            | _ => evError("Wrong kind of value given as subscript to vector-sub",SOME(A.posOfExp(index_exp)))))
and 
    makeEvalExpFunction(env,ab) = (fn (e,binding_map) => (case binding_map of 
                                                                  NONE => evExp(e,env,ab)
                                                                | SOME(map) => evExp(e,ref(augmentWithMap(!env,map)),ab)))
and 
    evalMethodApp(method,args:A.phrase list,env:SemanticValues.value_environment ref,ab:ABase.assum_base,pos:A.position) = 
     (let val app_pos = pos 
           fun getArgVals([],arg_vals,ded_vals) = (rev(arg_vals),ded_vals)
             | getArgVals(A.exp(e)::rest,arg_vals,ded_vals) = 
                        getArgVals(rest,evExp(e,env,ab)::arg_vals,ded_vals)
             | getArgVals(A.ded(d)::rest,arg_vals,ded_vals) = 
                       (case evDed(d,env,ab) of
                           propVal(dprop) => 
                              getArgVals(rest,propVal(dprop)::arg_vals,dprop::ded_vals)
                         | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                        "argument of a method application---the deduction did not "^
                                        "produce a sentence!",SOME(A.posOfDed(d))))
           fun getArgValsAndPositions() = 
                let val pos_ar = Array.array(length(args)+2,A.dum_pos)
                    val _ = Array.update(pos_ar,0,app_pos)
                    val _ = Array.update(pos_ar,1,A.posOfExp(method))
                    fun doArgs([],arg_vals,ded_vals,i) = (rev(arg_vals),ded_vals,pos_ar)
                      | doArgs(A.exp(e)::rest,arg_vals,ded_vals,i) = 
                          (Array.update(pos_ar,i,A.posOfExp(e));
                           doArgs(rest,evExp(e,env,ab)::arg_vals,ded_vals,i+1))
                      | doArgs(A.ded(d)::rest,arg_vals,ded_vals,i) = 
                          (Array.update(pos_ar,i,A.posOfDed(d));
                           (case evDed(d,env,ab) of
                               propVal(dprop) => 
                                 doArgs(rest,propVal(dprop)::arg_vals,dprop::ded_vals,i+1)
                             | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                             "argument of a method application---the deduction did not "^
                                             "produce a sentence",SOME(A.posOfDed(d)))))
                in
                   doArgs(args,[],[],2)
                end
       in
          (case evExp(method,env,ab) of 
               closMethodVal(A.methodExp({params,body,pos=mexp_pos,name=rname,...}),clos_env) =>
                       let val (arg_vals,ded_vals) = getArgVals(args,[],[])
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
                           in
                              evDed(body,new_env,new_ab)
                       end  
               | methodVal(f,string) => 
                    (let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
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
                      in 
                         f(arg_vals,env,new_ab)
                      end handle PrimError(msg) => evError(msg,SOME(app_pos)))
               | primUMethodVal(f,code) => 
                                      let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                                      in 
                                        if not(length(arg_vals)  = 1) then 
                                           evError(wrongArgNumber(S.name(code),length(arg_vals),1),getPosOpt(pos_array,0))
                                        else (f(hd(arg_vals),env,ab) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | primBMethodVal(f,code) => 
                                      let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                                      in 
                                        if not(length(arg_vals)  = 2) then 
                                           evError(wrongArgNumber((S.name code),length(arg_vals),2),getPosOpt(pos_array,0))
                                        else (f(hd(arg_vals),hd(tl(arg_vals)),env,ab) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                           val _ =  if not(length(arg_vals)  = 2) then 
                                       evError(wrongArgNumber(!name,length(arg_vals),2),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s1,hd(arg_vals))
                           val vm' = Symbol.enter(vm,s2,hd(tl(arg_vals)))
                           val new_env = ref(valEnv({val_map=vm',mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
                       in
                          evDed(d,new_env,new_ab)
                       end  
               | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,pos_array) = getArgValsAndPositions()
                           val _ =  if not(length(arg_vals)  = 1) then 
                                       evError(wrongArgNumber(!name,length(arg_vals),1),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s,hd(arg_vals))
                           val new_env = ref(valEnv({val_map=vm,mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
                       in
                          evDed(d,new_env,new_ab)
                       end  
               | v => evError("The leftmost expression of a method application "^
                              "must produce a method---here it produced a "^valLCTypeAndString(v),
                              SOME(A.posOfExp(method))))
       end)
and
   evalApp(proc_phrase,args,app_pos,env,ab) = 
    let val head_val = evPhrase(proc_phrase,env,ab) 
        val pos = app_pos 
    in
      ((case head_val of
          propConVal(con) => evalPropConApp(con,args,env,ab,pos)
        | funVal(f,name,_) => 
                          (
                            let fun doArgs([],_,res) = rev(res)
                                  | doArgs(a::more,i,res) = doArgs(more,i+1,evPhrase(a,env,ab)::res)
                                val arg_vals = doArgs(args,2,[])
                                val _ = if !Options.stack_trace then 
                                           addFrame(frame({call_pos=pos,call_file="",
                                                           lambda=FunVal({name=name})}))
                                        else
                                           if !Options.detailed_stack_trace then 
                                              addFrame(detailedFrame({call_pos=pos,call_file="",
                                                                      lambda=FunVal({name=name}),
                                                                      arg_vals=arg_vals}))
                                           else ()
                            in
				 f(arg_vals,env,ab)
                            end handle PrimError(msg) => evError(msg,SOME(app_pos))
                          )
        | closFunVal(A.functionExp({params,body,pos=fexp_pos,...}),clos_env,aux_clos_info) =>
                   let fun makeMessage(i,pos,required_arity,actual_arity,str) = 
                            fn () => evError("the "^(ordinal i)^" argument in this procedure call violated the\n"^
                                             "operator constraint of the corresponding parameter. The relevant OP \n"^
                                             "annotation ("^(A.posToString pos)^") "^
                                             "dictates an arity of "^required_arity^
                                              ".\nThe given "^str^" has an arity of "^actual_arity,
                                              SOME(app_pos))
                       fun f([],[],tab,arg_vals,_) = (tab,arg_vals)
                         | f(pwp::more_params,arg::more_args,tab,arg_vals,i) = 
	                         let val arg_val = evPhrase(arg,env,ab)
				 in
 				   (case pwp of
				       A.someParam({name,pos as param_pos,sort_as_fterm as SOME(fsort),...}) =>
                                         ((case (coerceValIntoTerm arg_val) of 
                                               SOME(t) => let val term_sort = AT.getSort(t)
                                                          in
                                                             (case unifySorts(term_sort,fsort) of
                                                                 SOME(sort_sub) =>  
                                                                     let val t' = AT.applySortSub(sort_sub,t)
                                                                     in         
                                                                       f(more_params,more_args,Symbol.enter(tab,name,termVal t'),
                                                                         arg_val::arg_vals,i+1)
                                                                     end
                                                               | _ => evError("the "^(ordinal i)^" argument in this procedure call violated the\n"^
                                                                              "sort constraint of the corresponding parameter. The relevant sort \n"^
                                                                              "annotation ("^(A.posToString param_pos)^
                                                                               ") dictates a term of sort "^
                                                                              (F.toStringDefault(fsort)),SOME(app_pos)))
                                                          end))
  				     | A.someParam({name,sort_as_fterm as NONE,...}) =>
                	                   (f(more_params,more_args,Symbol.enter(tab,name,arg_val),arg_val::arg_vals,i+1))
				     | A.wildCard(_) => 
				  	   f(more_params,more_args,tab,arg_val::arg_vals,i+1))
				 end
                         | f(_,_,_,_,_) = evError("Wrong number of arguments ("^Int.toString(length(args))^ 
                                                 ") given\nto procedure "^(!(#name(aux_clos_info)))^"---exactly "^argNumToString(length(params))^
                                                 " required",SOME(pos))
                       val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val (new_vmap,arg_vals) = f(params,args,vmap,[],1)
                       val new_env = valEnv({val_map=new_vmap,mod_map=mmap})
                       val _ = addPos(!(#name(aux_clos_info)),app_pos)
                   in
                       evExp(body,ref(new_env),ab)
                   end 
        | v =>  
             (case coerceValIntoTermCon(v) of
                 SOME(regFSym(some_fsym)) => 
                    (let (***  qqq 
                          Here. some_fsym might be "app", so we'll need to make sure that we evaluate this properly 
                         ***)
                         val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
                         fun errorMsg(i,v) = wrongArgKindExpectationOnly(termLCType,v)
                         val is_app_app = MS.modSymEq(name,Names.app_fsym_mname)
			 val (expected_arg_sorts,result_sort,is_poly,_) = 
                                if is_app_app then Data.getAppSig(args)
                                else Data.getSignature(name)
                         fun getTerm(arg_val,expected_sort,pos) = 
			                 (case coerceValIntoTerm(arg_val) of
                                             SOME(t) => (case AT.isConstant(t) of 
                 			                    SOME(name) =>  if FTerm.termEq(result_sort,AT.getSort(t)) then 
 					                                      AT.makeSortedConstantAux(name,result_sort,is_poly)
                                                                          else t
                                                         | _ => t)                                 
                                            | _ => (case D.funSortArity(expected_sort) of 
                                                        SOME(K) => liftArg(arg_val,K,SOME pos)
  	  					      | _ =>  evError(wrongArgKindExpectationOnly(termLCType,arg_val),SOME(pos))))
                        val N = length(args)
                     in
                        if is_app_app andalso N > 2 then  
                           (*** In this case the entire application is of the form (app E_1 ... E_n) for n > 2. ***)
                           let val arg_val1 = evPhrase(hd args,env,ab)
			       val rest_arg_vals_positions_and_expected_sorts = 
                                          map (fn (p,expected_sort) => (evPhrase(p,env,ab),A.posOfPhrase(p),expected_sort))
  	                                       (Basic.zip(tl(args),tl(expected_arg_sorts)))
                               val rest_arg_terms = map (fn (v,pos,e) => getTerm(v,e,pos)) 
							rest_arg_vals_positions_and_expected_sorts
                           in
                             (case coerceValIntoTerm(arg_val1) of
                                 SOME(functor_term) => 
                                            let val _ = (case F.isApp(AT.getSort(functor_term)) of 
                                                            SOME(f,expected_functor_arg_sorts) => 
                                                             let val expected_arity = length(expected_functor_arg_sorts)-1
                                                             in 
                                                               if not(expected_arity = (N-1)) then 
                                                                  evError("Type inference error: Was expecting " ^ (Int.toString expected_arity) ^ " arguments given to this functor, but instead found " ^ (Int.toString (N-1)),SOME(A.posOfPhrase(hd args)))
                                                               else ()
                                                             end
						           | _ => evError("I was expecting a functor as the first argument of app.", SOME(pos)))
                                                val (lifted_fsym_opt,term_arg1) = massage(functor_term)
                                               (**** If term_arg1 is a term constant of sort (Fun S T) that is lifted, i.e., of the form f^, then we should just return (f term_arg2)  ****)
  	  	  			        val term_res = (case lifted_fsym_opt of 
                                                                   SOME(fsym) => applyTermConstructor(MS.unlift(fsym),arity,rest_arg_terms,pos)
						  	         | _ => let (* val _ = print("\nLength of t::rest_arg_terms: " ^ (Int.toString (length (functor_term::rest_arg_terms)))) *)
                                                                        in
                                                                          applyTermConstructor(name,arity,functor_term::rest_arg_terms,pos)
                                                                        end)
                                            in
                                              termVal(term_res)
                                            end 
                               | _ => (case coerceValIntoTermCon(arg_val1) of 
                                           SOME(regFSym(fsym)) => termVal(applyTermConstructor(D.fsymName(fsym),arity,rest_arg_terms,pos))
                                          | _ => evError(wrongArgKindExpectationOnly(termLCType,head_val),SOME(pos))))
                           end
                        else let val arg_vals_positions_and_expected_sorts = 
                                            map (fn (p,expected_sort) => (evPhrase(p,env,ab),A.posOfPhrase(p),expected_sort))
                                                (Basic.zip(args,expected_arg_sorts))
                                 val term_args = map (fn (v,pos,e) => getTerm(v,e,pos))
                                                     arg_vals_positions_and_expected_sorts 
                                 val term_res = applyTermConstructor(name,arity,term_args,pos)
                                 in
                                    termVal(term_res)
                                 end
                     end)
               | SOME(athNumFSym(anum)) => 
                      (if null(args) then termVal(AT.makeNumTerm(anum))
                        else evError(Int.toString(length(args))^" arguments given to nullary "^
                                    "symbol "^A.athNumberToString(anum)^"---it requires exactly zero arguments",
                                    SOME(pos)))
               | SOME(metaIdFSym(str)) => 
                 (if null(args) then termVal(AT.makeIdeConstant(str))
                  else evError(Int.toString(length(args))^" arguments given to nullary "^
                               "symbol "^A.printMetaId(str)^"---it requires exactly zero arguments",
                               SOME(pos)))
               | _ => (case v of
                          closUFunVal(_,_,_,{name,...}) => evError(wrongArgNumber(!name,length(args),1),SOME(app_pos))
                        | primUFunVal(_,{name,...}) => evError(wrongArgNumber(name,length(args),1),SOME(app_pos))
                        | closBFunVal(_,_,_,_,{name,...}) => evError(wrongArgNumber(!name,length(args),2),SOME(app_pos))
                        | primBFunVal(_,{name,...}) => evError(wrongArgNumber(name,length(args),2),SOME(app_pos))
                        | _ => let val msg = "The leftmost expression\nof an application failed to produce "^
                                             "a procedure\nor a symbol or a substitution. Instead,\n"
                                   val msg2 = "it produced this: "^(valLCTypeAndString(v))
                                   in evError(msg^msg2,SOME(A.posOfPhrase(proc_phrase)))
                               end))))
    end
and
   evalPropConApp(con,args as first::rest,env,ab,pos) = 
     if A.isQuantPropCon(con) then
      (case rest of
 	 _::_ =>
	      let val rev_args = rev(args)
        	  val prop_arg = hd(rev_args)
	          val pval = evPhrase(prop_arg,env,ab)
	      in
	      (case coerceValIntoProp(pval) of
	         SOME(p) => (let val var_vals = map (fn a => evPhrase(a,env,ab)) (rev(tl(rev_args)))
	                         val term_vars = getTermVars(var_vals,con,pos)
	                         val res_prop = makeQuantProp(SOME(con),term_vars,p)
						handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),
										SOME(pos))
	                     in
	                        propVal(res_prop) 
	                     end)
	        | _ => evError(wrongArgKind(A.propConToString(con),length(rev_args),propLCType,pval),
			       SOME(A.posOfPhrase(prop_arg))))
	      end
       | _ => evError("Wrong number of arguments (1) given\nto "^A.propConToString(con)^"---at least "^
		      "two arguments are required",SOME(pos)))
     else
	(if con = A.andCon orelse con = A.orCon then
	  let val arg_vals = map (fn a => evPhrase(a,env,ab)) args
	      val first_pos = A.posOfPhrase(first)
	      val (arg_vals1,arg_positions) = (case arg_vals of 
						[listVal(vl)] => (case vl of 
								    [_] => (vl,[first_pos])
   								  | _ => (vl,map (fn _ => first_pos) vl))
					      | _ => (arg_vals,map (A.posOfPhrase) args))
	      val con_val = propConVal(con)
	      val makeTheProp = (if con = A.andCon then P.makeConjunction else P.makeDisjunction)
	      val plst = coercePositionedValsIntoProps(arg_vals1,arg_positions,valLCTypeAndStringNoColon(con_val))
	  in
              (propVal(makeTheProp plst)) handle Basic.FailLst(msgs) => 
							evError(Basic.failMsgsToStr(msgs),SOME(pos))

	  end
	  else
	          let val arg_vals = map (fn a => evPhrase(a,env,ab)) args
		      val arg_vals1 = (case arg_vals of [listVal(vl)] => vl | _ => arg_vals)
		      val con_val = propConVal(con)
		      val (v1,v2) = (case arg_vals1 of
					[v1,v2] => (v1,v2)
				      | _ => evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),
								    length(arg_vals1),2),SOME(pos)))
        	 in
	          (case (coerceValIntoProp(v1),coerceValIntoProp(v2)) of
        	      (SOME(p1),SOME(p2)) => 
	                  let val res_prop = makeBinaryProp(con,p1,p2) 
					 	handle Basic.FailLst(msgs) => 
							 evError(Basic.failMsgsToStr(msgs),SOME(pos))
	                      in
	                        propVal(res_prop)

	                  end
        	    | (SOME(_),NONE) =>  evError(wrongArgKind(valLCTypeAndStringNoColon(con_val),2,propLCType,v2),
                	                         SOME(pos))
	            | (_,_) => evError(wrongArgKind(valLCTypeAndStringNoColon(con_val),1,propLCType,v1),
        	                                 SOME(pos)))
		 end)
  | evalPropConApp(con as A.andCon,[],_,_,pos) =  
	evError("No arguments given to "^valLCTypeAndStringNoColon(propConVal(con))^"---at least one\n"^
		"argument is required",SOME(pos))
  | evalPropConApp(con as A.orCon,[],_,_,pos) =  
	evError("No arguments given to "^valLCTypeAndStringNoColon(propConVal(con))^"---at least one\n"^
		"argument is required",SOME(pos))
  | evalPropConApp(con,args,_,_,pos) = 
            evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),length(args),2),
                    SOME(pos))
and 
    evalClosure(v as closFunVal(A.functionExp({params,body,pos,...}),clos_env,{prec,assoc,...}),
               arg_vals,ab,pos_option) =
           let val param_num = length(params)
               val arg_num = length(arg_vals)
           in
               if not(arg_num = param_num) then
                  makeError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),pos_option)
               else 
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val new_env = ref(valEnv({val_map=enterParamValLst(vmap,params,arg_vals),mod_map=mmap}))
                       in
                         evExp(body,new_env,ab)
                   end
           end
  | evalClosure(v as closBFunVal(body,param1,param2,clos_env,_),
               arg_vals,ab,pos_opt) =
           let val param_num = 2
               val arg_num = length(arg_vals)
           in
               if not(arg_num = param_num) then
                  makeError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),pos_opt)
               else
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val vmap' = Symbol.enter(vmap,param1,hd arg_vals)
                       val vmap'' = Symbol.enter(vmap',param2,hd (tl arg_vals))
                       val new_env = ref(valEnv({val_map=vmap'',mod_map=mmap}))
                       in
                         evExp(body,new_env,ab)
                   end
           end
  | evalClosure(v as closUFunVal(body,param,clos_env,{name,...}),
               arg_vals,ab,pos_opt) =
           let val param_num = 1
               val arg_num = length(arg_vals)
               val cond = (arg_num = param_num)
           in
               if not(cond) then
                  makeError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),pos_opt)
               else
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val vmap' = Symbol.enter(vmap,param,hd arg_vals)
                       val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
                       in
                         evExp(body,new_env,ab)
                   end
           end
  | evalClosure(_) = genError("Invalid call to evalClosure",NONE)
and
    evalMethodClosure(v as closMethodVal(A.methodExp({params,body,pos,...}),clos_env),
                      arg_vals,ab,position) =
           let val param_num = length(params)
               val arg_num = length(arg_vals)
           in
               if not(arg_num = param_num) then
                  evError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),SOME(position))
               else
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val new_env = ref(valEnv({val_map=enterParamValLst(vmap,params,arg_vals),mod_map=mmap}))
                       in
                         evDed(body,new_env,ab)
                   end
           end
  | evalMethodClosure(v as closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),_),arg_vals,ab,position) = 
           let val arg_num = length(arg_vals)
           in
              if not(arg_num = 1) then
                 evError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,1),SOME(position))
              else let val vm = Symbol.enter(val_map,s,hd arg_vals)
                       val new_env = ref(valEnv({val_map=vm,mod_map=mod_map}))
                   in
                      evDed(d,new_env,ab)
                   end
           end           
  | evalMethodClosure(v as closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),_),arg_vals,ab,position) = 
           let val arg_num = length(arg_vals)
           in
              if not(arg_num = 2) then
                 evError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,2),SOME(position))
              else let val vm = Symbol.enter(val_map,s1,hd arg_vals)
                       val vm' = Symbol.enter(vm,s2,hd(tl(arg_vals)))
                       val new_env = ref(valEnv({val_map=vm',mod_map=mod_map}))
                   in
                      evDed(d,new_env,ab)
                   end
           end           
  | evalMethodClosure(_) = genError("Invalid call to evalClosure",NONE)
and 
   evDed(method_app as A.BMethAppDed({method,arg1,arg2,pos}),env,ab) = 
    ((let val head_val = evExp(method,env,ab) 
      in
        (case head_val of
           primBMethodVal(M,method_code) => 
                (let val v1 = evPhrase(arg1,env,ab)
                     val v2 = evPhrase(arg2,env,ab)
                     val ab' = if A.isDeduction(arg1) then putValIntoAB(v1,ab) else ab
                     val ab'' = if A.isDeduction(arg2) then putValIntoAB(v2,ab') else ab'
                 in
                    M(v1,v2,env,ab'') 
                 end handle PrimError(msg) => evError(msg,SOME(pos))
                          | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()
                                                in
                                                  evError(msg,SOME(right_pos))
                                                end)
         | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) => 
                  let val v1 = evPhrase(arg1,env,ab)
                      val v2 = evPhrase(arg2,env,ab) 
                      val ab' = if A.isDeduction(arg1) then putValIntoAB(v1,ab) else ab
                      val ab'' = if A.isDeduction(arg2) then putValIntoAB(v2,ab') else ab'
                      val vm = Symbol.enter(Symbol.enter(val_map,s1,v1),s2,v2)
                      val _ = addPos(!name,pos)
                  in
                     evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab'')                  
                  end
        | _ =>  evalMethodApp(method,[arg1,arg2],env,ab,pos))
      end))
  | evDed(A.UMethAppDed({method,arg,pos}),env,ab) = 
     ((let val head_val = evExp(method,env,ab)
       in
         (case head_val of
              primUMethodVal(f,_) => (let val arg_val = evPhrase(arg,env,ab)
                                          val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
                                      in
                                         f(arg_val,env,ab') 
                                      end handle PrimError(msg) => evError(msg,SOME(pos))                                      
                                               | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()
                                                                     in
                                                                        evError(msg,SOME(right_pos))
                                                                     end
)
            | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),clos_name) => 
                   let val arg_val = evPhrase(arg,env,ab)
                       val vm = Symbol.enter(val_map,s,arg_val)
                       val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
                       val _ = addPos(!clos_name,pos)
                   in
                      evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab')                  
                   end
            | _ => evalMethodApp(method,[arg],env,ab,pos))
       end))
  | evDed(method_app as A.methodAppDed({method,args,pos=app_pos}),env,ab) = evalMethodApp(method,args,env,ab,app_pos)
  | evDed(A.letDed({bindings,body,pos}),env,ab) = 
       let fun doLetDed([]:A.binding list,env1,ab1) = evDed(body,env1,ab1)
             | doLetDed({bpat,def=A.ded(d),pos}::more,env1,ab1) = 
                  let val dval = evDed(d,env1,ab1)
                  in
                     (case matchPat(dval,bpat,makeEvalExpFunction (env1,ab)) of 
                        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                         val new_ab = (case dval of
                                                          propVal(p) => ABaseAugment(ab1,Prop.decomposeConjunctions p)
                                                        | _ => ab1)
                                     in
                                       doLetDed(more,new_env,new_ab)
                                     end 
                      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                                     (valLCTypeAndStringNoColon dval),
                                     SOME(A.posOfPat(bpat))))
                  end
             | doLetDed({bpat,def=A.exp(e),pos}::more,env1,ab1) = 
                  let val eval = evExp(e,env1,ab1)
                  in
                     (case matchPat(eval,bpat,makeEvalExpFunction (env1,ab)) of 
                        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                     in
                                       doLetDed(more,new_env,ab1)
                                     end 
                      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                                      (valLCTypeAndStringNoColon eval),
                                     SOME(A.posOfPat(bpat))))
                  end
           in
              doLetDed(bindings,env,ab)
       end
  | evDed(A.matchDed({discriminant,clauses,pos}),env,ab) =
      let val discrim_value = evPhrase(discriminant,env,ab)
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
                          in
                            evDed(ded,new_env,new_ab)
                      end
                 | _ => tryClauses(more))
          in
            tryClauses(clauses)
      end                         
  | evDed(A.assumeDed({assumption,body,pos}),env,ab) = 
            let val aval = evPhrase(assumption,env,ab)
            in
               (case coerceValIntoProp(aval) of
                   SOME(p1) => let val asms = Prop.decomposeConjunctions(p1)
                                   val ab' = ABase.augment(ab,asms)
                               in 
                                 (case coerceValIntoProp(evDed(body,env,ab')) of 
                                    SOME(p2) => propVal(P.makeConditional(p1,p2))
                                  | _ => evError("Impossible error encountered in assume deduction: the body of "^
                                                  "the deduction did not produce a sentence",
			  		  SOME(A.posOfDed(body))))
                               end
                 | _ => evError("In a deduction of the form (assume F D), the value of F"^ 
                                " must\nbe a sentence, but here it was a "^valLCTypeAndString(aval),
                                SOME(A.posOfPhrase(assumption))))
            end
  | evDed(A.assumeLetDed({bindings,body,pos}),env,ab) = 
           let fun getProp(F,is_ded,env,ab) = 
                  let val Fval = evPhrase(F,env,ab)
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
                     in
                       propVal(Prop.foldConditionals(rev(assumptions),
                               getProp(A.ded(body),true,env1,ABaseAugment(ab,asms'))))
                     end
                  | doBindings({bpat,def,...}::more,assumptions,env1) = 
                       let val new_assumption = getProp(def,false,env1,ab)
                       in
                          (case matchPat(propVal(new_assumption),bpat,makeEvalExpFunction (env1,ab)) of 
                              SOME(map,_) => let val (vmap,mmap) = getValAndModMaps(!env1)
                                               val env1' = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                           in
                                             doBindings(more,new_assumption::assumptions,env1')
                                           end
                            | _ => evError("Assume pattern failed to match the corresponding value, the\n "^
                                            (valLCTypeAndStringNoColon (propVal new_assumption)),
                                            SOME(A.posOfPat(bpat))))
                       end
           in
              doBindings(bindings,[],env)
           end
  | evDed(A.absurdDed({hyp,body,pos}),env,ab) = doSupposeAbsurd(hyp,NONE,body,pos,env,ab)
  | evDed(A.absurdLetDed({named_hyp,body,pos}),env,ab) = 
          let val (hyp_name_pat,hyp) = (#bpat(named_hyp),#def(named_hyp))
              in
                doSupposeAbsurd(hyp,SOME(hyp_name_pat),body,pos,env,ab)
          end
  | evDed(A.inductionDed({prop,clauses,pos}),env:value_environment ref,ab) = 
      let val (uvar,body,goal) = let val pval = evPhrase(prop,env,ab)
                                 in
                                   (case (coerceValIntoProp(pval)) of
	    	  	   	     SOME(P) => (case P.isUGen(P) of 
                                                    SOME(v,body) => (v,body,P)
				    	           | _ => evError((prefix ())^(msg3 pval),
					  	    	           SOME(A.posOfPhrase(prop))))
                                    | _ => evError((prefix ())^(msg3 pval),SOME(A.posOfPhrase(prop))))
  			         end
          val uvar_sort = ATV.getSort(uvar)
          val _ = if StructureAnalysis.isStructureType(uvar_sort) then () else 
                  evError(msg1(2,ATV.toStringWithSort(uvar),P.toString(body,makeVarSortPrinter()),
			  F.toStringDefault(uvar_sort)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evExp(e',env',ab)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,uvar_sort,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,uvar_sort) of
                      SOME(t) => evError(msg2(F.toStringDefault(uvar_sort),
                                              AT.toStringDefault(t)),SOME(pos))
                    | _ => ()) 
          fun property(t) = P.replace(uvar,t,body)
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),previous_clauses,ab) = 
               let fun emsg(req,gotten) = "One of the given cases of this inductive deduction failed "^
                                          "to establish the right conlusion.\nWanted: "^
                                           Util.decide(pprintProp(req),50)^
                                          "\nGotten: "^Util.decide(pprintProp(gotten),50)^"\n"
                   val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val new_iarm = {uvar=uvar,uvar_sort=uvar_sort,uprop=body,
                                   uv_pattern=pat_as_ath_term}
                   val _ = iarm_stack := LStack.push(new_iarm,!iarm_stack)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                 else new_env_0
                   val real_current_goal = property(pat_as_ath_term)
                   fun getReflexiveFreshvars(vars,res) = 
                         (case vars of
                             [] => (rev res)
                           | fv::more => let val fresh_var_sort = ATV.getSort(fv)
                                         in
                                            (case F.isVarOpt(fresh_var_sort) of
                                                SOME(_) => getReflexiveFreshvars(more,res)
                                              | _ => (case F.unify(fresh_var_sort,F.rename(uvar_sort)) of
                                                         SOME(sub) => let val new = ATV.applySortSub(sub,fv)
                                                                      in
                                                                        getReflexiveFreshvars(more,new::res)
                                                                      end
                                                       | _ =>  getReflexiveFreshvars(more,res)))
                                         end)

                  val reflexive_fresh_vars = getReflexiveFreshvars(fresh_vars,[])
                  val reflexive_vars_as_terms = map AT.makeVar reflexive_fresh_vars
                  val current_ind_hyps = map property reflexive_vars_as_terms
                  fun sameRootSymbol(t1,t2) = 
                         (case (AT.isApp(t1),AT.isApp(t2)) of
                             (SOME(f,_),SOME(g,_)) => MS.modSymEq(f,g)
                           | _ => false)
                  val diff_facts:P.prop list = 
                          if not(!(Options.fundef_mlstyle_option)) orelse null(previous_clauses) then [] 
                          else (let val previous_pats_as_terms:AT.term list = map (fn (_,y,_,_,_) => y) previous_clauses
                                    val previous_pats_as_terms = List.filter (fn t => sameRootSymbol(t,pat_as_ath_term)) previous_pats_as_terms
                                    val previous_pat_string = Basic.printSExpListStr(previous_pats_as_terms,fn t => (valToString (termVal t)))
                                    val pstr = getSafeName("diff*")
                                    val str = "("^pstr^" "^(valToString (termVal pat_as_ath_term))^" ["^previous_pat_string^"])"
                                    val evalString = !evaluateString
                                    val lv = evalString(str)
                                in 
                                   case coerceValIntoProp(lv) of
                                       SOME(p) => let val res = Prop.decomposeConjunctions(p)
                                                  in
                                                    res
                                                  end
                                end) handle _ => [] 
                   val ind_hyps = (current_ind_hyps@
                                  (if (AT.height(pat_as_ath_term) = 0) then [] 
                                   else getInductiveHypotheses(!iarm_stack,fresh_vars,real_current_goal,pat_as_ath_term)))
				  handle Basic.FailLst(msgs) => evError("Error in generating inductive "^
									"hypotheses..."^Basic.failMsgsToStr(msgs),
									SOME(pos))
                   val new_ab = ABaseAugment(ab,diff_facts@ind_hyps)
                   val res_prop = (case evDed(ded,new_env,new_ab) of
                                      propVal(P) => P
                                    | _ => raise Basic.Never)
               in
                  (case provesTheRightInductiveCase(res_prop,uvar,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"inductive") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => (iarm_stack := LStack.pop(!iarm_stack);
                            let val conjunction = P.makeConjunction(ind_hyps)
                                val body = if null(ind_hyps) then res_prop else P.makeConditional(conjunction,res_prop)
                                val res = P.makeUGen(fresh_vars,body)
                            in res
                            end))
               end
          fun doNewClauses([],_,_) = propVal(P.makeUGen([uvar],body))
            | doNewClauses(clause::more_clauses,previous_clauses,ab) = 
                  let val res = doNewClause(clause,previous_clauses,ab) 
                  in
                     doNewClauses(more_clauses,clause::previous_clauses,ab) 
                  end
      in
         doNewClauses(new_clauses,[],ab)
      end
  | evDed(A.structureCasesDed({prop,clauses,pos,term}),env:value_environment ref,ab) = 
    (case term of 
     SOME(dt_exp) =>  
      let fun prefix(n) = let val str = "first"
                          in
                             "Invalid argument given to the datatype-cases form.\n"^
                             "In every deduction of the form (datatype-cases E v D), the "^
                             "value of E must\nbe a sentence P and v must be (or denote) a variable"  
                          end
          fun msg1(n,var_str,P_str,obtype) = prefix(n)^". In addition, the\nsort of v in P must be a datatype."^ 
                                   " But here "^"v and P are "^var_str^" and\n"^P_str^
                                   "\nrespectively, where "^var_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a datatype"
          fun msg2(str1,str2) = "Ill-formed datatype-cases deduction---the given patterns do not exhaust\nthe "^
                                "datatype "^str1^". Here is a counter-example: "^str2
          fun msg3(n,v) = prefix(n)^".\nBut here E was a "^valLCTypeAndString(v)
          fun msg4(e) = "A variable was expected here"
          val dt_exp_pos = A.posOfExp(dt_exp)
          val var = (case evExp(dt_exp,env,ab) of
                        termVal(t) => (case AT.isVarOpt(t) of
                                          SOME(v) => v
                                        | _ => evError(msg4(dt_exp),SOME(dt_exp_pos)))
                      | _ => evError(msg4(dt_exp),SOME(dt_exp_pos)))
          val var_term = AthTerm.makeVar(var)
          val body = let val pval = evPhrase(prop,env,ab)
                            in
                              (case coerceValIntoProp(pval) of
                                  SOME(P) => P
                                 | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                            end 
          val var_type = ATV.getSort(var)
          val _ = if StructureAnalysis.isStructureType(var_type) then () else 
                  evError(msg1(2,Terms.printAthTermVar(var),prettyValToString(propVal(body)),Terms.printFTermSExp(var_type)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evExp(e',env',ab)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,var_type,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,var_type) of
                      SOME(t) => evError(msg2(Terms.printFTermSExp(var_type),
                                              Terms.printAthTermSExp(t)),SOME(pos))
                    | _ => ())
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),ab) = 
               let val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
		                   let 
                                   in
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                   end
                                 else 
				    let
                                    in
                                      new_env_0
                                    end
                   val new_ab = ABaseAugment(ab,[Prop.makeEquality(var_term,pat_as_ath_term),Prop.makeEquality(pat_as_ath_term,var_term)])
                   val res_prop = (case evDed(ded,new_env,new_ab) of
                                      propVal(P) => P)
               in
                  (case provesTheRightInductiveCase(res_prop,var,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"structure-cases") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => P.makeUGen(fresh_vars,res_prop))
               end
          fun doNewClauses([],_) = propVal(body)
            | doNewClauses(clause::more_clauses,ab) = 
                  let val res = doNewClause(clause,ab) 
                  in
                     doNewClauses(more_clauses,ABaseInsert(res,ab))
                  end
      in
         doNewClauses(new_clauses,ab)
      end
    | NONE =>   
      let fun prefix(n) = let val str = "first"
                          in
                             "Invalid "^str^" argument given to the structure-cases form. "^
                             "In every deduction\nof the form (structure-cases E D), the "^
                             "value of E must be a sentence P of the form (forall v Q)"  
                          end
          fun msg1(n,var_str,P_str,obtype) = prefix(n)^".\nIn addition, the sort of v in Q must be a structure."^ 
                                   " But here\n"^"v and P are "^var_str^" and "^P_str^
                                   ", respectively, where "^var_str^" in "^P_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a structure"
          fun msg2(str1,str2) = "Ill-formed structure-cases deduction---the given patterns do not exhaust\nthe "^
                                "structure "^str1^". Here is a counter-example: "^str2
          fun msg3(n,v) = prefix(n)^".\nBut here E was a "^valLCTypeAndString(v)
          val (uvar,body) = let val pval = evPhrase(prop,env,ab)
                            in
                              (case coerceValIntoProp(pval) of
				  SOME(P) => (case P.isUGen(P) of 
		                                 SOME(uv,ub) => (uv,ub)
					       | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                                 | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                            end 
          val uvar_sort = ATV.getSort(uvar)
          val _ = if StructureAnalysis.isStructureType(uvar_sort) then () else 
                  evError(msg1(2,ATV.toStringDefault(uvar),P.toString(body,makeVarSortPrinter()),
			  F.toStringDefault(uvar_sort)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evExp(e',env',ab)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,uvar_sort,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,uvar_sort) of
                      SOME(t) => evError(msg2(F.toStringDefault(uvar_sort),
                                              AT.toStringDefault(t)),SOME(pos))
                    | _ => ())
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),ab) = 
               let val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
		                   let
                                   in
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                   end
                                 else 
				    let
                                    in
                                      new_env_0
                                    end
                   val new_ab = ab
                   val res_prop = (case evDed(ded,new_env,new_ab) of
                                      propVal(P) => P
                                    | _ => raise Basic.Never)
               in
                  (case provesTheRightInductiveCase(res_prop,uvar,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"structure-cases") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => P.makeUGen(fresh_vars,res_prop))
               end
          fun doNewClauses([],_) = propVal(P.makeUGen([uvar],body))
            | doNewClauses(clause::more_clauses,ab) = 
                  let val res = doNewClause(clause,ab) 
                  in
                     doNewClauses(more_clauses,ABaseInsert(res,ab))
                  end
      in
         doNewClauses(new_clauses,ab)
      end)
  | evDed(A.byCasesDed({disj,from_exps,arms,pos}),env,ab) = 
	let val disj_val = evPhrase(disj,env,ab)
	    val disj_prop = (case coerceValIntoProp(disj_val) of
           			SOME(P) => P
			      | _ => evError("A sentence (disjunction) was expected here. Instead, a\n"^
					     "value of type "^valLCTypeAndString(disj_val)^" was found.",
                	                      SOME(A.posOfPhrase(disj))))
	    val disj_holds = if ABase.isMember(disj_prop,ab) orelse A.isDeduction(disj) orelse Prop.isExMiddleInstance(disj_prop) then true
			     else
				(case from_exps of 
				   NONE => evError("By-cases disjunction doesn't hold",
					           SOME(A.posOfPhrase(disj)))
			          | SOME(exps) => 
				 let fun er() = evError("Error in cases proof: unable to "^
					         "automatically derive the disjunction "^
						  prettyValToStringNoTypes(disj_val),SOME(pos))
				    val atp_call = A.methodAppDed({
							method=A.idExp({msym=msym N.vpfPrimMethod_symbol,no_mods=true,mods=[],sym=N.vpfPrimMethod_symbol,pos=pos}),
					    args=[disj,A.exp(A.listExp({members=(map A.exp exps),
							pos=A.dum_pos}))],pos=pos})
				     val atp_val = evDed(atp_call,env,ab) handle EvalError(str,_) => 
						 (print(str);raise Basic.Never)
				 in
				   (case coerceValIntoProp(atp_val) of
				       SOME(dp) => if P.alEq(dp,disj_prop) then true else er()
				     | _ => er())
				 end)
	    val alts = P.getDisjuncts(disj_prop)
	    fun getAltProp(v,pos) = (case coerceValIntoProp(v) of 
				        SOME(P) => P
				      | _ => evError("A sentence was expected here. Instead, a\n"^
					             "value of type "^valLCTypeAndString(v)^" was found.",
                	                             SOME(pos)))
	    fun casesLeftUntreated(P) = evError("Non-exhaustive cases proof.\nThis case was not "^
				                "considered:\n"^P.toPrettyString(0,P,makeVarSortPrinter()),
					        SOME(pos))
	    fun gratuitousCase(P,pos) = evError("Gratuitous case considered in proof by cases:\n"^
						 P.toPrettyString(0,P,makeVarSortPrinter()),
						SOME(pos))
	    val {case_name,alt=first_case,proof=first_ded}:A.case_clause = hd arms
	    val (first_case_considered,conclusion,cases_left) = 
		  let val first_prop = getAltProp(evExp(first_case,env,ab),A.posOfExp(first_case)) 
                      val (vmap,mmap) = getValAndModMaps(!env)
   		      val env' = (case case_name of
			             SOME({name,...}) => ref(valEnv({val_map=Symbol.enter(vmap,name,propVal(first_prop)),mod_map=mmap}))
				   | _ => env)
		      val first_concl = (case coerceValIntoProp(evDed(first_ded,env',
						ABaseInsert(first_prop,ab))) of
					   SOME(P) => P | _ => raise Basic.Never)
		      val (cases_left,is_mem) = Basic.removeAndCheckMemEq(first_prop,alts,P.alEq)
		  in
		     (first_prop,first_concl,cases_left) 
		  end
	    fun checkConclusion(d,case_considered, new_env) = 
              let val conc = evDed(d,new_env,ABaseInsert(case_considered,ab))
              in
		 (case coerceValIntoProp(conc) of
		     SOME(P) => if P.alEq(P,conclusion) then ()
				else let val varSortPrinter = makeVarSortPrinter()
				     in
					evError("The sentence "^
					     P.toPrettyString(0,conclusion,varSortPrinter)^
					     " was expected here.\n"^
					     "Instead, the following sentence was produced: "^
					     P.toPrettyString(0,P,varSortPrinter),
					     SOME(A.posOfDed(d)))
				     end
		   | _ => raise Basic.Never)
	      end 
	    fun doArms([],cases_considered,cases_left) = if Basic.subsetEq(cases_left,cases_considered,P.alEq)
							 then propVal(conclusion)
							 else casesLeftUntreated(hd cases_left)
	      | doArms((cc:A.case_clause as {case_name,alt,proof})::rest,
			cases_considered,cases_left) =
		  let val new_case_val = evExp(alt,env,ab)
					 handle EvalError(str,_) => 
						 (print(str);raise Basic.Never)
					      |   ObTypeCheckFailure => 
						    (print("\nSort failure\n");raise Basic.Never)
                                              | _ => (print("\n Unknown error.\n"); raise Basic.Never)
		      val new_case = getAltProp(new_case_val,A.posOfExp(alt)) 
                      val (vmap,mmap) = getValAndModMaps(!env)
   		      val new_env = (case case_name of
			             SOME({name,...}) => ref(valEnv({val_map=Symbol.enter(vmap,name,propVal(new_case)),mod_map=mmap}))
				   | _ => env)
		      val (cases_left',is_mem) = Basic.removeAndCheckMemEq(new_case,cases_left,P.alEq)
		      val _ = checkConclusion(proof,new_case,new_env)
		  in
		      doArms(rest,new_case::cases_considered,cases_left') 
		  end
	in
	   doArms(tl arms,[first_case_considered],cases_left)
	end
  | evDed(A.checkDed({clauses,pos}),env,ab) = 
       (case evalDCheckClauses(clauses,env,ab) of
           SOME(d) => evDed(d,env,ab)
         | _ => evError("dcheck failed: no alternative holds",SOME(pos)))

  | evDed(A.beginDed({members,pos}),env,ab) = 
     let fun doAll([d],ab') = evDed(d,env,ab')
           | doAll(d1::(rest as (d2::more)),ab') = 
               (case evDed(d1,env,ab') of
                   propVal(p) => doAll(rest,ABaseInsert(p,ab'))
                 | _ => evError("Impossible error---a component deduction of a dbegin "^
                                "failed to produce a sentence",SOME(A.posOfDed(d1))))
         in  
           doAll(members,ab)
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
          val wv = evExp(wanted_res,env,ab)
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
                            res as propVal(Q) => if Prop.alEq(P,Q)
					         then (closeTracing(level,true);propVal(P))
                                                 else (closeTracing(level,false);
                                                       evError(msg(P,Q),SOME(pos))))
           | _ => evError(msg2(wv),SOME(A.posOfExp(wanted_res))))
      end
  | evDed(A.pickAnyDed({eigenvars,body,pos}),env,ab) = 
        let val names = map #name eigenvars
	    fun makeFreshVar({name,pos,sort_as_sym_term=NONE,sort_as_fterm=NONE,...}:A.possibly_typed_param) = 
	    	ATV.freshWithPrefix(Symbol.name(name)^"_")
	      | makeFreshVar({name,pos,sort_as_sym_term=SOME(sym_term),sort_as_fterm=NONE,sort_as_exp=SOME(se),...}) = 
	      	   let val sort_string = AthStringToMLString(evExp(se,env,ab))
                       fun isVar(str) = let val str_lst = explode str
		       	   	        in not(null(str_lst)) andalso 
					   hd(str_lst) = Names.sort_variable_prefix_as_char
					end
                   in
                       (case Terms.parseSymTerm(sort_string,isVar) of 
                           SOME(sort_as_sym_term) => let val fsort = Terms.carbonSymTermToFTerm(sort_as_sym_term)
                                                     in ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",fsort)
                                                     end)
                   end
              | makeFreshVar({name,pos,sort_as_sym_term,sort_as_fterm=SOME(sort),...}) = 
		  (let val res = ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",sort)
		   in 
		      res
		   end)
	    val fresh_vars = map makeFreshVar eigenvars 
            val (vmap,mmap) = getValAndModMaps(!env)
            val new_env = ref(valEnv({val_map=enterLst(vmap,names,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
            val res = evDed(body,new_env,ab)
        in        
               case res of
                  propVal(p) => let val P_safe = P.makeUGen(fresh_vars,p)
				    val P_preferable = SOME(P.renameQProp(List.map Symbol.name names,P_safe))
						       handle _ => NONE
			        in
				   (case P_preferable of
				       SOME(Q) => if P.alEq(P_safe,Q) then propVal(Q) 
						  else propVal(P_safe)
				     | _ => propVal(P_safe))
				end
        end
  | evDed(A.pickWitnessDed({ex_gen,var_id,inst_id,body=main_body,pos}),env,ab) =
        let val egv = evPhrase(ex_gen,env,ab)
	    fun showError() = evError("In a deduction of the form (pick-witness I F D), the value "^
		                      "of F must be an exisentially\nquantified sentence---but here "^
                                      "it was a "^valLCTypeAndString(egv),SOME(A.posOfPhrase(ex_gen)))
            val (ex_gen_val,ex_gen_var,ex_gen_body,new_ab) = 
                   (case coerceValIntoPropVal(egv) of 
                       SOME(v as propVal(egp)) => 
			 (case P.isEGen(egp) of 
			   SOME(ev,ebody) => 
			       (v,ev,ebody,(case ex_gen of 
   					     A.ded(_) => ABaseInsert(egp,ab)
                                           | _ => ab))
                           | _ => (case P.isEGenUnique(egp) of
				      SOME(ev,ebody) => 
					(v,ev,ebody,(case ex_gen of 
                                                       A.ded(_) => ABaseInsert(egp,ab)
                                                     | _ => ab))
                                    | _ => showError()))
                     | _ => showError())
            val ex_gen_var_sort = ATV.getSort(ex_gen_var)
            val unique_name = Symbol.symbol("!1")
            val fresh_var_v = AthTermVar.freshWithSortAndPrefix(Symbol.name(var_id)^"_",ex_gen_var_sort)
            val fresh_var = AT.makeVar(fresh_var_v)
            val (vmap,mmap) = getValAndModMaps(!env)
            val vmap' = enterLst(vmap,[unique_name,var_id],[ex_gen_val,termVal(fresh_var)])
            val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
            val id_prop = P.replaceVarByVar(ex_gen_var,fresh_var_v,ex_gen_body)
            val new_env' = (case inst_id of
		               SOME(id) => ref(valEnv({val_map=enterLst(vmap',[id],[propVal(id_prop)]),mod_map=mmap}))
                             | _ => new_env)
            val new_ded = A.withWitnessDed({eigenvar_exp=A.idExp({msym=msym var_id,mods=[],no_mods=true,sym=var_id,pos=A.posOfPhrase(ex_gen)}),
                                            ex_gen=A.exp(A.idExp({msym=msym unique_name,mods=[],no_mods=true,sym=unique_name,pos=A.posOfPhrase(ex_gen)})),
                                            body=main_body,pos=pos})
        in
           evDed(new_ded,new_env',new_ab)
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
  | evDed(d as A.pickWitnessesDed({ex_gen,var_ids,...}),env,ab) = 
        let val egv = evPhrase(ex_gen,env,ab)
	    fun showError() = evError("In a deduction of the form (pick-witnesses I1 ... In F D), "^
			 	      "the value of F must be an exisentially\nquantified "^
				      "sentence---but here it was a "^
                                      valLCTypeAndString(egv),SOME(A.posOfPhrase(ex_gen)))
            val (ex_gen_val,ex_gen_vars,ex_gen_body,new_ab) = 
                   (case coerceValIntoPropVal(egv) of 
                       SOME(v as propVal(egp)) =>
			 (case P.isEGen(egp) of 
			    SOME(ev,ebody) => 
	                         let val evars = getFrontQuantVars(egp)
				 in 
	                           (v,evars,ebody,(case ex_gen of 
        	                                     A.ded(_) => ABaseInsert(egp,ab)
                	                           | _ => ab))
				 end
		         | _ => (case P.isEGenUnique(egp) of
				    SOME(ev,ebody) => 
		                         let val evars = getFrontQuantVars(egp)
					 in 
		                           (v,evars,ebody,(case ex_gen of 
                	                             A.ded(_) => ABaseInsert(egp,ab)
                        	                   | _ => ab))
					 end
		                     | _ => showError()))
		    | _ => showError())
	  val (wit_count,evar_count) = (length(var_ids),length(ex_gen_vars))
          val _ = if wit_count >  evar_count then
		      evError("More witnesses ("^(Int.toString(wit_count))^") requested than\n"^
			      "could be obtained from the sentence:\n "^(prettyValToString(ex_gen_val))^
			      "\nThe above is existentially quantified over only "^(Int.toString(evar_count))^
			      (if evar_count = 1 then " variable" else " variables"),
			      SOME(A.posOfPhrase(ex_gen)))
		  else ()
       in
  	 evDed(desugarPW(d,env,ab,evPhrase),env,new_ab)
       end
  | evDed(A.genOverDed({eigenvar_exp,body,pos,...}),env,ab) =  
      let fun msg(vstr) = "Failed universal generalization.\nThe eigenvariable "^vstr^
                          " occurs free in the current assumption base"
          fun emsg1(v) = "In a deduction of the form (generalize-over E D), the value of E must be "^
                         "a variable---but here it was a "^valLCTypeAndString(v)
          fun emsg2(v) = "In a deduction of the form (generalize-over E D), the value of E must be "^
                         "a variable---but here it was the non-variable term "^valToString(v)
          fun printVar(v) = Names.variable_prefix^(ATV.toStringDefault(v))
          val ev = evExp(eigenvar_exp,env,ab)
      in
         case coerceValIntoTermVal(ev) of 
            SOME(termVal(t)) => 
                 (case AT.isVarOpt(t) of
                     SOME(v) => 
                         if Ab.occursFreeUpToSubsorting(v,ab) then
                            evError(msg(printVar(v)),SOME(A.posOfExp(eigenvar_exp)))
                         else 
                            let val res = evDed(body,env,ab)
                                val res_prop = (case coerceValIntoPropVal(res) of 
                                                   SOME(propVal(P)) => let val res = propVal(P.makeUGen([v],P))
 						                                       handle Basic.FailLst(msgs) => 
                                                                                              evError(Basic.failMsgsToStr(msgs),
                                                                                                      SOME(pos))
                                                                       in 
                                                                          res
                                                                       end                                     
                                                 | _ => evError("Impossible error encountered in universal "^
                                                                "generalization---the body of the deduction "^
                                                                "failed to produce a sentence",
                                                                SOME(A.posOfDed(body))))
                            in
                               res_prop
                            end
                   | _ => evError(emsg2(ev),SOME(A.posOfExp(eigenvar_exp))))
           | _ => evError(emsg1(ev),SOME(A.posOfExp(eigenvar_exp)))
      end 
  | evDed(A.withWitnessDed({eigenvar_exp,ex_gen,body,pos}),env,ab) = 
     let fun msg(vstr) = "Failed existential instantiation---the witness variable "^
                         "\noccurs free in the current assumption base"
         fun emsg1(v) = "In a deduction of the form (with-witness E F D), the value of E must "^
                        "be a variable---but here it was a "^valLCTypeAndString(v)
         fun emsg2(v) = "In a deduction of the form (with-witness E F D), the value of E must "^
                        "be a variable---but here it was the non-variable term "^valToString(v)
         val ev = evExp(eigenvar_exp,env,ab)
     in
       case coerceValIntoTerm(ev) of
        SOME(t) => 
         (case AT.isVarOpt(t) of
            SOME(fresh_var) => 
              if Ab.occursFree(fresh_var,ab) then
                 evError(msg(AthTermVar.name(fresh_var)),SOME(A.posOfExp(eigenvar_exp)))
              else 
               let val egenv = evPhrase(ex_gen,env,ab)
               in
                (case coerceValIntoProp(egenv) of  
                    SOME(specP) => 
		     (case P.isEGen(specP) of 
	               SOME(v,pbody) =>
                         if A.isDeduction(ex_gen) orelse ABase.isMember(specP,ab) then
                            let val pbody' = P.replace(v,AT.makeVar(fresh_var),pbody)
                                val pbody_components = Prop.decomposeConjunctions(pbody')
                                val new_ab = ABaseAugment(ab,pbody_components)
                                val final_res = evDed(body,env,new_ab)
                            in
                                (case final_res of 
                                   v as propVal(p') => 
                                     if P.occursFree(fresh_var,p') then 
                                         evError("Failed existential instantiation---the witness variable "^
                                                  "\noccurs free in the resulting sentence",SOME(pos))
                                     else v
                                 | _ => evError("Impossible error encountered in existential instantiation"^
                                                "the deduction body did not produce a sentence",
                                                SOME(A.posOfDed(body))))
                            end
                         else
			   let val specP_str = P.toPrettyString(0,specP,makeVarSortPrinter())
			   in
                             evError("Existential sentence to be instantiated is not in\nthe assumption base: "^
                                     (Util.decide(specP_str,16)),SOME(A.posOfPhrase(ex_gen)))
			   end
                       | _ => 
                        (case P.isEGenUnique(specP) of 
		         SOME(v,pbody) =>
                         if A.isDeduction(ex_gen) orelse ABase.isMember(specP,ab) then
                            let val fresh_term = AT.makeVar(fresh_var)
                                val instantiated_ex_prop = P.replace(v,fresh_term,pbody)
                                val new_var = ATV.freshWithSort(ATV.getSort(fresh_var))
                                val new_term = AT.makeVar(new_var)
                                val new_prop = P.replace(v,new_term,pbody)
                                val eq_prop1 = P.makeEquality(new_term,fresh_term)
                                val eq_prop2 = P.makeEquality(fresh_term,new_term)
                                val uniqueness_prop1 = P.makeUGen([new_var],P.makeConditional(new_prop,eq_prop1))
                                val uniqueness_prop2 = P.makeUGen([new_var],P.makeConditional(new_prop,eq_prop2))
                                val new_ab = ABaseAugment(ab,[uniqueness_prop1,uniqueness_prop2])
                                val final_res = evDed(body,env,new_ab)
                            in        
                                  (case final_res of 
                                      v as propVal(p') => 
                                        if P.occursFree(fresh_var,p') then
                                           evError("Failed existential instantiation---the witness variable "^
                                                  "\noccurs free in the resulting "^
                                                  "sentence",SOME(pos))
                                        else v
                                    | _ => evError("Impossible error encountered in existential instantiation"^
                                                   "---the deduction body did not produce a sentence",
                                                   SOME(A.posOfDed(body))))
                            end
                         else
                             evError("Existential sentence to be instantiated is not in the assumption base: "^
                                      P.toPrettyString(0,specP,makeVarSortPrinter()),
						       SOME(A.posOfPhrase(ex_gen)))))
                  | _ => evError("In a deduction of the form (with-witness E F D) or (pick-witness E F D), the "^
                                 "value of F must be an existentially quantified\nsentence---but here"^
                                 " it was a "^valLCTypeAndString(egenv),SOME(A.posOfPhrase(ex_gen))))
               end
          | _ => evError(emsg2(ev),SOME(A.posOfExp(eigenvar_exp))))
      | _ => evError(emsg1(ev),SOME(A.posOfExp(eigenvar_exp)))
     end
  | evDed(A.letRecDed({bindings,body,pos}),env,ab) = 
       let val rec_env = ref(!env)
           fun getVals([],map) = map 
             | getVals((b:A.binding as {bpat,def,pos})::more,map) = 
                let val mv = evPhrase(def,rec_env,ab)
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
  | evDed(A.fromDed({conclusion,premises,pos}),env,ab) = 
       let fun getProps(val_lst,list_name,pos,env) = 
                 let fun msg(v,i) = "Wrong kind of value found in the "^ordinal(i)^
				     " position of "^list_name^"---"^expectInOneLine(propLCType,v)
                     fun getProps([],results,i) = rev results
                       | getProps(v::rest,results,i) = 
                           (case coerceValIntoProp(v) of 
                              SOME(P) => getProps(rest,P::results,i+1)
                       | _ => evError(msg(v,i),SOME(pos)))
                  in
                     getProps(val_lst,[],1)
                  end
       in
         (case coerceValIntoProp(evExp(conclusion,env,ab)) of 
             SOME(P) => (case evExp(premises,env,ab) of
                          listVal(pvals) => 
                            let val premise_props = getProps(pvals,"the list argument of "
                                                                  ^" FROM deduction ",
							     A.posOfExp(premises),env)
                            in 
			       unitVal
                            end)
            | _ => raise Basic.Never)
       end
  | evDed(A.infixAssumeDed({bindings,body,pos}),env,ab) = 
	let fun getPropsAndEnv([],props,env) = (props,env)
	      | getPropsAndEnv((b:A.binding as {bpat,pos,def,...})::rest,props,env) = 
	                let val pval = evPhrase(def,env,ab)
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
	    val res_val = evDed(body,new_env,ABase.augment(ab,hyps'))
            in
	      (case coerceValIntoProp(res_val) of
	         SOME(q) => let val conj = (case hyps of
					      [P] => P
					    |  _  => Prop.makeConjunction(hyps))
			    in
			       propVal(Prop.makeConditional(conj,q))
			    end
               | _ => evError("Impossible error encountered in assume deduction: the body of "^
                              "the deduction did not produce a sentence",SOME(A.posOfDed(body))))
	   end
and
   doSupposeAbsurd(hyp:A.phrase,hyp_name_pat:A.pattern option,body:A.deduction,pos:A.position,env,ab) = 
    let val hypv = evPhrase(hyp,env,ab)
    in
      (case coerceValIntoPropVal(hypv) of
          SOME(pval as propVal(p)) => 
              let val new_env = 
                       (case hyp_name_pat of
                           SOME(bpat) => (case matchPat(pval,bpat,makeEvalExpFunction (env,ab)) of 
                                             SOME(map,_) => ref(augmentWithMap(!env,map))
                                           | _ => evError("Suppose-absurd pattern failed to match "^ 
                                                          "the corresponding value, the\n"^
                                                          (valLCTypeAndStringNoColon pval),
                                                          SOME(A.posOfPat(bpat))))
                          | _ => env)
                  val body_res = evDed(body,new_env,ABaseAugment(ab,[p]))
                  in
                     (case coerceValIntoProp(body_res) of
                         SOME(p') => if Prop.isBooleanFalse(p') then
                                           propVal(Prop.makeNegation(p))
                                        else
                                           evError("The body of a suppose-absurd deduction"
                                                  ^" must derive the sentence false---but here the "^
                                                  "result was the sentence\n"^pprintProp(p'),
                                                  SOME(A.posOfDed(body))))
              end
        | _ => evError("The hypothesis of a suppose-absurd deduction must be a sentence---"^
                       "but here it is a "^valLCTypeAndString(hypv),SOME(A.posOfPhrase(hyp))))
    end
and evPhrase(A.exp(e),env:value_environment ref,ab) = evExp(e,env,ab)
  | evPhrase(A.ded(d),env:value_environment ref,ab) = evDed(d,env,ab)
and
coercePositionlessValsIntoProps(vals,meth_name) = 
     let fun f([],res,_) = res
           | f(v::more,res,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,P::res,i+1)
                     | _ => primError(wrongArgKind(meth_name,i,propLCType,v)))
     in
        f(vals,[],1)
     end                                            
and
coerceSolePositionedValsIntoProps(vals,pos,name) = 
     let fun f([],res,_) = rev(res)
           | f(v::more,res,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,P::res,i+1)
                     | _ => evError(wrongArgKind(name,i,propLCType,v),SOME(pos)))
     in
        f(vals,[],1)
     end
and 
coercePositionedValsIntoProps(vals,pos_list,name) = 
     let fun f([],res,_,_) = rev(res)
           | f(v::more,res,pos::rest,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,P::res,rest,i+1)
                     | _ => evError(wrongArgKind(name,i,propLCType,v),SOME(pos)))
     in
        f(vals,[],pos_list,1)
     end                                                 
and
coercePositionedValsIntoPropsAndPositionCopies(vals,pos,meth_name) = 
     let fun f([],res,_) = res
           | f(v::more,res,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,(P,pos)::res,i-1)
                     | _ => evError("Wrong kind of value given as argument to "^meth_name^"---"^(expect(propLCType,v)),SOME pos))
     in
        f(vals,[],length vals)
     end                                            
and evalCheckClauses(clauses,env,ab) = 
     let fun f([]) = NONE
           | f({test=A.boolCond(phr),result}::more) =
                  (case evPhrase(phr,env,ab) of 
                                 propVal(P) => (case P.isAtom(P) of
	 			                   SOME(t) => if isTrueTerm(t) then SOME(result) else f(more)
            				         | _ => f(more))
                                 | termVal(t) => if isTrueTerm(t) then SOME(result) else f(more)
	      		         | _ => f(more))
           | f({test=A.elseCond,result}::more) = SOME(result)
     in
        f(clauses)
     end
and evalDCheckClauses(clauses,env,ab) = 
     let fun f([]) = NONE
           | f({test=A.boolCond(phr),result}::more) =
                  (case evPhrase(phr,env,ab) of 
                                 propVal(P) =>
				   (case P.isAtom(P) of
				       SOME(t) => if isTrueTerm(t) then SOME(result) else f(more)
				     | _ => f(more))
                                 | termVal(t) => if isTrueTerm(t) then SOME(result)
	 					 else f(more)
	      		         | _ => f(more))
           | f({test=A.elseCond,result}::more) = SOME(result)
     in
        f(clauses)
     end     
in
   (fn (e,env,ab) => (
                      let val res = evExp(e,env,ab) 
                      in
                        res
                      end),
    fn (d,env,ab) => let (** val _ = print("\nOLD-FASHIONED DEDUCTION EVALUATION!\n") **)
                     in
                        (evDed(d,env,ab))
                     end,
    fn (p,env,ab) => (let val res = evPhrase(p,env,ab)
                    in
                       res
                    end),
    fn x => (evalClosure(x)),
    fn x => (evalMethodClosure(x)),
    fn x => (evalMethodApp(x)),
    fn x => (makeEvalExpFunction(x)),
    fn x => (doSupposeAbsurd(x)),
    fn x => (evalDCheckClauses(x)),
    fn x => coercePositionlessValsIntoProps(x),
    fn x => coercePositionedValsIntoProps(x),
    fn x => coercePositionedValsIntoPropsAndPositionCopies(x))
end

fun getNeededPremises(arg_vals,method_sym) = 
   let fun f(v) = (case coerceValIntoPropVal(v) of 
                      SOME(v') => v' 
                    | _ => (print("\nNon-sentential input: " ^ (valToString v));raise Basic.Never))
   in
      []
   end

fun primMethodSententialArgPos(code,arg_pos) = 
     if ((code = Names.eqReflexPrimMethod_symbol) orelse 
         ((code = Names.uspecPrimMethod_symbol) andalso (arg_pos = 2)) orelse
         ((code = Names.egenPrimMethod_symbol) andalso (arg_pos = 2)) orelse
         ((code = Names.leftEitherPrimMethod_symbol) andalso (arg_pos = 2)) orelse
         ((code = Names.rcongPrimMethod_symbol) andalso (arg_pos = 2)) orelse
         ((code = Names.fcongPrimMethod_symbol) andalso (arg_pos = 1)) orelse
         ((code = Names.rightEitherPrimMethod_symbol) andalso (arg_pos = 1))) then false else true

(**

    Proof-tracking version of the interpreter (WT = "with tracking"). This version should produce a type-alpha certificate for
    any proof that terminates, no matter how much computation it involves. This was implemented as a separate collection
    of functions due to the intensive amount of logging that is needed. It might make sense to refactor by bundling this 
    capability into the main evaluation functions - if it can be shown that doing so has no observable effect on performance
    (proof-checking latency in particular) when this option is disabled, which is the typical use case. 
    
**)

val (evalExpWT,
     evalDedWT,
     evalPhraseWT,
     evalClosureWT,
     evalMethodClosureWT,
     coerceLstWT,
     coercePositionedValsIntoPropsWT,
     coercePositionedValsIntoPropsAndPositionCopiesWT) =
let 
    val iarm_stack:iarm_type LStack.stack ref = ref(LStack.empty)
    fun initIndStack() = iarm_stack := LStack.empty
    fun initCallStack() = call_stack := LStack.empty 
    fun evExp(expression,env,ab,premises:PropSet.prop_set) = 
      (case expression of
        A.idExp(id as {sym,no_mods,...}) => 
           (case !env of
             (e as (valEnv({val_map,...}))) => 
                 let val res = if no_mods then Symbol.lookUp(val_map,sym) else lookUp(e,#mods(id),sym)
                 in
                   (case res of
                       SOME(v) => v
                      | _ => evError("Could not find a value for "^(MS.name (#msym(id))),SOME(#pos(id))))
                 end)
     | A.unitExp(_) => unitVal
     | app_exp as A.BAppExp({proc,arg1,arg2,pos}) => 
      let val head_val = evPhrase(proc,env,ab,premises)
      in
        (case head_val of
             closBFunVal(body,p1,p2,clos_env as ref(valEnv({val_map,mod_map,...})),{name,...}) => 
                   let val v1 = evPhrase(arg1,env,ab,premises)
                       val v2 = evPhrase(arg2,env,ab,premises)
                       val vm = Symbol.enter(Symbol.enter(val_map,p1,v1),p2,v2)
                       val _ = addPos (!name,pos)
                   in 
                      evExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab,premises)                   
                   end
           | termConVal(regFSym(some_fsym)) =>
                     (let 
                          val name = D.fsymName(some_fsym)
                          val arg_val1 = evPhrase(arg1,env,ab,premises)
                          val arg_val2 = evPhrase(arg2,env,ab,premises)                       
                          val term_arg1 =  (case coerceValIntoTerm(arg_val1) of
                                             SOME(t) => (case AT.isConstant(t) of 
                 			                   SOME(name) =>  let val (_,sort,is_poly,_) = Data.getSignature(name)
 					                                  in
						                            if FTerm.termEq(sort,AT.getSort(t)) then 
						                               AT.makeSortedConstantAux(name,sort,is_poly)
                                                                            else t
                                                                          end
                                                         | _ => t)
                                            | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val1),SOME(pos)))
                          val term_arg2 =  (case coerceValIntoTerm(arg_val2) of
                                             SOME(t) => (case AT.isConstant(t) of 
                 			                   SOME(name) =>  let val (_,sort,is_poly,_) = Data.getSignature(name)
 					                                  in
						                            if FTerm.termEq(sort,AT.getSort(t)) then 
						                               AT.makeSortedConstantAux(name,sort,is_poly)
                                                                            else t
                                                                          end
                                                         | _ => t)
                                            | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val2),SOME(pos)))
                          val term_res = applyBinaryTermConstructor(name,term_arg1,term_arg2,pos)
                      in
                         termVal(term_res)
                      end)
           | propConVal(con) => 
                  if A.isQuantPropCon(con) then
 	             let val pval = evPhrase(arg2,env,ab,premises)
 	             in
	               (case coerceValIntoProp(pval) of
 	                  SOME(p) => (let val var_val = evPhrase(arg1,env,ab,premises)
	                                  val term_var = (getTermVar var_val) handle _ => evError(wrongArgKind(A.propConToString(con),1,varLCType,var_val),SOME(pos))
	                                  val res_prop = makeQuantProp(SOME con,[term_var],p)
						           handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
	                              in
	                                propVal(res_prop) 
	                              end)
	                 | _ => evError(wrongArgKind(A.propConToString(con),2,propLCType,pval),SOME(A.posOfPhrase(arg2))))
	             end
                  else
 	                 let val arg_val1 = evPhrase(arg1,env,ab,premises)
                             val arg_val2 = evPhrase(arg2,env,ab,premises)
                             val prop1 = (case coerceValIntoProp(arg_val1) of  
                                             SOME(P) => P
                                           | _ => evError(wrongArgKind(valLCTypeAndStringNoColon(propConVal(con)),1,propLCType,arg_val1),SOME(A.posOfPhrase(arg1))))
                             val prop2 = (case coerceValIntoProp(arg_val2) of  
                                             SOME(P) => P
                                           | _ => evError(wrongArgKind(valLCTypeAndStringNoColon(propConVal(con)),2,propLCType,arg_val2),SOME(A.posOfPhrase(arg2))))
                             val res = (case con of
                                          A.andCon => P.makeConjunction([prop1,prop2])
                                        | A.orCon => P.makeDisjunction([prop1,prop2])
                                        | A.ifCon => P.makeConditional(prop1,prop2)
                                        | A.iffCon => P.makeBiConditional(prop1,prop2)
                                        | _ => evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),2,1),SOME(pos)))
                                           handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                         in
                           propVal(res)
	                 end
           | primBFunVal(f,_) => (f(evPhrase(arg1,env,ab,premises),evPhrase(arg2,env,ab,premises),env,ab)
                                      handle PrimError(msg) => evError(msg,SOME(pos)) 
                                 )
           | funVal(f,name,_) => 
                           (let val arg_val_1 = evPhrase(arg1,env,ab,premises) 
                                val arg_val_2 = evPhrase(arg2,env,ab,premises)
                            in
		               f([arg_val_1,arg_val_2],env,ab)
                            end handle PrimError(msg) => evError(msg,SOME(pos)))
           | _ => (evalApp(proc,[arg1,arg2],pos,env,ab,premises)))
      end
  | app_exp as A.UAppExp({proc,arg,pos}) => 
      let val head_val = evPhrase(proc,env,ab,premises)
      in
        (case head_val of
             closUFunVal(body,p1,clos_env as ref(valEnv({val_map,mod_map,...})),{name,...}) =>
                   let val vm = Symbol.enter(val_map,p1,evPhrase(arg,env,ab,premises))
                       val _ = addPos(!name,pos)
		       val  (dyn_vmap,dyn_mod_map) = getValAndModMaps(!env)
		       val  (clos_vmap,clos_mod_map) = getValAndModMaps(!clos_env)
                   in 
                      evExp(body,ref(valEnv({val_map=vm,mod_map=mod_map})),ab,premises)                   
                   end
           | primUFunVal(f,_) => (f(evPhrase(arg,env,ab,premises),env,ab)
                                     handle PrimError(msg) => evError(msg,SOME(pos)) 
                                 )
           | termConVal(regFSym(some_fsym)) =>
                     (let val name = D.fsymName(some_fsym)
                          val arg_val = evPhrase(arg,env,ab,premises)
                          val term_arg =  (case coerceValIntoTerm(arg_val) of
                                             SOME(t) => (case AT.isConstant(t) of 
                 			                   SOME(name) =>  let val (_,sort,is_poly,bits) =  Data.getSignature(name)
 					                                  in
						                            if FTerm.termEq(sort,AT.getSort(t)) then 
						                               AT.makeSortedConstantAux(name,sort,is_poly)
                                                                            else t
                                                                          end
                                                         | _ => t)
                                            | _ => evError(wrongArgKindExpectationOnly(termLCType,arg_val),SOME(pos)))
                          val term_res = applyTermConstructor(name,1,[term_arg],pos)
                      in
                         termVal(term_res)
                      end)
           | propConVal(con) => 
                     (case con of
                         A.notCon => let val res_prop = 
                                               (let val nav = (case evPhrase(arg,env,ab,premises) of	
					                          listVal(vl) => 
                                                                    (case vl of
                                                                        [v] => v
                                                                      | _ => let val n = Int.toString(length(vl))
  					                                     in
							                       evError("Wrong number of arguments ("^n^") given to\n"^
								                       (valLCTypeAndStringNoColon(propConVal(con)))^
                                                                                       ". Exactly one argument is required",SOME(pos))
							                     end)
 				                                | v => v)
                                               in
                                                  case coerceValIntoProp(nav) of
                                                      SOME(p) => P.makeNegation(p) 
                                                     | _ => evError(wrongArgKind(S.name(N.not_symbol),1,propLCType,nav),SOME(pos))
                                               end)
                                    in 
                                      propVal(res_prop)
                                    end
                    | _ => let val arg_val = evPhrase(arg,env,ab,premises)
                           in
                             (case con of
                                 A.andCon => let val arg_vals = (case arg_val of 
  			 	                                   listVal(vl) => if null(vl) then 
                                                                                     evError("Empty list of arguments given to "^
                                                                                             (valLCTypeAndStringNoColon(propConVal(con))),SOME(pos))
                                                                                  else vl 
                                                                  | _ => [arg_val])
                                                 val plst = coerceSolePositionedValsIntoProps(arg_vals,pos,"sentential constructor and")
                                                 val res = (P.makeConjunction plst) handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                                             in
                                               propVal(res) 
                                             end
                               | A.orCon => let val arg_vals = (case arg_val of 
  			 	                                   listVal(vl) => if null(vl) then 
                                                                                     evError("Empty list of arguments given to "^N.or_name,SOME(pos))
                                                                                  else vl 
                                                                  | _ => [arg_val])
                                                val plst = coerceSolePositionedValsIntoProps(arg_vals,pos,"sentential constructor or")
                                                val res = (P.makeDisjunction plst) handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                                             in
                                                propVal(res)
                                             end
                              | _ => (case arg_val of
                                         listVal(vals as [v1,v2]) => 
                                             let val [p1,p2] = coerceSolePositionedValsIntoProps(vals,pos,valLCTypeAndStringNoColon(propConVal(con)))
                                                 val res_prop = (if con = A.ifCon then P.makeConditional(p1,p2)  
                                                                 else if con = A.iffCon then P.makeBiConditional(p1,p2)
                                                                 else evError("Wrong number of arguments (1) given to "^(A.propConToString(con)),SOME(pos)))
                                                                 handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),SOME(pos))
                                             in 
                                                propVal(res_prop)
                                             end
                                       | _ => let val arg_num = (case arg_val of
                                                                    listVal(vals) => length(vals)  
                                                                  | _ => 1)
                                              in
                                                if A.isQuantPropCon(con) then
                                                   evError("Wrong number of arguments ("^(Int.toString(arg_num))^") given to\n"^
                                                           (valLCTypeAndStringNoColon(propConVal(con)))^". At least two arguments are required",SOME(pos))
                                                else evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),arg_num,1),SOME(pos))
                                              end))
                           end)
           | subVal(sub) => (case evPhrase(arg,env,ab,premises) of
                                         v as termVal(t) =>  
                                                 (case applySubToValPosLst(sub,[(v,pos)]) of
                                                     listVal([tv]) => tv)
                                       | v as propVal(p) => 
                                                 (case applySubToValPosLst(sub,[(v,pos)]) of
                                                     listVal([pv]) => pv)
                                       | v as listVal(vals) => applySubToValLst(sub,vals,pos)
                                       | v => (case coerceValIntoTerm(v) of
                                                  SOME(t) => 
                                                    (case applySubToValPosLst(sub,[(termVal(t),pos)]) of
                                                       listVal([tv]) => tv)
                                                | _ => (case coerceValIntoProp(v) of
                                                          SOME(P) => (case applySubToValPosLst(sub,[(v,pos)]) of
		                                                        listVal([pv]) => pv)
							| _ => evError("Wrong kind of argument supplied to a "^
                                                               "substitution application; "^expect(termLCType,v),
                                                               SOME(A.posOfPhrase(arg))))))
           | mapVal(m) => (case evPhrase(arg,env,ab,premises) of
                              v => (case Maps.find(m,v) of
                                        SOME(res) => res
                                           | _ => evError("Failed map application: no such key in the map: " ^ (valLCTypeAndString v),SOME(A.posOfPhrase(arg)))))
           | funVal(f,name,_) => 
                           (let val arg_val = evPhrase(arg,env,ab,premises) 
                            in
		               f([arg_val],env,ab)
                            end                          
                                    handle PrimError(msg) => evError(msg,SOME(pos)) 
                            )
           | _ => (evalApp(proc,[arg],pos,env,ab,premises)))
      end
  | A.matchExp({discriminant,clauses,pos}) => 
      let val discrim_value = evPhrase(discriminant,env,ab,premises)
	  val e_fun = makeEvalExpFunction (env,ab,premises)
          fun tryClauses([]:A.match_clause list) =  
                  evError("match failed---the "^valLCTypeAndStringNoColon(discrim_value)^
                          "\ndid not match any of the given patterns",SOME(pos))
            | tryClauses({pat,exp}::more) = 
                 (case matchPat(discrim_value,pat,e_fun) of
                     SOME(map,_) => 
                        let val new_env = ref(augmentWithMap(!env,map))
                            in
                              evExp(exp,new_env,ab,premises)
                        end
                   | _ => tryClauses(more))
          in
            tryClauses(clauses)
      end                
  | (ev_e as A.letExp({bindings,body,pos})) => 
       let
           fun doLetExp([]:A.binding list,env1) = 
                 let 
                 in
                    evExp(body,env1,ab,premises)
                 end
             | doLetExp({bpat,def,pos}::more,env1) = 
                  let val val1 = evPhrase(def,env1,ab,premises)

                  in
                     (case matchPat(val1,bpat,makeEvalExpFunction (env1,ab,premises)) of 
                        SOME(map,_) => let val tval = (case Symbol.lookUp(map,Symbol.symbol("bar")) of
                                                        SOME(v) => v | _ => unitVal)

                                         val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                     in
                                       doLetExp(more,new_env)
                                     end 
                      | _ => evError("Let pattern: "^(A.printPat(bpat))^
                                      " failed to match\nthe corresponding value, the "^
                                     (valLCTypeAndStringNoColon val1),
                                     SOME(A.posOfPat(bpat))))
                  end
           in
              doLetExp(bindings,env)
       end
  | app_exp as A.appExp({proc=proc_phrase,args,pos,alt_exp}) => evalApp(proc_phrase,args,pos,env,ab,premises)
  | A.listExp({members,pos}) => listVal(map (fn p => evPhrase(p,env,ab,premises)) members)
  | A.termVarExp({term_var,...}) => termVal(AT.makeVar(term_var))
  | A.taggedConSym({name,sort_as_tagged_symterm,sort_as_fterm=SOME(tagged_sort),pos,...}) => termVal(AT.makeSortedConstant(name,tagged_sort))
  | A.taggedConSym({name,sort_as_tagged_symterm,sort_as_fterm=NONE,pos,...}) => raise Basic.Never
  | A.numExp({number=num,pos}) => termVal(AT.makeNumTerm(num))        
  | A.checkExp({clauses,pos}) => 
         (case evalCheckClauses(clauses,env,ab,premises) of
             SOME(e) => evExp(e,env,ab,premises)
           | _ => evError("check error: all alternatives failed",SOME(pos)))
  | A.logicalOrExp({args,pos}) => 
      let fun f([]) = false_val
            | f(p::more) = let val v = evPhrase(p,env,ab,premises)
                           in
                            (case getBool(v) of
                                 SOME(true) => true_val              
                               | SOME(false) => f(more)
                               | _ => logError("or",A.posOfPhrase(p),v))
                            end
      in
         f(args)
      end
  | A.logicalAndExp({args,pos}) => 
      let fun f([]) = true_val
            | f(p::more) = let val v = evPhrase(p,env,ab,premises)
                           in 
                             (case getBool(v) of
                               SOME(true) => f(more)
                             | SOME(false) => false_val
                             | _ => logError("and",A.posOfPhrase(p),v))
                           end
      in
         f(args)
      end
  | exp as A.functionExp({params,pos,body,...}) =>
          (case params of
               [p1,p2] => closBFunVal(body,A.pwpToSym(p1),A.pwpToSym(p2),env,{name=ref(""),prec=ref(Options.lowest_fsymbol_precedence),assoc=ref(NONE)})
             | [p] => closUFunVal(body,A.pwpToSym(p),env,{name=ref(""),prec=ref(Options.lowest_fsymbol_precedence)})
             | _ => closFunVal(exp,env,{name=ref(""),prec=ref(Options.defaultPrec(length params)),assoc=ref(NONE)}))
  | A.tryExp({choices,pos}) =>
       let fun tryExps([]) = NONE
             | tryExps(e::more) = 
                     (case (SOME(evExp(e,env,ab,premises)) handle _ => NONE) of
                         NONE => tryExps(more)
                       | r => r)
           in
             (case tryExps(choices) of
                 NONE => evError("Try expression error; all alternatives failed.",SOME(pos))
               | (SOME v) => v)
       end
  | exp as A.methodExp({params,body,pos,...}) => 
          (case params of
               [p1,p2] => closBMethodVal(body,A.pwpToSym(p1),A.pwpToSym(p2),env,ref(""))
             | [p]     => closUMethodVal(body,A.pwpToSym(p),env,ref(""))
             | _       => closMethodVal(exp,env))
  | A.quotedIdeExp({name,pos}) => termVal(AT.makeIdeConstant(name))
  | A.stringExp({mem_index,...}) => RSA.sub(SV.string_literals,mem_index)
  | A.charExp({code,...}) => charVal(code)
  | A.letRecExp({bindings,body,pos}) => 
       let val rec_env = ref(!env)
           fun getVals([],map) = map 
             | getVals((b:A.binding as {bpat,def,pos})::more,map) = 
                let val mv = evPhrase(def,rec_env,ab,premises)
                in
                  (case matchPat(mv,bpat,makeEvalExpFunction (rec_env,ab,premises)) of 
                      SOME(map',_) => getVals(more,Symbol.augment(map,map'))
                    | _ => evError("Letrec pattern failed to match the corresponding value, the\n"^ 
                                   (valLCTypeAndStringNoColon mv),
                                   SOME(A.posOfPat(bpat))))
                end
           val pmap = getVals(bindings,S.empty_mapping)
           val (vmap,mod_map) = getValAndModMaps(!env)
           val new_env = valEnv({val_map=Symbol.augment(vmap,pmap),mod_map=mod_map})
           val _ = rec_env := new_env
           in
              evExp(body,ref(new_env),ab,premises)
       end
  | A.whileExp({test,body,pos}) =>
       let fun evPh(p) = evPhrase(p,env,ab,premises)
       in
         (while (let val v = evPh(test) 
                 in 
                   (case coerceValIntoTerm(v) of
                           SOME(b) => if isTrueTerm(b) then true
                                      else if AT.termEq(b,false_term) then false
                                      else evError("Test phrase of while loop failed to produce true or false",
                                                   SOME(pos))
                        | _ => evError("The test phrase of a while loop must produce either true or false---"^
                                       "here it produced a "^valLCTypeAndString(v),
                                       SOME(A.posOfPhrase(test))))
                 end)
          do evPh(body);
         unitVal)
       end
  | A.beginExp({members,pos}) => 
       let fun f([]) = unitVal
             | f([p]) = evPhrase(p,env,ab,premises)
             | f(p1::p2::more) = let val _ = evPhrase(p1,env,ab,premises)
                                 in f(p2::more) end 
       in
          f(members)
       end
  | A.refExp({cell_exp,pos}) =>
          (case evExp(cell_exp,env,ab,premises) of
              cellVal(v) => !v
            | _ => evError("Attempt to dereference a non-cell value",SOME(pos)))
  | A.setCellExp({cell_exp,set_phrase,pos}) => 
        (case evExp(cell_exp,env,ab,premises) of
            cellVal(cv) => (cv := evPhrase(set_phrase,env,ab,premises);unitVal)
          | _ => evError("Attempt to modify a non-cell value",SOME(pos)))
  | A.cellExp({contents,pos}) => cellVal(ref(evPhrase(contents,env,ab,premises)))
  | A.opExp({op_exp,pos}) => evExp(op_exp,env,ab,premises)
  | A.vectorInitExp({length_exp,init_val,pos}) => 
      let val msg = "Given term does not represent a valid vector size"
      in
          (case (coerceValIntoTerm(evExp(length_exp,env,ab,premises))) of
              SOME(t) => (case (AthTerm.getNumVal t) of 
                             SOME(A.int_num(n,_),false) => 
                                if n < 0 then 
  			  	   evError(msg,SOME(A.posOfExp(length_exp)))
    		                else 
                                   vectorVal(Array.array(n,evPhrase(init_val,env,ab,premises)))
                           | _ => evError("Wrong sort of term given as the length (first) argument "^ 
                                          "to vector initialization", 
 				          SOME(A.posOfExp(length_exp))))
            | _ => evError("Wrong kind of value given as first argument to vector initialization",
			    SOME(A.posOfExp(length_exp))))
      end
  | A.vectorSetExp({vector_exp,index_exp,new_val,pos}) => 
         (case evExp(vector_exp,env,ab,premises) of
             vectorVal(vec) => 
               (case (coerceValIntoTerm(evExp(index_exp,env,ab,premises))) of
                  SOME(t) => (case (AthTerm.getNumVal t) of 
                                 SOME(A.int_num(n,_),false) => 
                                    if n < 0 orelse n >= Array.length(vec) then
                                       evError("Vector subscript out of bounds",SOME(A.posOfExp(index_exp)))
                                    else 
                                       (Array.update(vec,n,evPhrase(new_val,env,ab,premises));unitVal)
                               | _ =>  evError("Given term does not represent a valid vector subscript",SOME(A.posOfExp(index_exp))))
                | _ => evError("Wrong kind of value given as subscript to vector-set!",SOME(A.posOfExp(index_exp))))
           | _ => evError("Attempt to vector-set! a non-vector value",SOME(A.posOfExp(vector_exp))))
  | A.vectorSubExp({vector_exp,index_exp,pos}) => 
         (case evExp(vector_exp,env,ab,premises) of
             vectorVal(vec) => 
               (case (coerceValIntoTerm(evExp(index_exp,env,ab,premises))) of
                   SOME(t) => (case  (AthTerm.getNumVal t) of 
                                 SOME(A.int_num(n,_),false) => 
                                      if n < 0 orelse n >= Array.length(vec) then
                                         evError("Vector subscript out of bounds",SOME(A.posOfExp(index_exp)))
                                      else Array.sub(vec,n)
                               | _ => evError("Wrong kind of value given as a vector subscript",SOME(A.posOfExp(index_exp))))
                 | _ =>  evError("Given term does not represent a valid vector subscript",SOME(A.posOfExp(index_exp))))
            | _ => evError("Wrong kind of value given as subscript to vector-sub",SOME(A.posOfExp(index_exp)))))
and 
    makeEvalExpFunction(env,ab,premises) = (fn (e,binding_map) => (case binding_map of 
                                                                      NONE => evExp(e,env,ab,premises)
                                                                    | SOME(map) => evExp(e,ref(augmentWithMap(!env,map)),ab,premises)))
and
   evalApp(proc_phrase,args,app_pos,env,ab,premises) = 
    let 
        val head_val = evPhrase(proc_phrase,env,ab,premises) 
        val pos = app_pos 
    in
       (case head_val of
          propConVal(con) => evalPropConApp(con,args,env,ab,pos)
        | funVal(f,name,_) =>
                            
                            (let fun doArgs([],_,res) = rev(res)
                                  | doArgs(a::more,i,res) = doArgs(more,i+1,evPhrase(a,env,ab,premises)::res)
                                val arg_vals = doArgs(args,2,[])
                                val _ = if !Options.stack_trace then 
                                           addFrame(frame({call_pos=pos,call_file="",
                                                           lambda=FunVal({name=name})}))
                                        else
                                           if !Options.detailed_stack_trace then 
                                              addFrame(detailedFrame({call_pos=pos,call_file="",
                                                                      lambda=FunVal({name=name}),
                                                                      arg_vals=arg_vals}))
                                           else ()
                            in
				 f(arg_vals,env,ab)
                            end handle PrimError(msg) => evError(msg,SOME(app_pos)))
        | closFunVal(A.functionExp({params,body,pos=fexp_pos,...}),clos_env,aux_clos_info) =>
                   let fun makeMessage(i,pos,required_arity,actual_arity,str) = 
                            fn () => evError("the "^(ordinal i)^" argument in this procedure call violated the\n"^
                                             "operator constraint of the corresponding parameter. The relevant OP \n"^
                                             "annotation ("^(A.posToString pos)^") "^
                                             "dictates an arity of "^required_arity^
                                              ".\nThe given "^str^" has an arity of "^actual_arity,
                                              SOME(app_pos))
                       fun f([],[],tab,arg_vals,_) = (tab,arg_vals)
                         | f(pwp::more_params,arg::more_args,tab,arg_vals,i) = 
	                         let val arg_val = evPhrase(arg,env,ab,premises)
				 in
 				   (case pwp of
				       A.someParam({name,pos as param_pos,sort_as_fterm as SOME(fsort),...}) =>
                                         ((case (coerceValIntoTerm arg_val) of 
                                               SOME(t) => let val term_sort = AT.getSort(t)
                                                          in
                                                             (case unifySorts(term_sort,fsort) of
                                                                 SOME(sort_sub) =>  
                                                                     let val t' = AT.applySortSub(sort_sub,t)
                                                                     in         
                                                                       f(more_params,more_args,Symbol.enter(tab,name,termVal t'),
                                                                         arg_val::arg_vals,i+1)
                                                                     end
                                                               | _ => evError("the "^(ordinal i)^" argument in this procedure call violated the\n"^
                                                                              "sort constraint of the corresponding parameter. The relevant sort \n"^
                                                                              "annotation ("^(A.posToString param_pos)^
                                                                               ") dictates a term of sort "^
                                                                              (F.toStringDefault(fsort)),SOME(app_pos)))
                                                          end))
  				     | A.someParam({name,sort_as_fterm as NONE,...}) =>
                	                   (f(more_params,more_args,Symbol.enter(tab,name,arg_val),arg_val::arg_vals,i+1))
				     | A.wildCard(_) => 
				  	   f(more_params,more_args,tab,arg_val::arg_vals,i+1))
				 end
                         | f(_,_,_,_,_) = evError("Wrong number of arguments ("^Int.toString(length(args))^ 
                                                 ") given\nto procedure "^(!(#name(aux_clos_info)))^"---exactly "^argNumToString(length(params))^
                                                 " required",SOME(pos))
                       val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val (new_vmap,arg_vals) = f(params,args,vmap,[],1)
                       val new_env = valEnv({val_map=new_vmap,mod_map=mmap})
                       val _ = addPos(!(#name(aux_clos_info)),app_pos)

                   in
                       evExp(body,ref(new_env),ab,premises)
                   end 
        | v =>  
             (case coerceValIntoTermCon(v) of
                 SOME(regFSym(some_fsym)) => 
                    (let 
                         val (name,arity) = (D.fsymName(some_fsym),D.fsymArity(some_fsym))
                          val arg_vals_and_positions = map 
                                                      (fn p => (evPhrase(p,env,ab,premises),A.posOfPhrase(p))) args
                          fun errorMsg(i,v) = wrongArgKind(MS.name(name),i,termLCType,v)
                          val term_args = getTermsWithCoercion(arg_vals_and_positions,errorMsg,coerceValIntoTerm)
                          val term_res = applyTermConstructor(name,arity,term_args,pos)
                      in
                         termVal(term_res)
                      end)
               | SOME(athNumFSym(anum)) => 
                      (if null(args) then termVal(AT.makeNumTerm(anum))
                        else evError(Int.toString(length(args))^" arguments given to nullary "^
                                    "symbol "^A.athNumberToString(anum)^"---it requires exactly zero arguments",
                                    SOME(pos)))
               | SOME(metaIdFSym(str)) => 
                 (if null(args) then termVal(AT.makeIdeConstant(str))
                  else evError(Int.toString(length(args))^" arguments given to nullary "^
                               "symbol "^A.printMetaId(str)^"---it requires exactly zero arguments",
                               SOME(pos)))
               | _ => (case v of
                          closUFunVal(_,_,_,{name,...}) => evError(wrongArgNumber(!name,length(args),1),SOME(app_pos))
                        | primUFunVal(_,{name,...}) => evError(wrongArgNumber(name,length(args),1),SOME(app_pos))
                        | closBFunVal(_,_,_,_,{name,...}) => evError(wrongArgNumber(!name,length(args),2),SOME(app_pos))
                        | primBFunVal(_,{name,...}) => evError(wrongArgNumber(name,length(args),2),SOME(app_pos))
                        | _ => let val msg = "The leftmost expression\nof an application failed to produce "^
                                             "a procedure\nor a symbol or a substitution. Instead,\n"
                                   val msg2 = "it produced this: "^(valLCTypeAndString(v))
                                   in evError(msg^msg2,SOME(A.posOfPhrase(proc_phrase)))
                               end)))
    end
and
   evalPropConApp(con,args as first::rest,env,ab,pos) = 
     if A.isQuantPropCon(con) then
      (case rest of
 	 _::_ =>
	      let val rev_args = rev(args)
        	  val prop_arg = hd(rev_args)
	          val pval = evPhrase(prop_arg,env,ab,PropSet.empty_prop_set)
	      in
	      (case coerceValIntoProp(pval) of
	         SOME(p) => (let val var_vals = map (fn a => evPhrase(a,env,ab,PropSet.empty_prop_set)) (rev(tl(rev_args)))
	                         val term_vars = getTermVars(var_vals,con,pos)
	                         val res_prop = makeQuantProp(SOME(con),term_vars,p)
						handle Basic.FailLst(msgs) => evError(Basic.failMsgsToStr(msgs),
										SOME(pos))
	                     in
	                        propVal(res_prop) 
	                     end)
	        | _ => evError(wrongArgKind(A.propConToString(con),length(rev_args),propLCType,pval),
			       SOME(A.posOfPhrase(prop_arg))))
	      end
       | _ => evError("Wrong number of arguments (1) given\nto "^A.propConToString(con)^"---at least "^
		      "two arguments are required",SOME(pos)))
     else
	(if con = A.andCon orelse con = A.orCon then
	  let val arg_vals = map (fn a => evPhrase(a,env,ab,PropSet.empty_prop_set)) args
	      val first_pos = A.posOfPhrase(first)
	      val (arg_vals1,arg_positions) = (case arg_vals of 
						[listVal(vl)] => (case vl of 
								    [_] => (vl,[first_pos])
   								  | _ => (vl,map (fn _ => first_pos) vl))
					      | _ => (arg_vals,map (A.posOfPhrase) args))
	      val con_val = propConVal(con)
	      val makeTheProp = (if con = A.andCon then P.makeConjunction else P.makeDisjunction)
	      val plst = coercePositionedValsIntoProps(arg_vals1,arg_positions,valLCTypeAndStringNoColon(con_val))
	  in
              (propVal(makeTheProp plst)) handle Basic.FailLst(msgs) => 
							evError(Basic.failMsgsToStr(msgs),SOME(pos))

	  end
	  else
	          let val arg_vals = map (fn a => evPhrase(a,env,ab,PropSet.empty_prop_set)) args
		      val arg_vals1 = (case arg_vals of [listVal(vl)] => vl | _ => arg_vals)
		      val con_val = propConVal(con)
		      val (v1,v2) = (case arg_vals1 of
					[v1,v2] => (v1,v2)
				      | _ => evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),
								    length(arg_vals1),2),SOME(pos)))
        	 in
	          (case (coerceValIntoProp(v1),coerceValIntoProp(v2)) of
        	      (SOME(p1),SOME(p2)) => 
	                  let val res_prop = makeBinaryProp(con,p1,p2) 
					 	handle Basic.FailLst(msgs) => 
							 evError(Basic.failMsgsToStr(msgs),SOME(pos))
	                      in
	                        propVal(res_prop)

	                  end
        	    | (SOME(_),NONE) =>  evError(wrongArgKind(valLCTypeAndStringNoColon(con_val),2,propLCType,v2),
                	                         SOME(pos))
	            | (_,_) => evError(wrongArgKind(valLCTypeAndStringNoColon(con_val),1,propLCType,v1),
        	                                 SOME(pos)))
		 end)
  | evalPropConApp(con as A.andCon,[],_,_,pos) =  
	evError("No arguments given to "^valLCTypeAndStringNoColon(propConVal(con))^"---at least one\n"^
		"argument is required",SOME(pos))
  | evalPropConApp(con as A.orCon,[],_,_,pos) =  
	evError("No arguments given to "^valLCTypeAndStringNoColon(propConVal(con))^"---at least one\n"^
		"argument is required",SOME(pos))
  | evalPropConApp(con,args,_,_,pos) = 
            evError(wrongArgNumber(valLCTypeAndStringNoColon(propConVal(con)),length(args),2),
                    SOME(pos))
and 
    evalClosure(v as closFunVal(A.functionExp({params,body,pos,...}),clos_env,{prec,assoc,...}),
               arg_vals,ab,pos_option) =
           let val param_num = length(params)
               val arg_num = length(arg_vals)
           in
               if not(arg_num = param_num) then
                  makeError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),pos_option)
               else 
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val new_env = ref(valEnv({val_map=enterParamValLst(vmap,params,arg_vals),mod_map=mmap}))
                       in
                         evExp(body,new_env,ab,PropSet.empty_prop_set)
                   end
           end
  | evalClosure(v as closBFunVal(body,param1,param2,clos_env,_),
               arg_vals,ab,pos_opt) =
           let val param_num = 2
               val arg_num = length(arg_vals)
           in
               if not(arg_num = param_num) then
                  makeError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),pos_opt)
               else
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val vmap' = Symbol.enter(vmap,param1,hd arg_vals)
                       val vmap'' = Symbol.enter(vmap',param2,hd (tl arg_vals))
                       val new_env = ref(valEnv({val_map=vmap'',mod_map=mmap}))
                       in
                         evExp(body,new_env,ab,PropSet.empty_prop_set)
                   end
           end
  | evalClosure(v as closUFunVal(body,param,clos_env,{name,...}),
               arg_vals,ab,pos_opt) =
           let val param_num = 1
               val arg_num = length(arg_vals)
               val cond = (arg_num = param_num)
           in
               if not(cond) then
                  makeError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),pos_opt)
               else
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val vmap' = Symbol.enter(vmap,param,hd arg_vals)
                       val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
                       in
                         evExp(body,new_env,ab,PropSet.empty_prop_set)
                   end
           end
  | evalClosure(_) = genError("Invalid call to evalClosure",NONE)
and
    evalMethodApp(method,args,env,ab,pos,premises) =
       let val app_pos = pos 
           fun getArgVals([],arg_vals,ded_vals,new_premises) = (rev(arg_vals),ded_vals,new_premises)
             | getArgVals(A.exp(e)::rest,arg_vals,ded_vals,new_premises) = 
                        getArgVals(rest,evExp(e,env,ab,premises)::arg_vals,ded_vals,new_premises)
             | getArgVals(A.ded(d)::rest,arg_vals,ded_vals,new_premises) = 
                       (case evDed(d,env,ab,new_premises) of
                           (dval as propVal(dprop),new_premises') => 
                              getArgVals(rest,propVal(dprop)::arg_vals,dprop::ded_vals,new_premises')
                         | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                        "argument of a method application---the deduction did not "^
                                        "produce a sentence!",SOME(A.posOfDed(d))))
           fun getArgValsAndPositions() = 
                let val pos_ar = Array.array(length(args)+2,A.dum_pos)
                    val _ = Array.update(pos_ar,0,app_pos)
                    val _ = Array.update(pos_ar,1,A.posOfExp(method))
                    fun doArgs([],arg_vals,ded_vals,i,new_premises) = (rev(arg_vals),ded_vals,pos_ar,new_premises)
                      | doArgs(A.exp(e)::rest,arg_vals,ded_vals,i,new_premises) = 
                          (Array.update(pos_ar,i,A.posOfExp(e));
                           doArgs(rest,evExp(e,env,ab,premises)::arg_vals,ded_vals,i+1,new_premises))
                      | doArgs(A.ded(d)::rest,arg_vals,ded_vals,i,new_premises) = 
                          (Array.update(pos_ar,i,A.posOfDed(d));
                           (case evDed(d,env,ab,new_premises) of
                               (propVal(dprop),new_premises') => 
                                 doArgs(rest,propVal(dprop)::arg_vals,dprop::ded_vals,i+1,new_premises')
                             | _ => evError("Impossibile error encountered in evaluating a deduction "^
                                             "argument of a method application---the deduction did not "^
                                             "produce a sentence",SOME(A.posOfDed(d)))))
                in
                   doArgs(args,[],[],2,premises)
                end
       in
          (case evExp(method,env,ab,premises) of 
               closMethodVal(A.methodExp({params,body,pos=mexp_pos,name=rname,...}),clos_env) =>
                       let val (arg_vals,ded_vals,premises') = getArgVals(args,[],[],premises)
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
			   val (res,premises'') = evDed(body,new_env,new_ab,premises')
			   val final_premises = PropSet.removeLst(ded_vals,premises'')
                           in
                              (res,final_premises)
                       end  
               | methodVal(f,method_name) => 
                    (let val (arg_vals,ded_vals,pos_array,new_premises) = getArgValsAndPositions()
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
                           val final_premises = (PropSet.insertValLst(getNeededPremises(arg_vals,method_name),new_premises))
			   val final_premises' = PropSet.removeLst(ded_vals,final_premises)
                      in 
                         (f(arg_vals,env,new_ab),final_premises')
                      end handle PrimError(msg) => evError(msg,SOME(app_pos)))
               | primUMethodVal(f,code) => 
                                      let val (arg_vals,ded_vals,pos_array,new_premises) = getArgValsAndPositions()
                                      in 
                                        if not(length(arg_vals)  = 1) then 
                                           evError(wrongArgNumber(S.name code,length(arg_vals),1),getPosOpt(pos_array,0))
                                        else ((f(hd(arg_vals),env,ab),PropSet.removeLst(ded_vals,new_premises)) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | primBMethodVal(f,code) => 
                                      let val (arg_vals,ded_vals,pos_array,new_premises) = getArgValsAndPositions()
				          val final_premises = PropSet.insertValLst(getNeededPremises(arg_vals,code),new_premises)
                                      in 
                                        if not(length(arg_vals)  = 2) then 
                                           evError(wrongArgNumber(S.name code,length(arg_vals),2),getPosOpt(pos_array,0))
                                        else ((f(hd(arg_vals),hd(tl(arg_vals)),env,ab),PropSet.removeLst(ded_vals,final_premises)) handle EvalError(str,_) => evError(str,SOME(pos)))
                                      end
               | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,pos_array,new_premises) = getArgValsAndPositions()
                           val _ =  if not(length(arg_vals)  = 2) then 
                                       evError(wrongArgNumber(!name,length(arg_vals),2),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s1,hd(arg_vals))
                           val vm' = Symbol.enter(vm,s2,hd(tl(arg_vals)))
                           val new_env = ref(valEnv({val_map=vm',mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
			   val (res,final_premises) = evDed(d,new_env,new_ab,new_premises)
                       in
                          (res,PropSet.removeLst(ded_vals,final_premises))
                       end  
               | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),name) =>
                       let val (arg_vals,ded_vals,pos_array,new_premises) = getArgValsAndPositions()
                           val _ =  if not(length(arg_vals)  = 1) then 
                                       evError(wrongArgNumber(!name,length(arg_vals),1),getPosOpt(pos_array,0))
                                    else ()
                           val vm = Symbol.enter(val_map,s,hd(arg_vals))
                           val new_env = ref(valEnv({val_map=vm,mod_map=mod_map}))
                           val new_ab = ABaseAugment(ab,ded_vals) 
			   val (res,final_premises) = evDed(d,new_env,new_ab,new_premises)
                       in
                          (res,PropSet.removeLst(ded_vals,final_premises))
                       end  
               | v => evError("The leftmost expression of a method application "^
                              "must produce a method---here it produced a "^valLCTypeAndString(v),
                              SOME(A.posOfExp(method))))
       end
and
  (** Note that evalMethodClosure needs no premise tracking. **)
    evalMethodClosure(v as closMethodVal(A.methodExp({params,body,pos,...}),clos_env),
                      arg_vals,ab,position,premises) =
           let val param_num = length(params)
               val arg_num = length(arg_vals)
           in
               if not(arg_num = param_num) then
                  evError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,param_num),SOME(position))
               else
                   let val (vmap,mmap) = getValAndModMaps(!clos_env)
                       val new_env = ref(valEnv({val_map=enterParamValLst(vmap,params,arg_vals),mod_map=mmap}))
                       in
                         evDed(body,new_env,ab,premises)
                   end
           end
  | evalMethodClosure(v as closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),_),arg_vals,ab,position,premises) = 
           let val arg_num = length(arg_vals)
           in
              if not(arg_num = 1) then
                 evError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,1),SOME(position))
              else let val vm = Symbol.enter(val_map,s,hd arg_vals)
                       val new_env = ref(valEnv({val_map=vm,mod_map=mod_map}))
                   in
                      evDed(d,new_env,ab,premises)
                   end
           end           
  | evalMethodClosure(v as closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),_),arg_vals,ab,position,premises) = 
           let val arg_num = length(arg_vals)
           in
              if not(arg_num = 2) then
                 evError(wrongArgNumber(valLCTypeAndStringNoColon(v),arg_num,2),SOME(position))
              else let val vm = Symbol.enter(val_map,s1,hd arg_vals)
                       val vm' = Symbol.enter(vm,s2,hd(tl(arg_vals)))
                       val new_env = ref(valEnv({val_map=vm',mod_map=mod_map}))
                   in
                      evDed(d,new_env,ab,premises)
                   end
           end           
  | evalMethodClosure(_) = genError("Invalid call to evalClosure",NONE)
and 
   evDed(method_app as A.BMethAppDed({method,arg1,arg2,pos}),env,ab,premises) =
      let val head_val = evExp(method,env,ab,premises) 
      in
        (case head_val of
           primBMethodVal(M,code) => 
                (let  
                     val v1 = evPhrase(arg1,env,ab,premises)
                     val v2 = evPhrase(arg2,env,ab,premises)
                     val (v1,ab',new_premises_1,is_ded_1) = 
		           (case arg1 of
                              A.ded(d) => let val (v,new_premises) = evDed(d,env,ab,premises)			                      
                                          in
                                            (v,putValIntoAB(v,ab),new_premises,true)
                                          end
                            | _ => let val v = evPhrase(arg1,env,ab,premises)
			               val new_premises = if primMethodSententialArgPos(code,1) then
                                                            (case coerceValIntoProp(v) of
                                                                SOME(p) => PropSet.insert(p,premises)
                                                              | _ => premises)
                                                          else premises 
				       val res = (v,ab,new_premises,false)
                                   in
                                      res
                                   end)
                     val (v2,ab'',new_premises_2,is_ded_2) = 
		           (case arg2 of
                              A.ded(d) => let val (v,new_premises) = evDed(d,env,ab',new_premises_1)
                                          in
                                            (v,putValIntoAB(v,ab'),new_premises,true)
                                          end
                            | _ => let val v = evPhrase(arg2,env,ab',new_premises_1)
 			               val new_premises  = if primMethodSententialArgPos(code,2) then
                                                             (case coerceValIntoProp(v) of
                                                                 SOME(p) => PropSet.insert(p,new_premises_1)
                                                               | _ => new_premises_1)
                                                           else new_premises_1
                                   in
                                      (v,ab',new_premises,false)
                                   end)
		    val res = M(v1,v2,env,ab'')
                 in
                    (res,new_premises_2) 
                 end handle PrimError(msg) => evError(msg,SOME(pos))

                          | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()

                                                in
                                                  evError(msg,SOME(right_pos))
                                                end)
         | closBMethodVal(d,s1,s2,clos_env as ref(valEnv({val_map,mod_map,...})),name) => 
 	          let val (v1,premises') =  (case arg1 of
                                                     A.exp(e) => (evExp(e,env,ab,premises),premises)
                                                   | A.ded(d) => evDed(d,env,ab,premises))
                      val (v2,premises'') =   (case arg2 of
                                                 A.exp(e) => (evExp(e,env,ab,premises'),premises')
                                               | A.ded(d) => evDed(d,env,ab,premises'))
                      val ab' = if A.isDeduction(arg1) then putValIntoAB(v1,ab) else ab
                      val ab'' = if A.isDeduction(arg2) then putValIntoAB(v2,ab') else ab'
                      val vm = Symbol.enter(Symbol.enter(val_map,s1,v1),s2,v2)
                      val _ = addPos(!name,pos)
		      val (res,final_premises) = evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab'',premises'')
		      val final_premises' = if A.isDeduction(arg1) then
                                                (if A.isDeduction(arg2) then PropSet.removeValLst([v1,v2],final_premises) else PropSet.removeVal(final_premises,v1))
                                            else 
					        (if A.isDeduction(arg2) then PropSet.removeVal(final_premises,v2) else final_premises)
                  in                          
                      (res,final_premises')                                      
                  end
        | _ =>  evalMethodApp(method,[arg1,arg2],env,ab,pos,premises))
      end
  | evDed(A.UMethAppDed({method,arg,pos}),env,ab,premises) = 
       let val head_val = evExp(method,env,ab,premises)
       in
         (case head_val of
              primUMethodVal(f,code) => (let val (arg_val,premises') = 
	                                         (case arg of
                                                     A.exp(e) => let val v = evExp(e,env,ab,premises)
  	 		                                             val new_premises = if primMethodSententialArgPos(code,1) then
								                           (case coerceValIntoProp(v) of
                                                                                            SOME(p) => PropSet.insert(p,premises)
                                                                                          | _ => premises)
                                                                                         else premises
                                                                 in
                                                                   (v,new_premises)
								 end
                                                   | A.ded(d) => evDed(d,env,ab,premises))
                                          val ab' = if A.isDeduction(arg) then putValIntoAB(arg_val,ab) else ab
					  val res = f(arg_val,env,ab')	  
					  val final_premises = if A.isDeduction(arg) then PropSet.removeVal(premises',arg_val) else premises'
                                      in
                                         (res,final_premises)
                                      end handle PrimError(msg) => evError(msg,SOME(pos))                                      

                                               | AthenaError(msg) => let val (_,right_pos) = chooseAthenaErrorPosition()

                                                                     in
                                                                        evError(msg,SOME(right_pos))
                                                                     end)

            | closUMethodVal(d,s,clos_env as ref(valEnv({val_map,mod_map,...})),clos_name) => 
                   let val (arg_val,premises') =  (case arg of
                                                     A.exp(e) => (evExp(e,env,ab,premises),premises)
                                                   | A.ded(d) => evDed(d,env,ab,premises))
                       val vm = Symbol.enter(val_map,s,arg_val)
		       val is_ded = A.isDeduction(arg)
                       val ab' = if is_ded then putValIntoAB(arg_val,ab) else ab
                       val _ = addPos(!clos_name,pos)
		       val (res,final_premises) = evDed(d,ref(valEnv({val_map=vm,mod_map=mod_map})),ab',premises')
		       val final_premises' = if is_ded then PropSet.removeVal(final_premises,arg_val) else final_premises
                   in
		       (res,final_premises')                                        
                   end
            | _ => evalMethodApp(method,[arg],env,ab,pos,premises))
       end
  | evDed(method_app as A.methodAppDed({method,args,pos=app_pos}),env,ab,premises) = evalMethodApp(method,args,env,ab,app_pos,premises)
  | evDed(A.assumeDed({assumption,body,pos}),env,ab,premises) = 
            let val aval = evPhrase(assumption,env,ab,premises)
            in
               (case coerceValIntoProp(aval) of
                   SOME(p1) => let val asms = Prop.decomposeConjunctions(p1)
                                   val ab' = ABase.augment(ab,asms)
				   val (body_val,premises') = evDed(body,env,ab',premises)
                               in 
                                 (case coerceValIntoProp(body_val) of 
                                    SOME(p2) => (propVal(P.makeConditional(p1,p2)),PropSet.removeLst(p1::asms,premises'))
                                  | _ => evError("Impossible error encountered in assume deduction: the body of "^
                                                  "the deduction did not produce a sentence",
			  		  SOME(A.posOfDed(body))))
                               end
                 | _ => evError("In a deduction of the form (assume F D), the value of F"^ 
                                " must\nbe a sentence, but here it was a "^valLCTypeAndString(aval),
                                SOME(A.posOfPhrase(assumption))))
            end
  | evDed(A.matchDed({discriminant,clauses,pos}),env,ab,premises) =
      let val (discrim_value,premises') = (case discriminant of
                                              A.exp(_) => (evPhrase(discriminant,env,ab,premises),premises)
                                            | A.ded(d) => evDed(d,env,ab,premises))
          val e_fun = makeEvalExpFunction (env,ab,premises')
          val (new_ab,d_prop_opt) =
                      if A.isDeduction(discriminant) then
                          (case coerceValIntoProp(discrim_value) of
                              opt as SOME(P) => (ABase.insert(P,ab),opt)
                            | _ => evError("Impossible error encountered in dmatch"^
                                      "---the discriminant is a deduction and yet it "^
                                      "did not produce a sentence",
                                      SOME(A.posOfPhrase(discriminant))))
                       else (ab,NONE)
          fun tryClauses([]:A.dmatch_clause list) =  
                  evError("dmatch failed---the "^valLCTypeAndStringNoColon(discrim_value)^
                          "\ndid not match any of the given patterns",SOME(pos))
            | tryClauses({pat,ded}::more) = 
               (case matchPat(discrim_value,pat,e_fun) of
                   SOME(map,_) => 
                      let val new_env = ref(augmentWithMap(!env,map))
		          val final_premises = (case d_prop_opt of
                                                   SOME(p) => PropSet.remove(premises',p)
                                                 | _ => premises')
                          val (res,final_premises) = evDed(ded,new_env,new_ab,final_premises) 						 
			  val final_premises' = (case d_prop_opt of
                                                   SOME(p) => PropSet.remove(final_premises,p)
                                                 | _ => final_premises)
                          in
                            (res,final_premises')
                          end
                 | _ => tryClauses(more))
          in
            tryClauses(clauses)
      end                         
  | evDed(A.letDed({bindings,body,pos}),env,ab,premises) = 
       let fun doLetDed([]:A.binding list,env1,ab1,premises,conclusions) = 
                  let val (v,premises') = evDed(body,env1,ab1,premises)
                  in
                     (v,PropSet.removeLst(conclusions,premises'))
                  end
             | doLetDed({bpat,def=A.ded(d),pos}::more,env1,ab1,premises,conclusions) = 
                  let val (dval,premises') = evDed(d,env1,ab1,premises)
		      val premises'' = PropSet.removeLst(conclusions,premises')
                  in
                     (case matchPat(dval,bpat,makeEvalExpFunction (env1,ab,premises'')) of 
                        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                         val (new_ab,new_conclusions) =
                  			         (case dval of
                                                      propVal(p) => (ABaseAugment(ab1,Prop.decomposeConjunctions p),p::conclusions)
                                                    | _ => (ab1,conclusions))
                                     in
                                       doLetDed(more,new_env,new_ab,premises'',new_conclusions)
                                     end 
                      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                                     (valLCTypeAndStringNoColon dval),
                                     SOME(A.posOfPat(bpat))))
                  end
             | doLetDed({bpat,def=A.exp(e),pos}::more,env1,ab1,premises,conclusions) = 
                  let val eval = evExp(e,env1,ab1,premises)
                  in
                     (case matchPat(eval,bpat,makeEvalExpFunction (env1,ab,premises)) of 
                        SOME(map,_) => let val (vmap,mod_map) = getValAndModMaps(!env1)
                                         val new_env = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mod_map}))
                                     in
                                       doLetDed(more,new_env,ab1,premises,conclusions)
                                     end 
                      | _ => evError("Dlet pattern failed to match the corresponding value, the\n "^
                                      (valLCTypeAndStringNoColon eval),
                                     SOME(A.posOfPat(bpat))))
                  end
           in
              doLetDed(bindings,env,ab,premises,[])
       end
  | evDed(A.assumeLetDed({bindings,body,pos}),env,ab,premises) = 
           let fun getProp(F,env,ab) = 
                  let val ((Fval,premises'),Fkind) = 
                                              (case F of
                                                 A.exp(_) => ((evPhrase(F,env,ab,premises),premises),"hypothesis")
                                              | A.ded(d) => (evDed(d,env,ab,premises),"bidy"))
                  in
                     (case coerceValIntoProp(Fval) of
                         SOME(P) => (P,premises')
                       | _ => evError("assume-let "^Fkind^" failed to result in a sentence. Instead, it "^ 
                                      "produced a "^valLCTypeAndString(Fval),SOME(A.posOfPhrase(F))))
                  end
               fun doBindings([]:A.binding list,assumptions,env1) = 
                     let val asms' = Basic.flatten(map Prop.decomposeConjunctions assumptions)
		         val (body_conclusion,premises') = getProp(A.ded(body),env1,ABaseAugment(ab,asms'))
                     in
                       (propVal(Prop.foldConditionals(rev(assumptions),body_conclusion)),premises')
                     end
                  | doBindings({bpat,def,...}::more,assumptions,env1) = 
                       let val (new_assumption,_) = getProp(def,env1,ab)
                       in
                          (case matchPat(propVal(new_assumption),bpat,makeEvalExpFunction (env1,ab,premises)) of 
                              SOME(map,_) => let val (vmap,mmap) = getValAndModMaps(!env1)
                                               val env1' = ref(valEnv({val_map=Symbol.augment(vmap,map),mod_map=mmap}))
                                           in
                                             doBindings(more,new_assumption::assumptions,env1')
                                           end
                            | _ => evError("Assume pattern failed to match the corresponding value, the\n "^
                                            (valLCTypeAndStringNoColon (propVal new_assumption)),
                                            SOME(A.posOfPat(bpat))))
                       end
           in
              doBindings(bindings,[],env)
           end
  | evDed(A.absurdDed({hyp,body,pos}),env,ab,premises) = doSupposeAbsurd(hyp,NONE,body,pos,env,ab,premises)
  | evDed(A.absurdLetDed({named_hyp,body,pos}),env,ab,premises) = 
          let val (hyp_name_pat,hyp) = (#bpat(named_hyp),#def(named_hyp))
              in
                doSupposeAbsurd(hyp,SOME(hyp_name_pat),body,pos,env,ab,premises)
          end
  | evDed(A.inductionDed({prop,clauses,pos}),env:value_environment ref,ab,premises) = 
      let 
          val (uvar,body,goal) = let val pval = evPhrase(prop,env,ab,premises)
                                 in
                                   (case (coerceValIntoProp(pval)) of
	    	  	   	     SOME(P) => (case P.isUGen(P) of 
                                                    SOME(v,body) => (v,body,P)
				    	           | _ => evError((prefix ())^(msg3 pval),
					  	    	           SOME(A.posOfPhrase(prop))))
                                    | _ => evError((prefix ())^(msg3 pval),SOME(A.posOfPhrase(prop))))
  			         end

          val uvar_sort = ATV.getSort(uvar)

          val _ = if StructureAnalysis.isStructureType(uvar_sort) then () else 
                  evError(msg1(2,ATV.toStringWithSort(uvar),P.toString(body,makeVarSortPrinter()),
			  F.toStringDefault(uvar_sort)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evExp(e',env',ab,premises)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,uvar_sort,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,uvar_sort) of
                      SOME(t) => evError(msg2(F.toStringDefault(uvar_sort),
                                              AT.toStringDefault(t)),SOME(pos))
                    | _ => ()) 
          fun property(t) = P.replace(uvar,t,body)
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),previous_clauses,ab,premises) = 
               let
                   fun emsg(req,gotten) = "One of the given cases of this inductive deduction failed "^
                                          "to establish the right conlusion.\nWanted: "^
                                           Util.decide(pprintProp(req),50)^
                                          "\nGotten: "^Util.decide(pprintProp(gotten),50)^"\n"

                   val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val new_iarm = {uvar=uvar,uvar_sort=uvar_sort,uprop=body,
                                   uv_pattern=pat_as_ath_term}
                   val _ = iarm_stack := LStack.push(new_iarm,!iarm_stack)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab,premises)
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                 else new_env_0
                   val real_current_goal = property(pat_as_ath_term)




                   fun getReflexiveFreshvars(vars,res) = 
                         (case vars of
                             [] => (rev res)
                           | fv::more => let val fresh_var_sort = ATV.getSort(fv)
                                         in
                                            (case F.isVarOpt(fresh_var_sort) of
                                                SOME(_) => getReflexiveFreshvars(more,res)
                                              | _ => (case F.unify(fresh_var_sort,F.rename(uvar_sort)) of
                                                         SOME(sub) => let val new = ATV.applySortSub(sub,fv)
                                                                      in
                                                                        getReflexiveFreshvars(more,new::res)
                                                                      end
                                                       | _ =>  getReflexiveFreshvars(more,res)))
                                         end)

                  val reflexive_fresh_vars = getReflexiveFreshvars(fresh_vars,[])


                   val reflexive_vars_as_terms = map AT.makeVar reflexive_fresh_vars
                   val current_ind_hyps = map property reflexive_vars_as_terms

                   fun sameRootSymbol(t1,t2) = 
                         (case (AT.isApp(t1),AT.isApp(t2)) of
                             (SOME(f,_),SOME(g,_)) => MS.modSymEq(f,g)
                           | _ => false)
                   val diff_facts:P.prop list = 
                          if not(!(Options.fundef_mlstyle_option)) orelse null(previous_clauses) then [] 
                          else (let val previous_pats_as_terms:AT.term list = map (fn (_,y,_,_,_) => y) previous_clauses
                                    val previous_pats_as_terms = List.filter (fn t => sameRootSymbol(t,pat_as_ath_term)) previous_pats_as_terms
                                    val previous_pat_string = Basic.printSExpListStr(previous_pats_as_terms,fn t => (valToString (termVal t)))
                                    val pstr = getSafeName("diff*")
                                    val str = "("^pstr^" "^(valToString (termVal pat_as_ath_term))^" ["^previous_pat_string^"])"

                                    val evalString = !evaluateString
                                    val lv = evalString(str)
                                in 
                                   case coerceValIntoProp(lv) of
                                       SOME(p) => let val res = Prop.decomposeConjunctions(p)
                                                  in
                                                    res
                                                  end
                                end) handle _ => [] 

                   val ind_hyps = (current_ind_hyps@
                                  (if (AT.height(pat_as_ath_term) = 0) then [] 
                                   else getInductiveHypotheses(!iarm_stack,fresh_vars,real_current_goal,pat_as_ath_term)))
				  handle Basic.FailLst(msgs) => evError("Error in generating inductive "^
									"hypotheses..."^Basic.failMsgsToStr(msgs),
									SOME(pos))

                   val new_ab = ABaseAugment(ab,diff_facts@ind_hyps)
                   val (res_prop,premises') = 
                                 (case evDed(ded,new_env,new_ab,premises) of
             	                            (propVal(P),premises') => (P,premises')
                                    | _ => raise Basic.Never)
                   val premises'' = PropSet.removeLst(ind_hyps,premises')				  
               in
                  (case provesTheRightInductiveCase(res_prop,uvar,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"inductive") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => (iarm_stack := LStack.pop(!iarm_stack);
                            let val conjunction = P.makeConjunction(ind_hyps)
                                val body = if null(ind_hyps) then res_prop else P.makeConditional(conjunction,res_prop)
                            in 
                              premises''
                            end))
               end
          fun doNewClauses([],_,_,premises) = (propVal(P.makeUGen([uvar],body)),premises)
            | doNewClauses(clause::more_clauses,previous_clauses,ab,premises) = 
                  let val premises' = doNewClause(clause,previous_clauses,ab,premises) 
                  in
                     doNewClauses(more_clauses,clause::previous_clauses,ab,premises')
                  end
      in
        doNewClauses(new_clauses,[],ab,premises)
      end
  | evDed(A.structureCasesDed({prop,clauses,pos,term}),env:value_environment ref,ab,premises) = 
    (case term of 
     SOME(dt_exp) =>  
      let fun prefix(n) = let val str = "first"
                          in
                             "Invalid argument given to the datatype-cases form.\n"^
                             "In every deduction of the form (datatype-cases E v D), the "^
                             "value of E must\nbe a sentence P and v must be (or denote) a variable"  
                          end
          fun msg1(n,var_str,P_str,obtype) = prefix(n)^". In addition, the\nsort of v in P must be a datatype."^ 
                                   " But here "^"v and P are "^var_str^" and\n"^P_str^
                                   "\nrespectively, where "^var_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a datatype"
          fun msg2(str1,str2) = "Ill-formed datatype-cases deduction---the given patterns do not exhaust\nthe "^
                                "datatype "^str1^". Here is a counter-example: "^str2
          fun msg3(n,v) = prefix(n)^".\nBut here E was a "^valLCTypeAndString(v)
          fun msg4(e) = "A variable was expected here"
          val dt_exp_pos = A.posOfExp(dt_exp)
          val var = (case evExp(dt_exp,env,ab,premises) of
                        termVal(t) => (case AT.isVarOpt(t) of
                                          SOME(v) => v
                                        | _ => evError(msg4(dt_exp),SOME(dt_exp_pos)))
                      | _ => evError(msg4(dt_exp),SOME(dt_exp_pos)))
          val var_term = AthTerm.makeVar(var)
          val body = let val pval = evPhrase(prop,env,ab,premises)
                            in
                              (case coerceValIntoProp(pval) of
                                  SOME(P) => P
                                 | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                            end 
          val var_type = ATV.getSort(var)
          val _ = if StructureAnalysis.isStructureType(var_type) then () else 
                  evError(msg1(2,Terms.printAthTermVar(var),prettyValToString(propVal(body)),Terms.printFTermSExp(var_type)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evExp(e',env',ab,premises)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,var_type,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,var_type) of
                      SOME(t) => evError(msg2(Terms.printFTermSExp(var_type),
                                              Terms.printAthTermSExp(t)),SOME(pos))
                    | _ => ())
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),ab,premises) = 
               let val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab,premises)		   
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
		                   let 
                                   in
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                   end
                                 else 
				    let
                                    in
                                      new_env_0
                                    end
                   val new_ab = ABaseAugment(ab,[Prop.makeEquality(var_term,pat_as_ath_term),Prop.makeEquality(pat_as_ath_term,var_term)])
                   val (res_prop,premises') = 
                                  (case evDed(ded,new_env,new_ab,premises) of
                                      (propVal(P),premises') => (P,premises'))
               in
                  (case provesTheRightInductiveCase(res_prop,var,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"structure-cases") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => (P.makeUGen(fresh_vars,res_prop),premises'))
               end
          fun doNewClauses([],_,premises) = (propVal(body),premises)
            | doNewClauses(clause::more_clauses,ab,premises) = 
                  let val (res,premises') = doNewClause(clause,ab,premises) 
                  in
                     doNewClauses(more_clauses,ABaseInsert(res,ab),premises')
                  end
      in
         doNewClauses(new_clauses,ab,premises)
      end
    | NONE =>   
      let fun prefix(n) = let val str = "first"
                          in
                             "Invalid "^str^" argument given to the structure-cases form. "^
                             "In every deduction\nof the form (structure-cases E D), the "^
                             "value of E must be a sentence P of the form (forall v Q)"  
                          end
          fun msg1(n,var_str,P_str,obtype) = prefix(n)^".\nIn addition, the sort of v in Q must be a structure."^ 
                                   " But here\n"^"v and P are "^var_str^" and "^P_str^
                                   ", respectively, where "^var_str^" in "^P_str^" ranges over "^obtype^
                                   "---and "^obtype^" is not a structure"
          fun msg2(str1,str2) = "Ill-formed structure-cases deduction---the given patterns do not exhaust\nthe "^
                                "structure "^str1^". Here is a counter-example: "^str2
          fun msg3(n,v) = prefix(n)^".\nBut here E was a "^valLCTypeAndString(v)
          val (uvar,body) = let val pval = evPhrase(prop,env,ab,premises)
                            in
                              (case coerceValIntoProp(pval) of
				  SOME(P) => (case P.isUGen(P) of 
		                                 SOME(uv,ub) => (uv,ub)
					       | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                                 | _ => evError(msg3(2,pval),SOME(A.posOfPhrase(prop))))
                            end 
          val uvar_sort = ATV.getSort(uvar)
          val _ = if StructureAnalysis.isStructureType(uvar_sort) then () else 
                  evError(msg1(2,ATV.toStringDefault(uvar),P.toString(body,makeVarSortPrinter()),
			  F.toStringDefault(uvar_sort)), 
                          SOME(A.posOfPhrase(prop)))
          fun makeNewClause(clause as {pat:A.pattern,ded:A.deduction}) = 
               let fun evSortExp(e) = 
                           let val mod_path = (case (!Paths.open_mod_paths) of
                                                  [] => []
                                                | mp::_ => mp)
                               val (e',_,fids) = SV.preProcessExp(e,mod_path)
			       val env' = makeEnv(fids,!env)
                           in
                              evExp(e',env',ab,premises)
                           end
                   val (pat_as_ath_term,pat_ids_paired_with_fresh_vars,is_named_pat) = makePatIntoAthenaTerm(pat,uvar_sort,evSortExp)
               in
                  (pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded,is_named_pat)
               end
          val new_clauses = map makeNewClause clauses
          val pats_as_ath_terms = map (fn (_,b,_,_,_) => b) new_clauses
          val _ = (case StructureAnalysis.exhaustStructure(pats_as_ath_terms,uvar_sort) of
                      SOME(t) => evError(msg2(F.toStringDefault(uvar_sort),
                                              AT.toStringDefault(t)),SOME(pos))
                    | _ => ())
          fun doNewClause((pat,pat_as_ath_term,pat_ids_paired_with_fresh_vars,ded:A.deduction,is_named_pat:bool),ab,premises) = 
               let val (pat_ids,fresh_vars) = ListPair.unzip(pat_ids_paired_with_fresh_vars)
                   val (vmap,mmap) = getValAndModMaps(!env)
                   val e_fun = makeEvalExpFunction (env,ab,premises)		   
                   val new_env_0 = ref(valEnv({val_map=enterLst(vmap,pat_ids,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
                   val new_env = if is_named_pat then
		                   let 
                                   in
                                    (case matchPat(termVal(pat_as_ath_term),pat,e_fun) of
                                        SOME(map,_) => ref(augmentWithMap(!new_env_0,map))
                                       | _ => new_env_0)
                                   end
                                 else 
				    let
                                    in
                                      new_env_0
                                    end
                   val new_ab = ab
                   val (res_prop,premises') = 
                               (case evDed(ded,new_env,new_ab,premises) of
                                      (propVal(P),premises') => (P,premises')
                                    | _ => raise Basic.Never)
               in
                  (case provesTheRightInductiveCase(res_prop,uvar,body,pat_as_ath_term,
                                                         pat_ids,fresh_vars,"structure-cases") of
                      SOME(msg) => evError(msg,SOME(A.posOfDed(ded)))
                    | _ => (P.makeUGen(fresh_vars,res_prop),premises'))
               end
          fun doNewClauses([],_,premises) = (propVal(P.makeUGen([uvar],body)),premises)
            | doNewClauses(clause::more_clauses,ab,premises) = 
                  let val (res,premises') = doNewClause(clause,ab,premises) 
                  in
                     doNewClauses(more_clauses,ABaseInsert(res,ab),premises')
                  end
      in
        doNewClauses(new_clauses,ab,premises)
      end)
  | evDed(A.byCasesDed({disj,from_exps,arms,pos}),env,ab,premises) = 
	let val (disj_val,premises) = (case disj of
                                           A.exp(_) => (evPhrase(disj,env,ab,premises),premises)
                                         | A.ded(d) => evDed(d,env,ab,premises))
	    val disj_prop = (case coerceValIntoProp(disj_val) of
           			SOME(P) => P
			      | _ => evError("A sentence (disjunction) was expected here. Instead, a\n"^
					     "value of type "^valLCTypeAndString(disj_val)^" was found.",
                	                      SOME(A.posOfPhrase(disj))))
	    val (disj_holds,premises) = 
                             if ABase.isMember(disj_prop,ab) orelse A.isDeduction(disj) then (true,premises)
			     else
				(case from_exps of 
				   NONE => evError("By-cases disjunction doesn't hold",
					           SOME(A.posOfPhrase(disj)))
			          | SOME(exps) => 
				 let fun er() = evError("Error in cases proof: unable to "^
					         "automatically derive the disjunction "^
						  prettyValToStringNoTypes(disj_val),SOME(pos))
				    val atp_call = A.methodAppDed({
							method=A.idExp({msym=msym N.vpfPrimMethod_symbol,no_mods=true,mods=[],sym=N.vpfPrimMethod_symbol,pos=pos}),
					    args=[disj,A.exp(A.listExp({members=(map A.exp exps),
							pos=A.dum_pos}))],pos=pos})
				     val (atp_val,premises') = evDed(atp_call,env,ab,premises) handle EvalError(str,_) => 
						 (print(str);raise Basic.Never)
				 in
				   (case coerceValIntoProp(atp_val) of
				       SOME(dp) => if P.alEq(dp,disj_prop) then (true,premises') else er()
				     | _ => er())
				 end)
	    val alts = P.getDisjuncts(disj_prop)
	    fun getAltProp(v,pos) = (case coerceValIntoProp(v) of 
				        SOME(P) => P
				      | _ => evError("A sentence was expected here. Instead, a\n"^
					             "value of type "^valLCTypeAndString(v)^" was found.",
                	                             SOME(pos)))
	    fun casesLeftUntreated(P) = evError("Non-exhaustive cases proof.\nThis case was not "^
				                "considered:\n"^P.toPrettyString(0,P,makeVarSortPrinter()),
					        SOME(pos))
	    fun gratuitousCase(P,pos) = evError("Gratuitous case considered in proof by cases:\n"^
						 P.toPrettyString(0,P,makeVarSortPrinter()),
						SOME(pos))
	    val {case_name,alt=first_case,proof=first_ded}:A.case_clause = hd arms
	    val (first_case_considered,conclusion,cases_left,premises) = 
		  let val first_prop = getAltProp(evExp(first_case,env,ab,premises),A.posOfExp(first_case)) 
                      val (vmap,mmap) = getValAndModMaps(!env)
   		      val env' = (case case_name of
			             SOME({name,...}) => ref(valEnv({val_map=Symbol.enter(vmap,name,propVal(first_prop)),mod_map=mmap}))
				   | _ => env)
                      val (first_ded_val,premises') = evDed(first_ded,env',ABaseInsert(first_prop,ab),premises)
		      val first_concl = (case coerceValIntoProp(first_ded_val) of
					   SOME(P) => P | _ => raise Basic.Never)
		      val (cases_left,is_mem) = Basic.removeAndCheckMemEq(first_prop,alts,P.alEq)
		  in
		     (first_prop,first_concl,cases_left,premises') 
		  end
	    fun checkConclusion(d,case_considered, new_env,premises) = 
              let val (conc,premises') = evDed(d,new_env,ABaseInsert(case_considered,ab),premises)
              in
		 (case coerceValIntoProp(conc) of
		     SOME(P) => if P.alEq(P,conclusion) then premises'
				else let val varSortPrinter = makeVarSortPrinter()
				     in
					evError("The sentence "^
					     P.toPrettyString(0,conclusion,varSortPrinter)^
					     " was expected here.\n"^
					     "Instead, the following sentence was produced: "^
					     P.toPrettyString(0,P,varSortPrinter),
					     SOME(A.posOfDed(d)))
				     end
		   | _ => raise Basic.Never)
	      end 
	    fun doArms([],cases_considered,cases_left,premises) = 
	                                    let val final_premises = if A.isDeduction(disj) then PropSet.remove(premises,disj_prop) else premises
					    in
                                               if Basic.subsetEq(cases_left,cases_considered,P.alEq)
					       then (propVal(conclusion),premises)
					       else casesLeftUntreated(hd cases_left)
                                            end
	      | doArms((cc:A.case_clause as {case_name,alt,proof})::rest,
			cases_considered,cases_left,premises) =
		  let val new_case_val = evExp(alt,env,ab,premises)
					 handle EvalError(str,_) => 
						 (print(str);raise Basic.Never)
					      |   ObTypeCheckFailure => 
						    (print("\nSort failure\n");raise Basic.Never)
                                              | _ => (print("\n Unknown error.\n"); raise Basic.Never)
		      val new_case = getAltProp(new_case_val,A.posOfExp(alt)) 
                      val (vmap,mmap) = getValAndModMaps(!env)
   		      val new_env = (case case_name of
			             SOME({name,...}) => ref(valEnv({val_map=Symbol.enter(vmap,name,propVal(new_case)),mod_map=mmap}))
				   | _ => env)
		      val (cases_left',is_mem) = Basic.removeAndCheckMemEq(new_case,cases_left,P.alEq)
		      val premises' = checkConclusion(proof,new_case,new_env,premises)
		  in
		      doArms(rest,new_case::cases_considered,cases_left',premises') 
		  end
	in
	   doArms(tl arms,[first_case_considered],cases_left,premises)
	end
  | evDed(A.checkDed({clauses,pos}),env,ab,premises) = 
       (case evalDCheckClauses(clauses,env,ab,premises) of
           SOME(d) => evDed(d,env,ab,premises)
         | _ => evError("dcheck failed: no alternative holds",SOME(pos)))

  | evDed(A.beginDed({members,pos}),env,ab,premises) = 
     let fun doAll([d],ab',premises,conclusions) = 
                let val (v,premises') = evDed(d,env,ab',premises)
                in
                   (v,PropSet.removeLst(conclusions,premises'))
                end
           | doAll(d1::(rest as (d2::more)),ab',premises,conclusions) = 
               (case evDed(d1,env,ab',premises) of
                   (propVal(p),premises') => doAll(rest,ABaseInsert(p,ab'),PropSet.removeLst(conclusions,premises'),p::conclusions)
                 | _ => evError("Impossible error---a component deduction of a dbegin "^
                                "failed to produce a sentence",SOME(A.posOfDed(d1))))
         in  
           doAll(members,ab,premises,[])
     end           
  | evDed(A.byDed({wanted_res,body,pos,conc_name}),env,ab,premises) =  
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
          val wv = evExp(wanted_res,env,ab,premises)
          val env' = (case conc_name of 
                         SOME({name,...}) => let val (vmap,mmap) = getValAndModMaps(!env)
                                             in
                                                ref(valEnv({val_map=Symbol.enter(vmap,name,wv),mod_map=mmap}))
                                              end
                       | _ => env)
      in
         (case coerceValIntoProp(wv) of 
             SOME(P) => (openTracing(P,level);
                         case (evDed(body,env',ab,premises) 
                               handle ex => (closeTracing(level,false);raise ex)) of
                            (res as propVal(Q),premises')
                                   => if Prop.alEq(P,Q)
					         then (closeTracing(level,true);(propVal(P),premises'))
                                                 else (closeTracing(level,false);
                                                       evError(msg(P,Q),SOME(pos))))
           | _ => evError(msg2(wv),SOME(A.posOfExp(wanted_res))))
      end
  | evDed(A.pickAnyDed({eigenvars,body,pos}),env,ab,premises) = 
        let val names = map #name eigenvars
	    fun makeFreshVar({name,pos,sort_as_sym_term=NONE,sort_as_fterm=NONE,...}:A.possibly_typed_param) = 
	    	ATV.freshWithPrefix(Symbol.name(name)^"_")
	      | makeFreshVar({name,pos,sort_as_sym_term=SOME(sym_term),sort_as_fterm=NONE,sort_as_exp=SOME(se),...}) = 
	      	   let val sort_string = AthStringToMLString(evExp(se,env,ab,premises))
                       fun isVar(str) = let val str_lst = explode str
		       	   	        in not(null(str_lst)) andalso 
					   hd(str_lst) = Names.sort_variable_prefix_as_char
					end
                   in
                       (case Terms.parseSymTerm(sort_string,isVar) of 
                           SOME(sort_as_sym_term) => let val fsort = Terms.carbonSymTermToFTerm(sort_as_sym_term)
                                                     in ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",fsort)
                                                     end)
                   end
              | makeFreshVar({name,pos,sort_as_sym_term,sort_as_fterm=SOME(sort),...}) = 
		  (let val res = ATV.freshWithSortAndPrefix(Symbol.name(name)^"_",sort)
		   in 
		      res
		   end)
	    val fresh_vars = map makeFreshVar eigenvars 
            val (vmap,mmap) = getValAndModMaps(!env)
            val new_env = ref(valEnv({val_map=enterLst(vmap,names,map (fn v => termVal(AT.makeVar(v))) fresh_vars),mod_map=mmap}))
            val (res,premises') = evDed(body,new_env,ab,premises)
        in        
               case res of
                  propVal(p) => let val P_safe = P.makeUGen(fresh_vars,p)
				    val P_preferable = SOME(P.renameQProp(List.map Symbol.name names,P_safe))
						       handle _ => NONE
			        in
				   (case P_preferable of
				       SOME(Q) => if P.alEq(P_safe,Q) then (propVal(Q),premises')
						  else (propVal(P_safe),premises')
				     | _ => (propVal(P_safe),premises'))
				end
        end
  | evDed(A.pickWitnessDed({ex_gen,var_id,inst_id,body=main_body,pos}),env,ab,premises) =
        let val (egv,premises) = (case ex_gen of
                                      A.exp(_) => (evPhrase(ex_gen,env,ab,premises),premises)
                                    | A.ded(d) => evDed(d,env,ab,premises))
	    fun showError() = evError("In a deduction of the form (pick-witness I F D), the value "^
		                      "of F must be an exisentially\nquantified sentence---but here "^
                                      "it was a "^valLCTypeAndString(egv),SOME(A.posOfPhrase(ex_gen)))
            val (ex_gen_val,ex_gen_var,ex_gen_body,new_ab) = 
                   (case coerceValIntoPropVal(egv) of 
                       SOME(v as propVal(egp)) => 
			 (case P.isEGen(egp) of 
			   SOME(ev,ebody) => 
			       (v,ev,ebody,(case ex_gen of 
   					     A.ded(_) => ABaseInsert(egp,ab)
                                           | _ => ab))
                           | _ => (case P.isEGenUnique(egp) of
				      SOME(ev,ebody) => 
					(v,ev,ebody,(case ex_gen of 
                                                       A.ded(_) => ABaseInsert(egp,ab)
                                                     | _ => ab))
                                    | _ => showError()))
                     | _ => showError())
            val ex_gen_var_sort = ATV.getSort(ex_gen_var)
            val unique_name = Symbol.symbol("!1")
            val fresh_var_v = AthTermVar.freshWithSortAndPrefix(Symbol.name(var_id)^"_",ex_gen_var_sort)
            val fresh_var = AT.makeVar(fresh_var_v)
            val (vmap,mmap) = getValAndModMaps(!env)
            val vmap' = enterLst(vmap,[unique_name,var_id],[ex_gen_val,termVal(fresh_var)])
            val new_env = ref(valEnv({val_map=vmap',mod_map=mmap}))
            val id_prop = P.replaceVarByVar(ex_gen_var,fresh_var_v,ex_gen_body)
            val new_env' = (case inst_id of
		               SOME(id) => ref(valEnv({val_map=enterLst(vmap',[id],[propVal(id_prop)]),mod_map=mmap}))
                             | _ => new_env)
            val new_ded = A.withWitnessDed({eigenvar_exp=A.idExp({msym=msym var_id,mods=[],no_mods=true,sym=var_id,pos=A.posOfPhrase(ex_gen)}),
                                            ex_gen=A.exp(A.idExp({msym=msym unique_name,mods=[],no_mods=true,sym=unique_name,pos=A.posOfPhrase(ex_gen)})),
                                            body=main_body,pos=pos})
            val (res,premises') = evDed(new_ded,new_env',new_ab,premises)        
        in
           if A.isDeduction(ex_gen) then (res,PropSet.removeVal(premises',ex_gen_val)) else (res,premises')
        end    
  | evDed(A.tryDed({choices,pos}),env,ab,premises) =
       let fun tryDeds([]) = NONE
             | tryDeds(d::more) = 
                   (case (SOME(evDed(d,env,ab,premises)) handle _ => NONE) of 
                       NONE => tryDeds(more)
                     | r =>  r)
           in
             (case tryDeds(choices) of
                NONE => evError("Try deduction error; all alternatives failed.\n",SOME(pos))
               | (SOME v) => v)
       end

  | evDed(d as A.pickWitnessesDed({ex_gen,var_ids,...}),env,ab,premises) = 
        let val (egv,premises) = (case ex_gen of
                                      A.exp(_) => (evPhrase(ex_gen,env,ab,premises),premises)
                                    | A.ded(d) => evDed(d,env,ab,premises))
	    fun showError() = evError("In a deduction of the form (pick-witnesses I1 ... In F D), "^
			 	      "the value of F must be an exisentially\nquantified "^
				      "sentence---but here it was a "^
                                      valLCTypeAndString(egv),SOME(A.posOfPhrase(ex_gen)))
            val (ex_gen_val,ex_gen_vars,ex_gen_body,new_ab) = 
                   (case coerceValIntoPropVal(egv) of 
                       SOME(v as propVal(egp)) =>
			 (case P.isEGen(egp) of 
			    SOME(ev,ebody) => 
	                         let val evars = getFrontQuantVars(egp)
				 in 
	                           (v,evars,ebody,(case ex_gen of 
        	                                     A.ded(_) => ABaseInsert(egp,ab)
                	                           | _ => ab))
				 end
		         | _ => (case P.isEGenUnique(egp) of
				    SOME(ev,ebody) => 
		                         let val evars = getFrontQuantVars(egp)
					 in 
		                           (v,evars,ebody,(case ex_gen of 
                	                             A.ded(_) => ABaseInsert(egp,ab)
                        	                   | _ => ab))
					 end
		                     | _ => showError()))
		    | _ => showError())
	  val (wit_count,evar_count) = (length(var_ids),length(ex_gen_vars))
          val _ = if wit_count >  evar_count then
		      evError("More witnesses ("^(Int.toString(wit_count))^") requested than\n"^
			      "could be obtained from the sentence:\n "^(prettyValToString(ex_gen_val))^
			      "\nThe above is existentially quantified over only "^(Int.toString(evar_count))^
			      (if evar_count = 1 then " variable" else " variables"),
			      SOME(A.posOfPhrase(ex_gen)))
		  else ()
           val (res,premises') = evDed(desugarPW(d,env,ab,evPhrase),env,new_ab,premises)
       in
           if A.isDeduction(ex_gen) then (res,PropSet.removeVal(premises',ex_gen_val)) else (res,premises')             	 
       end
  | evDed(A.genOverDed({eigenvar_exp,body,pos,...}),env,ab,premises) =  
      let fun msg(vstr) = "Failed universal generalization.\nThe eigenvariable "^vstr^
                          " occurs free in the current assumption base"
          fun emsg1(v) = "In a deduction of the form (generalize-over E D), the value of E must be "^
                         "a variable---but here it was a "^valLCTypeAndString(v)
          fun emsg2(v) = "In a deduction of the form (generalize-over E D), the value of E must be "^
                         "a variable---but here it was the non-variable term "^valToString(v)
          fun printVar(v) = Names.variable_prefix^(ATV.toStringDefault(v))
          val ev = evExp(eigenvar_exp,env,ab,premises)
      in
         case coerceValIntoTermVal(ev) of 
            SOME(termVal(t)) => 
                 (case AT.isVarOpt(t) of
                     SOME(v) => 
                         if Ab.occursFreeUpToSubsorting(v,ab) then
                            evError(msg(printVar(v)),SOME(A.posOfExp(eigenvar_exp)))
                         else 
                            let val (res,premises') = evDed(body,env,ab,premises)
                                val res_prop = (case coerceValIntoPropVal(res) of 
                                                   SOME(propVal(P)) => let val res = propVal(P.makeUGen([v],P))
 						                                       handle Basic.FailLst(msgs) => 
                                                                                              evError(Basic.failMsgsToStr(msgs),
                                                                                                      SOME(pos))
                                                                       in 
                                                                          res
                                                                       end                                     
                                                 | _ => evError("Impossible error encountered in universal "^
                                                                "generalization---the body of the deduction "^
                                                                "failed to produce a sentence",
                                                                SOME(A.posOfDed(body))))
                            in
                               (res_prop,premises')
                            end
                   | _ => evError(emsg2(ev),SOME(A.posOfExp(eigenvar_exp))))
           | _ => evError(emsg1(ev),SOME(A.posOfExp(eigenvar_exp)))
      end 
  | evDed(A.withWitnessDed({eigenvar_exp,ex_gen,body,pos}),env,ab,premises) = 
     let fun msg(vstr) = "Failed existential instantiation---the witness variable "^
                         "\noccurs free in the current assumption base"
         fun emsg1(v) = "In a deduction of the form (with-witness E F D), the value of E must "^
                        "be a variable---but here it was a "^valLCTypeAndString(v)
         fun emsg2(v) = "In a deduction of the form (with-witness E F D), the value of E must "^
                        "be a variable---but here it was the non-variable term "^valToString(v)
         val ev = evExp(eigenvar_exp,env,ab,premises)
     in
       case coerceValIntoTerm(ev) of
        SOME(t) => 
         (case AT.isVarOpt(t) of
            SOME(fresh_var) => 
              if Ab.occursFree(fresh_var,ab) then
                 evError(msg(AthTermVar.name(fresh_var)),SOME(A.posOfExp(eigenvar_exp)))
              else 
               let val (egenv,premises) = (case ex_gen of
                                              A.exp(_) => (evPhrase(ex_gen,env,ab,premises),premises)
                                            | A.ded(d) => evDed(d,env,ab,premises))
               in
                (case coerceValIntoProp(egenv) of  
                    SOME(specP) => 
		     (case P.isEGen(specP) of 
	               SOME(v,pbody) =>
                         if A.isDeduction(ex_gen) orelse ABase.isMember(specP,ab) then
                            let val pbody' = P.replace(v,AT.makeVar(fresh_var),pbody)
                                val pbody_components = Prop.decomposeConjunctions(pbody')
                                val new_ab = ABaseAugment(ab,pbody_components)
                                val (final_res,premises') = evDed(body,env,new_ab,premises)
				val final_premises = PropSet.remove(PropSet.removeLst(pbody_components,premises'),pbody')
				val final_premises' = if A.isDeduction(ex_gen) then PropSet.removeVal(final_premises,egenv) else final_premises
                            in
                                (case final_res of 
                                   v as propVal(p') => 
                                     if P.occursFree(fresh_var,p') then 
                                         evError("Failed existential instantiation---the witness variable "^
                                                  "\noccurs free in the resulting sentence",SOME(pos))
                                     else (v,final_premises')
                                 | _ => evError("Impossible error encountered in existential instantiation"^
                                                "the deduction body did not produce a sentence",
                                                SOME(A.posOfDed(body))))
                            end
                         else
			   let val specP_str = P.toPrettyString(0,specP,makeVarSortPrinter())
			   in
                             evError("Existential sentence to be instantiated is not in\nthe assumption base: "^
                                     (Util.decide(specP_str,16)),SOME(A.posOfPhrase(ex_gen)))
			   end
                       | _ => 
                        (case P.isEGenUnique(specP) of 
		         SOME(v,pbody) =>
                         if A.isDeduction(ex_gen) orelse ABase.isMember(specP,ab) then
                            let val fresh_term = AT.makeVar(fresh_var)
                                val instantiated_ex_prop = P.replace(v,fresh_term,pbody)
                                val new_var = ATV.freshWithSort(ATV.getSort(fresh_var))
                                val new_term = AT.makeVar(new_var)
                                val new_prop = P.replace(v,new_term,pbody)
                                val eq_prop1 = P.makeEquality(new_term,fresh_term)
                                val eq_prop2 = P.makeEquality(fresh_term,new_term)
                                val uniqueness_prop1 = P.makeUGen([new_var],P.makeConditional(new_prop,eq_prop1))
                                val uniqueness_prop2 = P.makeUGen([new_var],P.makeConditional(new_prop,eq_prop2))
                                val new_ab = ABaseAugment(ab,[uniqueness_prop1,uniqueness_prop2])
                                val (final_res,premises') = evDed(body,env,new_ab,premises)
                            in        
                                  (case final_res of 
                                      v as propVal(p') => 
                                        if P.occursFree(fresh_var,p') then
                                           evError("Failed existential instantiation---the witness variable "^
                                                  "\noccurs free in the resulting "^
                                                  "sentence",SOME(pos))
                                        else if A.isDeduction(ex_gen) then (v,PropSet.removeVal(premises',egenv)) else (v,premises')
                                    | _ => evError("Impossible error encountered in existential instantiation"^
                                                   "---the deduction body did not produce a sentence",
                                                   SOME(A.posOfDed(body))))
                            end
                         else
                             evError("Existential sentence to be instantiated is not in the assumption base: "^
                                      P.toPrettyString(0,specP,makeVarSortPrinter()),
						       SOME(A.posOfPhrase(ex_gen)))))
                  | _ => evError("In a deduction of the form (with-witness E F D) or (pick-witness E F D), the "^
                                 "value of F must be an existentially quantified\nsentence---but here"^
                                 " it was a "^valLCTypeAndString(egenv),SOME(A.posOfPhrase(ex_gen))))
               end
          | _ => evError(emsg2(ev),SOME(A.posOfExp(eigenvar_exp))))
      | _ => evError(emsg1(ev),SOME(A.posOfExp(eigenvar_exp)))
     end
  | evDed(A.letRecDed({bindings,body,pos}),env,ab,premises) = 
       let val rec_env = ref(!env)
           fun getVals([],map) = map 
             | getVals((b:A.binding as {bpat,def,pos})::more,map) = 
                let val mv = evPhrase(def,rec_env,ab,premises)
                in
                  (case matchPat(mv,bpat,makeEvalExpFunction (rec_env,ab,premises)) of 
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
              evDed(body,ref(new_env),ab,premises)
       end
  | evDed(A.fromDed({conclusion,premises,pos}),env,ab,premises') = 
       let 
           fun getProps(val_lst,list_name,pos,env) = 
                 let fun msg(v,i) = "Wrong kind of value found in the "^ordinal(i)^
				     " position of "^list_name^"---"^expectInOneLine(propLCType,v)
                     fun getProps([],results,i) = rev results
                       | getProps(v::rest,results,i) = 
                           (case coerceValIntoProp(v) of 
                              SOME(P) => getProps(rest,P::results,i+1)
                       | _ => evError(msg(v,i),SOME(pos)))
                  in
                     getProps(val_lst,[],1)
                  end
       in
         (case coerceValIntoProp(evExp(conclusion,env,ab,premises')) of 
             SOME(P) => (case evExp(premises,env,ab,premises') of
                          listVal(pvals) => 
                            let val premise_props = getProps(pvals,"the list argument of "
                                                                  ^" FROM deduction ",
							     A.posOfExp(premises),env)
                            in 
			       (true_prop_val,PropSet.insertLst(premise_props,premises'))
                            end)
            | _ => raise Basic.Never)
       end
  | evDed(A.infixAssumeDed({bindings,body,pos}),env,ab,premises) = 
	let 
            fun getPropsAndEnv([],props,env) = (props,env)
	      | getPropsAndEnv((b:A.binding as {bpat,pos,def,...})::rest,props,env) = 
	                let val pval = evPhrase(def,env,ab,premises)
			in
			  (case coerceValIntoProp(pval) of
	                      SOME(p) => 
                                 (case matchPat(pval,bpat,makeEvalExpFunction (env,ab,premises)) of 
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
	    val (res_val,premises') = evDed(body,new_env,ABase.augment(ab,hyps'),premises)
            in
	      (case coerceValIntoProp(res_val) of
	         SOME(q) => let val conj = (case hyps of
					      [P] => P
					    |  _  => Prop.makeConjunction(hyps))
                                val final_premises  = PropSet.removeLst(conj::(hyps@hyps'),premises')					    
			    in
			       (propVal(Prop.makeConditional(conj,q)),final_premises)
			    end
               | _ => evError("Impossible error encountered in assume deduction: the body of "^
                              "the deduction did not produce a sentence",SOME(A.posOfDed(body))))
	   end
and
   doSupposeAbsurd(hyp,hyp_name_pat,body,pos,env,ab,premises) = 
    let val hypv = evPhrase(hyp,env,ab,premises)
    in
      (case coerceValIntoPropVal(hypv) of
          SOME(pval as propVal(p)) => 
              let val new_env = 
                       (case hyp_name_pat of
                           SOME(bpat) => (case matchPat(pval,bpat,makeEvalExpFunction (env,ab,premises)) of 
                                             SOME(map,_) => ref(augmentWithMap(!env,map))
                                           | _ => evError("Suppose-absurd pattern failed to match "^ 
                                                          "the corresponding value, the\n"^
                                                          (valLCTypeAndStringNoColon pval),
                                                          SOME(A.posOfPat(bpat))))
                          | _ => env)
                  val (body_res,premises') = evDed(body,new_env,ABaseAugment(ab,[p]),premises)
		  val final_premises = PropSet.remove(premises',p)
                  in
                     (case coerceValIntoProp(body_res) of
                         SOME(p') => if Prop.isBooleanFalse(p') then
                                           (propVal(Prop.makeNegation(p)),final_premises)
                                        else
                                           evError("The body of a suppose-absurd deduction"
                                                  ^" must derive the sentence false---but here the "^
                                                  "result was the sentence\n"^pprintProp(p'),
                                                  SOME(A.posOfDed(body))))
              end
        | _ => evError("The hypothesis of a suppose-absurd deduction must be a sentence---"^
                       "but here it is a "^valLCTypeAndString(hypv),SOME(A.posOfPhrase(hyp))))
    end
and evPhrase(A.exp(e),env:value_environment ref,ab,premises) = evExp(e,env,ab,premises)
  | evPhrase(A.ded(d),env:value_environment ref,ab,premises) = let val (ded_val,premises') = evDed(d,env,ab,premises) in ded_val end 
and
coercePositionlessValsIntoProps(vals,meth_name) = 
     let fun f([],res,_) = res
           | f(v::more,res,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,P::res,i+1)
                     | _ => primError(wrongArgKind(meth_name,i,propLCType,v)))
     in
        f(vals,[],1)
     end                                            
and 
coercePositionedValsIntoPropsAndPositionCopies(vals,pos,meth_name) = 
     let fun f([],res,_) = res
           | f(v::more,res,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,(P,pos)::res,i-1)
                     | _ => evError("Wrong kind of value given as argument to "^meth_name^"---"^(expect(propLCType,v)),SOME pos))
     in
        f(vals,[],length vals)
     end                                            
and 
coercePositionedValsIntoProps(vals,pos_list,name) = 
     let fun f([],res,_,_) = rev(res)
           | f(v::more,res,pos::rest,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,P::res,rest,i+1)
                     | _ => evError(wrongArgKind(name,i,propLCType,v),SOME(pos)))
     in
        f(vals,[],pos_list,1)
     end                                            
and
coerceSolePositionedValsIntoProps(vals,pos,name) = 
     let fun f([],res,_) = rev(res)
           | f(v::more,res,i) = 
                   (case coerceValIntoProp(v) of  
                       SOME(P) => f(more,P::res,i+1)
                     | _ => evError(wrongArgKind(name,i,propLCType,v),SOME(pos)))
     in
        f(vals,[],1)
     end                                            
and evalCheckClauses(clauses,env,ab,premises) = 
     let fun f([]) = NONE
           | f({test=A.boolCond(phr),result}::more) =
                  (case evPhrase(phr,env,ab,premises) of 
                                 propVal(P) => (case P.isAtom(P) of
	 			                   SOME(t) => if isTrueTerm(t) then SOME(result) else f(more)
            				         | _ => f(more))
                                 | termVal(t) => if isTrueTerm(t) then SOME(result) else f(more)
	      		         | _ => f(more))
           | f({test=A.elseCond,result}::more) = SOME(result)
     in
        f(clauses)
     end
and evalDCheckClauses(clauses,env,ab,premises) = 
     let fun f([]) = NONE
           | f({test=A.boolCond(phr),result}::more) =
                  (case evPhrase(phr,env,ab,premises) of 
                                 propVal(P) =>
				   (case P.isAtom(P) of
				       SOME(t) => if isTrueTerm(t) then SOME(result) else f(more)
				     | _ => f(more))
                                 | termVal(t) => if isTrueTerm(t) then SOME(result)
	 					 else f(more)
	      		         | _ => f(more))
           | f({test=A.elseCond,result}::more) = SOME(result)
     in
        f(clauses)
     end
     
in
   (fn (e,env,ab) => (
                      let val res = evExp(e,env,ab,PropSet.empty_prop_set)
                      in
                        res
                      end),
    fn (d,env,ab) => evDed(d,env,ab,PropSet.empty_prop_set),
    fn (p,env,ab) => (let val res = evPhrase(p,env,ab,PropSet.empty_prop_set)
                    in
                       res
                    end),
    fn x => (evalClosure(x)),
    fn x => (evalMethodClosure(x)),
    fn x => coercePositionlessValsIntoProps(x),
    fn x => coercePositionedValsIntoProps(x),
    fn x => coercePositionedValsIntoPropsAndPositionCopies(x))
end

fun getProps(val_lst,list_name,env) = 
  let fun msg(v,i) = "Wrong kind of value found in the "^ordinal(i)^" position\nof "^list_name^
                     "---"^expectInOneLine(propLCType,v)
      fun getProps([],results,i) = rev results
        | getProps(v::rest,results,i) = 
            (case coerceValIntoProp(v) of 
                SOME(P) => getProps(rest,P::results,i+1)
              | _ => primError(msg(v,i)))
  in 
    getProps(val_lst,[],1)
  end


fun getAProps(val_lst,list_name,env) = 
  let fun msg(v,i) = "Wrong kind of value found in the "^ordinal(i)^" argument position\nof "^list_name^
                     "---"^expectInOneLine(propLCType,v)
      fun getProps([],results,i) = rev results
        | getProps(v::rest,results,i) = 
            (case coerceValIntoProp(v) of 
                SOME(P) => getProps(rest,P::results,i+1)
              | _ => primError(msg(v,i)))
  in 
    getProps(val_lst,[],1)
  end

fun getPropArgMessage(v,i,name) = 
   ("Wrong kind of value found in the "^ordinal(i)^" argument position\nof "^name^"---"^expectInOneLine(propLCType,v))

fun getTwoProps(v1,v2,list_name,env) = 
  let fun msg(v,i) = getPropArgMessage(v,i,list_name)
  in 
    (case coerceValIntoProp(v1) of 
        SOME(P1) => (case coerceValIntoProp(v2) of 
                        SOME(P2) => [P1,P2]
                      | _ => primError(msg(v2,2)))
      | _ => primError(msg(v1,1)))
  end

fun getPropsOrListProps(val_lst,list_name,env) = 
  let fun msg(v,i) = "Wrong kind of value found in the "^ordinal(i)^" position of "^list_name^
                     "---"^("a "^propLCType^" or a "^(listLCType^" of "^propLCType^"s")^
		     " was expected, but the given value was a "^(valLCTypeAndString v))
      fun gp([],results,i) = rev results
        | gp(listVal(vals)::rest,results,i) = let val res = getProps(vals,"the "^ordinal(i)^" position of "^
								    list_name,env)
					      in
						 gp(rest,res@results,i+1)
					      end
						       
        | gp(v::rest,results,i) = 
            (case coerceValIntoProp(v) of 
                SOME(P) => gp(rest,P::results,i+1)
              | _ => primError(msg(v,i)))
  in 
    gp(val_lst,[],1)
  end

fun getTerms(val_lst,list_name,pos) = 
  let fun msg(v,i) = "Wrong type of value found in the "^ordinal(i)^" argument position of "^list_name^
                     ".\n"^expectUC(termLCType,v)
      fun getTerms([],results,i) = rev results
        | getTerms(v::rest,results,i) = 
            (case coerceValIntoTerm(v) of
                SOME(t) => getTerms(rest,t::results,i+1)
              | _ => evError(msg(v,i),SOME(pos)))
  in 
    getTerms(val_lst,[],1)
  end

fun getTermsNoPos(val_lst,list_name,NONE) = 
  let fun msg(v,i) = "Wrong type of value found in the "^ordinal(i)^" argument position of "^list_name^
                     ".\n"^expectUC(termLCType,v)
      fun getTerms([],results,i) = rev results
        | getTerms(v::rest,results,i) = 
            (case coerceValIntoTerm(v) of
                SOME(t) => getTerms(rest,t::results,i+1)
              | _ => primError(msg(v,i)))
  in 
    getTerms(val_lst,[],1)
  end
| getTermsNoPos(val_lst,list_name,SOME(expected_arg_sorts,result_sort,is_poly)) = 
(** The last option argument is of the form SOME(...) iff the relevant functor to be applied to these terms that are being collected
    is a function symbol that expects at least one argument of sort (Fun ...). 
**)
  let fun msg(v,i) = "Wrong type of value found in the "^ordinal(i)^" argument position of "^list_name^
                     ".\n"^expectUC(termLCType,v)
      fun getTerms([],results,i,_) = rev results
        | getTerms(v::rest,results,i,expected_arg_sort::more_expected_arg_sorts) = 
           (case coerceValIntoTerm(v) of
               SOME(t) => let val resulting_term = 
                                        (case AT.isConstant(t) of 
          			            SOME(name) =>  if FTerm.termEq(result_sort,AT.getSort(t)) then 
						              AT.makeSortedConstantAux(name,result_sort,is_poly)
                                                           else t
                                           | _ => t)
                          in
			    getTerms(rest,resulting_term::results,i+1,more_expected_arg_sorts)
                          end
             | _ => (case D.funSortArity(expected_arg_sort) of 
                        SOME(K) => let val resulting_term = liftArg(v,K,NONE)
                                   in
				     getTerms(rest,resulting_term::results,i+1,more_expected_arg_sorts)
                                   end 
                      | _ =>  primError(msg(v,i))))
  in 
    getTerms(val_lst,[],1,expected_arg_sorts)
  end

(* It's important that the above coercion function take term *values* as inputs
and not just terms. A term value is guaranteed to be well-typed, whereas an arbitrary
term might not be. *)

fun isMetaId(v) = 
      (case coerceValIntoTerm(v) of 
          SOME(term) => 
               (case AthTerm.isIdeConstant(term) of 
                  NONE => false | _ => true)
        | _ => false)

fun isMetaIdConstructive(v) = 
      (case coerceValIntoTerm(v) of 
          SOME(term) => AthTerm.isIdeConstant(term)
        | _ => NONE)
 
end (* of structure Semantics *) 



