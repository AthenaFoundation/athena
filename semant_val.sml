(*======================================================================

The definition of Athena's semantic values and associated code. This file
also contains the AST preprocessor used before evaluation. 

=======================================================================*)

structure SemanticValues = 
struct 

structure S = Symbol

structure A = AbstractSyntax

structure Ab = ABase

structure B = Basic

structure N = Names

structure F = FTerm

structure Ab = ABase

structure Pos = Position

structure P = Prop

structure D = Data

structure ATV = AthTermVar

structure AT = AthTerm

structure MS = ModSymbol

type pos = A.pos

datatype fun_sym = regFSym of Data.ath_fun_sym
                 | athNumFSym of A.ath_number 
                 | metaIdFSym of string

fun hashFunSym(regFSym(f)) = Data.hashAthFunSym(f)
  | hashFunSym(athNumFSym(n)) = A.hashANum(n)
  | hashFunSym(metaIdFSym(str)) = Basic.hashString(str)

fun funSymPrec(regFSym(Data.declared({prec,...}))) = prec
  | funSymPrec(regFSym(Data.defined({prec,...}))) = prec
  | funSymPrec(_) = ref(0)

fun funSymName(regFSym(f)) = MS.name(Data.fsymName(f))
  | funSymName(athNumFSym(n)) = A.athNumberToString(n)
  | funSymName(metaIdFSym(str)) = str

fun funSymAssoc(regFSym(Data.declared({assoc,...}))) = assoc
  | funSymAssoc(_) = ref(NONE)

fun funSymEq(regFSym(sym1),regFSym(sym2)) = MS.modSymEq(Data.fsymName(sym1),Data.fsymName(sym2)) andalso 
                                                       (Data.fsymArity(sym1) = Data.fsymArity(sym2))

  | funSymEq(metaIdFSym(str1),metaIdFSym(str2)) = (str1 = str2)
  | funSymEq(athNumFSym(anum1),athNumFSym(anum2)) = A.athNumEquality(anum1,anum2)
  | funSymEq(_,_) = false 

type method_code = Symbol.symbol

datatype value = termVal of AT.term | 
                 charVal of int | 
                 termConVal of fun_sym | 
                 propConVal of A.prop_con |
                 propVal of Prop.prop | 
                 cellVal of value ref | 
                 listVal of value list | 
                 vectorVal of value array | 
                 primUFunVal of ((value * value_environment ref * Ab.assum_base) -> value) * {prec:int ref,name:string} | 
                 primBFunVal of ((value * value * value_environment ref * Ab.assum_base) -> value) * {prec:int ref,assoc:bool option ref,name:string} | 
                 funVal of prim_fun_type * string * {arity:int,prec:int ref, assoc: bool option ref} | 
                 nprimUFunVal of ((value  * Ab.assum_base) -> value) * {prec:int ref,name:string} | 
                 nprimBFunVal of ((value * value * Ab.assum_base) -> value) * {prec:int ref,assoc:bool option ref,name:string} | 
                 nfunVal of nprim_fun_type * string * {arity:int,prec:int ref, assoc: bool option ref} | 
                 closFunVal of A.expression * value_environment ref * {prec:int ref, assoc:bool option ref,name:string ref} |
                 closUFunVal of A.expression * S.symbol * value_environment ref * {name:string ref,prec:int ref} | 
                 closBFunVal of A.expression * S.symbol * S.symbol * value_environment ref * {name:string ref,prec:int ref, assoc:bool option ref} | 
                 primUMethodVal of ((value  * value_environment ref * Ab.assum_base) -> value) * method_code | 
                 primBMethodVal of ((value * value * value_environment ref * Ab.assum_base) -> value) * method_code | 
                 methodVal of ((value list * value_environment ref * Ab.assum_base) -> value) * method_code | 
                 closMethodVal of A.expression * value_environment ref |
                 closUMethodVal of A.deduction * S.symbol * value_environment ref * string ref | 
                 closBMethodVal of A.deduction * S.symbol * S.symbol * value_environment ref * string ref | 
                 subVal of AT.sub |
                 mapVal of (value,value) Maps.mapping | 
                 tableVal of val_hash_table | 
                 unitVal

and

value_environment =  valEnv of {val_map:value Symbol.mapping,mod_map:module Symbol.mapping}

withtype module = {mod_name:ModSymbol.mod_symbol, env: value_environment, open_mod_directives: S.symbol list list}

and prim_fun_type = value list * value_environment ref * Ab.assum_base -> value

and nprim_fun_type = value list * Ab.assum_base -> value

and val_hash_table = (value,value) HashTable.hash_table

fun recurse f (listVal vals) = listVal(List.map (recurse f) vals)
  | recurse f (vectorVal V) = let val L = Basic.arrayToList(V)
                              in
			         vectorVal(Array.fromList (List.map (recurse f) L))
			      end
  | recurse f (cellVal(ref(v))) = cellVal(ref((recurse f) v))
  | recurse f v = f v

fun default_fv_pa(a) = {arity=a,prec=ref(Options.defaultPrec(a)),assoc=ref(NONE:bool option)}

fun default_ufv_pa(n) = {prec=ref(Options.lowest_fsymbol_precedence),name=n}
fun default_bfv_pa(n) = {prec=ref(Options.lowest_fsymbol_precedence),assoc=ref(NONE:bool option),name=n}

fun default_ufv_pa_for_procs(n) = {prec=ref(Options.lowest_fsymbol_precedence),name=n}
fun default_bfv_pa_for_procs(n) = {prec=ref(Options.lowest_fsymbol_precedence),assoc=ref(NONE:bool option),name=n}

val default_fv_pa_for_procs = default_fv_pa

fun getClosureArity(closFunVal(A.functionExp({params,...}),_,_)) = List.length(params)
  | getClosureArity(closUFunVal(_)) = 1 
  | getClosureArity(closBFunVal(_)) = 2 

fun getMethodClosureArity(A.methodExp({params,...})) = List.length(params)

fun makeVarSortPrinter() = F.varToString

val termType = "Term"
val termLCType = "term"
val metaIdType = "Meta-identifier"
val metaIdLCType = "meta-identifier"
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
val closBFunType = "Procedure"
val closBFunLCType = "procedure"
val closUFunType = "Procedure"
val closUFunLCType = "procedure"
val closFunType = "Procedure"
val closFunLCType = "procedure"
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
val tableType = "Table"
val mapType = "Map"
val mapLCType = "map"
val tableLCType = "table"
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
  | getType(primBFunVal(_)) = functionType
  | getType(closFunVal(_)) = closFunType
  | getType(closUFunVal(_)) = closUFunType
  | getType(closBFunVal(_)) = closBFunType
  | getType(methodVal(_)) = methodType
  | getType(primUMethodVal(_)) = methodType
  | getType(primBMethodVal(_)) = methodType
  | getType(closUMethodVal(_)) = closMethodType
  | getType(closBMethodVal(_)) = closMethodType
  | getType(closMethodVal(_)) = closMethodType
  | getType(subVal(_)) = subType
  | getType(unitVal) = unitType
  | getType(cellVal(_)) = cellType 
  | getType(charVal(_)) = charType
  | getType(tableVal(_)) = tableType
  | getType(mapVal(_)) = mapType
  | getType(vectorVal(_)) = vectorType

fun getLCType(termVal(_)) = termLCType
  | getLCType(termConVal(_)) = termConLCType
  | getLCType(propConVal(A.forallCon)) = quantLCType
  | getLCType(propConVal(A.existsCon)) = quantLCType
  | getLCType(propConVal(A.existsUniqueCon)) = quantLCType
  | getLCType(propConVal(_)) = propConLCType
  | getLCType(propVal(_)) = propLCType 
  | getLCType(listVal(_)) = listLCType
  | getLCType(funVal(_)) = functionLCType
  | getLCType(primBFunVal(_)) = functionLCType
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

exception GenEx of string * (AbstractSyntax.pos option)

fun genError(msg,pos_opt) = (raise GenEx(msg,pos_opt))

val true_term = AT.true_term
val false_term = AT.false_term

val true_val = termVal(true_term)
val false_val = termVal(false_term)

val true_prop_val = propVal(Prop.true_prop)
val false_prop_val = propVal(Prop.false_prop)

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

fun isClosMethod(closMethodVal(_)) = true
  | isClosMethod(closUMethodVal(_)) = true
  | isClosMethod(closBMethodVal(_)) = true
  | isClosMethod(_) = false

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
                     genError("Illegal character code passed to character output function",NONE)))

fun stringValToString([]) = ""
  | stringValToString(c::more) = charValToString(c)^stringValToString(more)

fun printStringVal([]) = ()
  | printStringVal(charVal(10)::more) = (print("\n");printStringVal(more)) 
  | printStringVal(charVal(9)::more) = (print("\t");printStringVal(more)) 
  | printStringVal(charVal(32)::more) = (print(" ");printStringVal(more))
  | printStringVal(charVal(c)::more) = (print(charValToString(c));printStringVal(more))
  | printStringVal(_::more) = genError("Wrong kind of argument encountered in the "^
                                       " list given to print",NONE);
  
fun valToString(v as termVal(_)) =  prettyValToString(v)
  | valToString(termConVal(regFSym(some_fsym))) = MS.name(D.fsymName(some_fsym))
  | valToString(termConVal(athNumFSym(anum))) = A.athNumberToString(anum)
  | valToString(termConVal(metaIdFSym(str))) = N.metaIdPrefix^str
  | valToString(propConVal(con)) = A.propConToString(con)
  | valToString(v as propVal(_)) = "\n"^(prettyValToString(v))^"\n"
  | valToString(funVal(_,name,_)) = name
  | valToString(primUFunVal(_,{name,...})) = name ^ " (primitive)"
  | valToString(primBFunVal(_,{name,...})) = name ^ " (primitive)"

  | valToString(closFunVal(A.functionExp({pos,...}),_,{name,...})) = 
       let val name' = !name
           val pos_info = (A.posToString pos)
       in
         (name')^(if pos_info = "" then "" else
                     " (defined at "^(A.posToString pos)^")")
       end
  | valToString(closFunVal(_)) = ""
  | valToString(closUFunVal(e,_,_,{name,...})) =
     let val pos_info = (A.posToString (A.posOfExp e))
     in
       (if pos_info = "" then (!name) ^ "(defined procedure)"  
        else (!name) ^ " (defined at "^pos_info^")")
     end
  | valToString(closBFunVal(e,_,_,_,{name,...})) = 
     let val pos_info = (A.posToString (A.posOfExp e))
     in
       (if pos_info = "" then (!name) ^ " (defined procedure)"  
        else (!name) ^ " (defined at "^pos_info^")")
     end
  | valToString(methodVal(_,code)) = (S.name code) ^ " (primitive)"
  | valToString(primUMethodVal(_,code)) = (S.name code) ^ " (primitive)"
  | valToString(primBMethodVal(_,code)) = (S.name code) ^ " (primitive)"
  | valToString(closUMethodVal(d,_,_,name)) = 
     let val pos_info = (A.posToString (A.posOfDed d))
     in
       (if pos_info = "" then (!name) else (!name) ^ " (defined at "^pos_info^")")
     end
  | valToString(closBMethodVal(d,_,_,_,name)) = 
     let val pos_info = (A.posToString (A.posOfDed d))
     in
       (if pos_info = "" then (!name) else (!name) ^ " (defined at "^pos_info^")")
     end
  | valToString(closMethodVal(A.methodExp({name,pos,...}),_)) = 
     let val pos_info = (A.posToString pos)
     in
       (!name)^(if pos_info = "" then "" else " (defined at "^pos_info^")")
     end
  | valToString(listVal(vals)) = "["^valsToStrings(vals)^"]"
  | valToString(vectorVal(val_vec)) = "|"^valsToStrings(Basic.arrayToList(val_vec))^"|"
  | valToString(subVal(sub)) = Terms.subToString(sub)
  | valToString(unitVal) = "()"
  | valToString(cellVal(vr)) = "cell"
  | valToString(charVal(i)) = "`"^charValToString(i)
  | valToString(tableVal(tab)) = "|[" ^ (tableToString tab) ^ "]|"
  | valToString(mapVal(m)) = mapToString(m)
  | valToString(_) = "Not sure how to print this value...\n"
and valToStringUnlimited(listVal(vals)) = "["^allValsToStrings(vals)^"]"
  | valToStringUnlimited(v) = valToString(v)
and prettyValToStringWithSpacesUnlimited(v,spaces) = 
    let val varSortPrinter = makeVarSortPrinter()
        fun f(propVal(P)) = P.toPrettyString(spaces,P,varSortPrinter)
          | f(termVal(t)) = AT.toPrettyString(spaces,t,varSortPrinter)
          | f(v) = valToStringUnlimited(v) 
    in
       f v
    end
and prettyValToStringUnlimited(v) = prettyValToStringWithSpacesUnlimited(v,0)
and valToStringAlt(v as propVal(_)) = 
        let val s = (prettyValToString(v))
        in
           if (String.size(s) < 50) then s else "\n"^s^"\n"
        end
  | valToStringAlt(v) = valToString(v)                              
and bindingsToString(L,opening,closing) = 
      let val (L,chopped) = if length(L) > 256 then (List.take(L,256),true) else (L,false) 
          val string_pairs = map (fn (a,b) => ((valToStringAlt a), (valToString b))) L
	  val total_size = List.foldl (fn ((s1,s2),sum) => String.size(s1) + String.size(s2) + sum) 0 string_pairs 
	  val sep = if total_size > 50 then "\n" else ", "
          val str = Basic.printListStr(string_pairs,fn (s1,s2) => s1 ^ " " ^ (Names.map_key_val_separator) ^ " " ^ s2,sep)
          val str = if chopped then str^"\n...\n" else str 
       in
         if null(L) then opening ^ closing else 
         if total_size > 50 then "\n"^opening^"\n"^str^"\n"^closing
         else opening^str^closing
       end
and tableToString(tab) = 
       let val L = HashTable.listItemsi tab
       in
         bindingsToString(L,"","")
       end
and mapToString(m) = 
       let val L = Maps.listKeyValuePairs(m) 
       in
         bindingsToString(L,"|{","}|")
       end
and
    allValsToStrings(vals) = Basic.printListStr(vals,valToString," ")
and 
  valsToStrings(vals) = if length(vals) > 512 then (allValsToStrings(List.take(vals,512)))^" ... "
   			else allValsToStrings(vals)
and  
  prettyValToStringWithSpaces(v,spaces) = 
    let val varSortPrinter = makeVarSortPrinter()
        fun f(propVal(P)) = P.toPrettyString(spaces,P,varSortPrinter)
          | f(termVal(t)) = AT.toPrettyString(spaces,t,varSortPrinter)
          | f(v) = valToString(v) 
    in
       f v
    end
and
  prettyValToStringWithSpacesFlush(v,spaces) = 
    let val varSortPrinter = makeVarSortPrinter()
        fun f(propVal(P)) = P.toPrettyString(spaces,P,varSortPrinter)
          | f(termVal(t)) = AT.toPrettyString(spaces,t,varSortPrinter)
          | f(listVal(vals)) = "[\n"^(valsToStringWithLines(vals,spaces+1))^"\n"^(Basic.spaces spaces)^"]"
          | f(v) = (valToString v)
    in
       f v
    end
and
  prettyValToString(v) = prettyValToStringWithSpaces(v,0)
and valsToStringWithLines([],_) = "" 
  | valsToStringWithLines([v],space_count) = (Basic.spaces space_count)^(prettyValToStringWithSpacesFlush(v,space_count))
  | valsToStringWithLines(v::more,space_count) = (Basic.spaces space_count)^(prettyValToStringWithSpacesFlush(v,space_count))^"\n"^valsToStringWithLines(more,space_count)

fun valTypeAndString(v) = getType(v)^": "^valToString(v)

fun prettyValToString'(v) = 
  (case isStringValConstructive(v) of
     SOME(str) => str
    | _ => prettyValToString(v))

fun prettyValToStringNoTypes(propVal(P)) = 
	 let val x = !Options.print_var_sorts
	     val _ = Options.print_var_sorts := false 
	     val res = P.toPrettyString(0,P,makeVarSortPrinter())
	     val _ = Options.print_var_sorts := x
	 in
	   res
	 end
  | prettyValToStringNoTypes(termVal(t)) = 
	 let val x = !Options.print_var_sorts
	     val _ = Options.print_var_sorts := false 
	     val res = AT.toPrettyString(0,t,makeVarSortPrinter())
	     val _ = Options.print_var_sorts := x
	 in
	   res
	 end
  | prettyValToStringNoTypes(v) = valToString(v)

fun printVal(v) = 
	let val sortVarPrinter = makeVarSortPrinter()
	    fun f(v as propVal(P)) = (print("\n");print(propType^": "^
              	                      P.toPrettyString(String.size(propType)+2,P,sortVarPrinter));
                   	              print("\n"))
	      | f(v as termVal(t)) = (print("\n");print(termType^": "^
				      AT.toPrettyStringDefault(String.size(termType)+2,t));
                                      print("\n"))
              | f(v as subVal(sub)) = (print("\n");print(subType^": ");Terms.printSub(sub);print("\n"))
              | f(v as tableVal(tab)) = (print("\n");print(tableType^": "^(tableToString tab));print("\n"))
              | f(v as mapVal(tab)) = (print("\n");print(mapType^": "^(mapToString tab));print("\n"))
	      | f(v) = (print("\n"^getType(v));
            		       let val vs = valToString(v) 
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
  | printValNoType(v as mapVal(t)) = print(mapToString t)
  | printValNoType(v) =
                   let val vs = valToString(v) 
                   in 
                      if vs = "" then print("\n") else
                         print(vs)
                   end
		   
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

val empty_val_map:value Symbol.mapping = Symbol.empty_mapping
val empty_mod_map:module Symbol.mapping = Symbol.empty_mapping
val top_val_env:value_environment ref = ref(valEnv({val_map=empty_val_map,mod_map=empty_mod_map}))
val top_val_env_backup = ref(!top_val_env)

val top_assum_base = ABase.top_assum_base

fun getValAndModMaps(valEnv({val_map,mod_map})) = (val_map,mod_map)

val empty_val_env_functional:value_environment  = valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.empty_mapping})

fun flipOrder(LESS) = GREATER
  | flipOrder(GREATER) = LESS
  | flipOrder(EQUAL) = EQUAL

fun compare(termVal(t1),termVal(t2)) = AT.compare(t1,t2)
  | compare(termVal(t),propVal(p)) = 
         (case Prop.isAtom(p) of
             SOME(t') => AT.compare(t,t')
           | _ => LESS)
  | compare(termVal(_),_) = LESS
  | compare(termConVal(regFSym(s1)),termConVal(regFSym(s2))) = MS.compare(Data.fsymName(s1),Data.fsymName(s2))
  | compare(charVal(c1),charVal(c2)) = Int.compare(c1,c2)
  | compare(charVal(c1),termVal(_)) = GREATER
  | compare(charVal(c1),propVal(p)) = 
        (case Prop.isAtom(p) of
             SOME(_) => GREATER
           | _ => LESS)
  | compare(charVal(c1),_) = LESS
  | compare(listVal(L1),listVal(L2)) = Basic.lexOrder(L1,L2,compare)
  | compare(listVal(L1),termVal(_)) = GREATER
  | compare(listVal(L1),charVal(_)) = GREATER
  | compare(listVal(L1),propVal(p)) = 
        (case Prop.isAtom(p) of
             SOME(_) => GREATER
           | _ => LESS)
  | compare(propVal(p1),propVal(p2)) = Prop.compare(p1,p2) 
  | compare(propVal(p),termVal(t)) =          
        (case Prop.isAtom(p) of
             SOME(t') => AT.compare(t,t')
           | _ => GREATER)
  | compare(propVal(p1),charVal(_)) = GREATER
  | compare(propVal(p1),listVal(_)) = GREATER
  | compare(propVal(p1),v) = LESS
  | compare(v,v' as termVal(_)) = flipOrder(compare(v',v))
  | compare(v,v' as charVal(_)) = flipOrder(compare(v',v))
  | compare(v,v' as listVal(_)) = flipOrder(compare(v',v))
  | compare(v,v' as propVal(_)) = flipOrder(compare(v',v))
  | compare(v,v') = String.compare(valToString(v),valToString(v'))
  
structure ValueKey : ORD_KEY = 
  struct
	type ord_key = value 
        val compare = compare
  end

structure ValueMap: ORDERED_MAP = makeOrdMap(ValueKey)

fun hashVal(termVal(s)) = AT.fastHash(s)
  | hashVal(propVal(p)) = Prop.hash(p)
  | hashVal(termConVal(fsym)) = hashFunSym(fsym)
  | hashVal(propConVal(c)) = A.hashPropCon(c)
  | hashVal(listVal(L)) = Basic.hashWordList(L,hashVal)
  | hashVal(v as (cellVal(cv as ref(v')))) = hashVal(v')
  (* Should preferably be replaced by MLton.hash(cv) in MLton-produced versions of Athena. *)  
  | hashVal(charVal(c)) = Basic.hashInt(c)
  | hashVal(subVal(s)) = Basic.hashString(Terms.subToString(s))
  | hashVal(tableVal(tab)) = Basic.hashString(tableToString(tab))
  | hashVal(mapVal(tab)) = Basic.hashString("MAP"^(mapToString(tab)))
  | hashVal(primUFunVal(_,{name,...})) = Basic.hashString(name)
  | hashVal(primBFunVal(_,{name,...})) = Basic.hashString(name)
  | hashVal(funVal(_,name,_)) = Basic.hashString(name)
  | hashVal(closBFunVal(_,_,_,_,{name,...})) = Basic.hashString(!name)
  | hashVal(closFunVal(_,_,{name,...})) = Basic.hashString(!name)
  | hashVal(closUFunVal(_,_,_,{name,...})) = Basic.hashString(!name)
  | hashVal(primUMethodVal(_,code)) = Basic.hashString(S.name(code))
  | hashVal(primBMethodVal(_,code)) = Basic.hashString(S.name(code))
  | hashVal(methodVal(_,code)) = Basic.hashString(S.name(code))
  | hashVal(closUMethodVal(_,_,_,name)) = Basic.hashString(!name)
  | hashVal(closBMethodVal(_,_,_,_,name)) = Basic.hashString(!name)
  | hashVal(closMethodVal(A.methodExp({name,...}),_)) = Basic.hashString(!name)
  (* Should preferably be replaced by MLton.hash(v) in MLton-produced versions of Athena: *)    
  | hashVal(v) = Basic.hashString(valToString(v)) 
                  
fun makeValMapping(key_value_pairs: (value * value) list) = 
  let val empty_map: (value,value) Maps.mapping = Maps.makeMap(compare)
      val mapping = Maps.insertLst(empty_map,key_value_pairs)
  in
     mapVal(mapping)
  end

fun env2String(valEnv({val_map,mod_map})) = 
      let fun valEntryString(sym,v) = (Symbol.name sym)^" --> "^(prettyValToString v)
          fun modEntryString(sym,m) =    (Symbol.name sym)^" --> module ... "
          val val_entries = map valEntryString (Symbol.listSymbolsAndImages val_map)
          val mod_entries = map modEntryString (Symbol.listSymbolsAndImages mod_map)
          val str1 = Basic.printListStr(val_entries,Basic.id,"\n")
          val str2 = Basic.printListStr(mod_entries,Basic.id,"\n")
      in 
         str1^(if str2 = "" then "" else "\n"^str2)
      end

fun env2String(valEnv({val_map,mod_map}),space_count) = 
      let val offset = 3
          fun valEntryString(sym,v) = 
                 let val str = Symbol.name sym
                     val offset' = String.size(str) + 5
                 in
                    (Basic.spaces space_count)^str^" --> "^(prettyValToStringWithSpacesFlush(v,space_count+offset'))
                 end
          val val_entries = map valEntryString (Symbol.listSymbolsAndImages val_map)
          val mod_entries = map (fn (s,m) => modEntryString(s,m,space_count)) (Symbol.listSymbolsAndImages mod_map)
          val str1 = Basic.printListStr(val_entries,Basic.id,"\n")
          val str2 = Basic.printListStr(mod_entries,Basic.id,"\n")
      in 
         str1^(if str2 = "" then "" else "\n"^str2)
      end
and modEntryString(sym,m:module as {env,...},space_count) = 
            let val offset = (String.size(Symbol.name sym)) + 4 + 3
                val (tv_map,tm_map) = getValAndModMaps(env)
            in
               (Basic.spaces space_count)^(Symbol.name sym)^" --> module { ### "^(Int.toString(Symbol.domainSize(tv_map) + Symbol.domainSize(tm_map)))^" bindings \n"^
               (env2String(env,space_count+offset))^(Basic.spaces (space_count + offset))^"\n"^(Basic.spaces(space_count+offset-2))^"}"
            end

fun envToString(e) = env2String(e,0)
fun modEnvToString(mod_name,e) = modEntryString(mod_name,e,0)

fun coerceFunSymbolIntoTerm(termConVal(regFSym(some_fsym))) = 
          if D.fsymArity(some_fsym) > 0 then NONE 
          else
             SOME(AT.makeConstant(D.fsymName(some_fsym)))
  | coerceFunSymbolIntoTerm(termConVal(athNumFSym(anum))) = SOME(AT.makeNumTerm(anum))
  | coerceFunSymbolIntoTerm(termConVal(metaIdFSym(str))) = SOME(AT.makeIdeConstant(str))
  | coerceFunSymbolIntoTerm(_) = NONE


fun coerceValIntoProp(propVal(P)) = SOME(P)
  | coerceValIntoProp(termVal(t)) = P.makeAtomOpt(t)
  | coerceValIntoProp(v as termConVal(_)) = (case coerceFunSymbolIntoTerm(v) of
                                                SOME(t) => P.makeAtomOpt(t)
                                              | _ => NONE)
  | coerceValIntoProp(v) = NONE

fun makeAthenaInt(i) = termVal(AthTerm.makeNumTerm(A.int_num(i,ref "")))
fun makeAthenaReal(x) = termVal(AthTerm.makeNumTerm(A.real_num(x,ref "")))

fun makeEmptyModule(name) = let val m:module = {mod_name=A.msym(name),env=empty_val_env_functional,open_mod_directives=[]}
                            in
                               m 
                            end

val empty_val_env:value_environment ref = ref(valEnv({val_map=Symbol.empty_mapping,mod_map=Symbol.empty_mapping}))

fun msym(s) = ModSymbol.makeModSymbol([],s,s)

fun msyms(sym_set) = let val syms = Symbol.listSymbols(sym_set)
                         val msyms = map msym syms
                     in
                        ModSymbol.symListToSet(msyms)
                     end

fun qualifyNameStr(str,mod_path) = 
     (case mod_path of
         [] => str
       | _ => (Basic.printListStr(mod_path,Symbol.name,"."))^"."^str)

fun qualifyName(name,mod_path) = 
     (case mod_path of
         [] => ModSymbol.makeModSymbol([],name,name)
       | m::rest => let val str = (Basic.printListStr(mod_path,Symbol.name,"."))^"."^(Symbol.name(name))
                    in
                      ModSymbol.makeModSymbol(mod_path,name,Symbol.symbol str)
                    end)

(***
Use fullyQualifySort (or the qualifySort immediately below) to qualify a sort term,
such as (List-Of (Pair-Of N.Nat A.B.Foo) Int). Use fullyQualifySortString below
to qualify a simple structure or domain name, such as "List-Of". 
***)

fun fullyQualifySort(absyn_type) = 
      let fun debugPrint(str) = ()
          fun decide(sort_name) =  
                let val sort_name_as_symbol = MS.nameAsSymbol(sort_name)
                    fun loop([]) = sort_name
                      | loop(path::rest) = let val sort_name' = qualifyName(sort_name_as_symbol,path)
                                           in
                                             if Data.isAnySortFlexible(sort_name') then sort_name' 
                                             else (case MS.find(Data.sort_abbreviations,sort_name') of
                                                      SOME(_) => sort_name'
                                                    | _ => loop(rest))
                                           end
                in
                   (case MS.split(sort_name) of
                       (first_mod::rest_mods,main_name) => if Symbol.symEq(first_mod,N.top_module_symbol) then 
                                                              MS.makeModSymbol'(rest_mods,main_name)
                                                           else loop(!(Paths.open_mod_paths))
                     | _ => loop(!(Paths.open_mod_paths)))

                end
          fun transformSortName(sort_name) = decide(sort_name)
          val absyn_type' = SymTerm.transform transformSortName absyn_type
          val res = Terms.replaceTaggedSymTermConstants(absyn_type',fn sym => MS.find(Data.sort_abbreviations,sym),A.dum_pos)
      in
        res
      end

fun qualifySort(absyn_type) = fullyQualifySort(absyn_type)

fun fullyQualifySortString(structure_name) = 
      let fun debugPrint(str) = print(str) 
          val structure_symbol = Symbol.symbol structure_name 
          fun decide(name:Symbol.symbol) =  
                let fun loop([]) = name 
                      | loop(path::rest) = let val name' = qualifyName(name,path)
                                           in
                                             if Data.isAnySort(name') then MS.nameAsSymbol(name') 
                                                else
                                                    (case MS.find(Data.sort_abbreviations,name') of
                                                        SOME(struc) => Symbol.symbol(SymTerm.toStringDefault(struc))
                                                      | _ => loop(rest))
                                           end
                in
                  loop(!(Paths.open_mod_paths))
                end
      in
        Symbol.name(decide(structure_symbol))
      end

(***
For fullyQualifyString, pass a value of 0 for the parameter sort_or_fsym 
to qualify a sort name, and pass a value of 1 to qualify a function symbol name.
***)

fun fullyQualifyString(name_str,sort_or_fsym) = 
      let val decider = if sort_or_fsym = 0 then Data.isAnySort else Data.isTermConstructorBool
          fun decide(name:Symbol.symbol) =  
                let fun loop([]) = name 
                      | loop(path::rest) = let val name' = qualifyName(name,path)
                                           in
                                             if decider(name') then MS.nameAsSymbol(name') 
                                             else (if sort_or_fsym = 0 then
                                                      (case MS.find(Data.sort_abbreviations,name') of
                                                          SOME(struc_name) => Symbol.symbol(SymTerm.toStringDefault(struc_name))
                                                        | _ => loop(rest))
                                                   else loop(rest))
                                           end
                in
                  loop(!(Paths.open_mod_paths))
                end
          val name_as_symbol = Symbol.symbol name_str 
      in
        Symbol.name(decide(name_as_symbol))
      end  

fun fullyQualifySortString(structure_name) = fullyQualifyString(structure_name,0)
fun fullyQualifyFSymString(fsym_name) = fullyQualifyString(fsym_name,1)

fun tryFullQualification(fsym_name) = 
   if Data.isTermConstructorBool(fsym_name) then fsym_name
   else let fun debugPrint(str) = ()
            fun loop([]) = fsym_name
              | loop(path::rest) = let val full_name = qualifyName(MS.lastName(fsym_name),path)
                                   in
                                      if Data.isTermConstructorBool(full_name) then full_name else loop(rest)
                                   end
         in
            loop(!(Paths.open_mod_paths))
         end

fun qualifyFSym(fsym_name,mod_path) = 
       let val qualified_fsym_name = qualifyName(MS.lastName(fsym_name),mod_path)
       in
         if Data.isTermConstructorBool(qualified_fsym_name) then qualified_fsym_name
         else tryFullQualification(fsym_name) 
       end

fun qualifyFSym(fsym_name) = 
        let fun debugPrint(str) = print(str)
            val fsym_name_as_symbol = MS.nameAsSymbol(fsym_name)
            fun loop([]) = fsym_name
              | loop(path::rest) = let val fsym_name' = qualifyName(fsym_name_as_symbol,path)
                                   in
                                      if Data.isTermConstructorBool(fsym_name') then fsym_name' else loop(rest)
                                   end
         in
           (case MS.split(fsym_name) of
              (first_mod::rest_mods,main_name) => if Symbol.symEq(first_mod,N.top_module_symbol) then 
                                                     MS.makeModSymbol'(rest_mods,main_name)
                                                  else loop(!(Paths.open_mod_paths))
           | _ => loop(!(Paths.open_mod_paths)))
         end

val string_literals:value RSA.rs_array = RSA.makeRSArray(128,listVal([]))

val _ = RSA.setIncrement(256)

val global_string_literal_array_index = ref(0)

fun coerceTermIntoTermCon(t) = 
      (case AT.isConstant(t) of
          SOME(f) => (case MS.find(Data.fsym_table,f) of
                         SOME(fsym) => SOME(regFSym(fsym))
                       | _ => NONE)
        | _ => (case AT.isNumConstantOpt(t) of
                   SOME(anum) => SOME(athNumFSym(anum))
                 | _ => (case AT.isIdeConstant(t) of
                            SOME(str) => SOME(metaIdFSym(str))
                          | _ => NONE)))
	  
fun isGloballyBound(msym,sym) = 
   (case !top_val_env of
      (e as (valEnv({val_map,...}))) => 
         (case Symbol.lookUp(val_map,sym) of 
            SOME(termVal(t)) => (case AT.isConstant(t) of
                                    SOME(f) => not(Symbol.symEq(MS.nameAsSymbol(f),sym))
                                  | _ => true)
          | SOME(_) => true
          | _ => false))

val (preProcessExp,preProcessDed,preProcessPhrase,
     preProcessExpLst,preProcessDedLst,preProcessPhraseLst,
     preProcessPattern,preProcessPattern',preProcessPatternLst,preProcessPatternLst') = 
    
let val mod_path_cell:Symbol.symbol list ref = ref([])
    val sort_var_table: FTerm.term S.htable = S.makeHTable()
    fun debug() = false
    fun dbprint(s) = if debug() then print(s) else ()
    val match_sort_var_table: FTerm.term S.htable = S.makeHTable()
    fun clearSortVarTables() = (S.clearHTable(sort_var_table);
                                S.clearHTable(match_sort_var_table))
    fun matchFind(sort_var) = S.find(match_sort_var_table,sort_var)
    fun find(sort_var) = (case S.find(sort_var_table,sort_var) of
                             NONE => S.find(match_sort_var_table,sort_var)
                           | res => res)	
    fun printSymTermVar(sym) = (Names.sort_variable_prefix)^(Symbol.name sym)
    fun symSortToString(sym_tagged_sort) = SymTerm.toPrettyString(14,(SymTerm.stripTags(sym_tagged_sort)),printSymTermVar)
    fun untaggedSymSortToString(sym_sort) = SymTerm.toPrettyString(14,sym_sort,printSymTermVar)
    fun invalidSort(sort_as_tagged_symterm,pos) = 
       let val pos = SymTerm.getTopTag(sort_as_tagged_symterm)
       in
          Data.genEx("Invalid sort: "^(symSortToString sort_as_tagged_symterm),SOME(pos),!Paths.current_file)
       end
    fun translateSort(sort_as_symterm,tagged_vars) = 
     let val _ = if debug() then
                    print("\nAbout to translate this sort_as_symterm: " ^ (untaggedSymSortToString sort_as_symterm) ^ "\n")
                 else ()
         val res = (case SymTerm.isVar(sort_as_symterm) of 
 	              SOME(v) => (case find(v) of 
		 	            SOME(v') => let val _ = if debug() then print("FOUND THIS for th var sym_sort " ^ 
  				                                (untaggedSymSortToString sort_as_symterm) ^ ": " ^ (F.toStringDefault(v')) ^ "\n") 
                                                            else ()
                                                in
                                                  v' 
                                                end
 			          | _ => (let val _ = if debug() then print("\nNOTHING FOUND for this var sym_sort: " ^ 
				                         (untaggedSymSortToString sort_as_symterm) ^ ".\n")
                                                      else ()
                                              val v' = if tagged_vars then FTerm.makeTaggedFreshVar() else FTerm.makeFreshVar() 
				              val _ = Symbol.insert(sort_var_table,v,v')
				          in
				             v'
				          end))
 	           | _ => (case SymTerm.isApp(sort_as_symterm) of
		              SOME(fsym,sorts) => let val sorts' = map (fn sort => translateSort(sort,tagged_vars)) sorts
			 	                  in
					            FTerm.makeApp(fsym,sorts')
				                  end
 		            | _ => raise Basic.Never))
     in   
	res
    end
    fun translateSortAux(sort_as_symterm) = 
	(case SymTerm.isVar(sort_as_symterm) of 
	    SOME(v) => (case matchFind(v) of 
			   SOME(v') => v' 
			 | _ => (let val v' = FTerm.makeFreshVar() 
				     val _ = Symbol.insert(match_sort_var_table,v,v')
				 in
				    v'
				 end))
	 | _ => (case SymTerm.isApp(sort_as_symterm) of
		   SOME(fsym,sorts) => let val sorts' = map translateSortAux sorts
				       in
					  FTerm.makeApp(fsym,sorts')
				       end
		 | _ => raise Basic.Never))
    fun getFTermSortFromSTermSort(sort_as_sym_term_opt,name,pos:Position.PosType) = 
       (case sort_as_sym_term_opt of
	    SOME(tagged_sort) => 
	       let val tagged_sort' = qualifySort(tagged_sort)
                   val sort' = SymTerm.stripTags(tagged_sort')
                   val sort = Terms.replaceSymTermConstants(sort',fn sym => MS.find(Data.sort_abbreviations,qualifyName(MS.lastName(sym),!mod_path_cell)))
                   val cond = SymTerm.isLegalFlex(sort,Data.sortConstructorArity,fn _ => true,Names.fun_name_msym)
	       in
                  if cond 
	          then let val ts = translateSort(sort,true) 
                       in SOME(ts) end
                  else NONE 
               end
         | _ => NONE)
    fun getFTermSortFromSTermSortWithError(sort_as_sym_term_opt,name,pos:Position.PosType) = 
       (case sort_as_sym_term_opt of
	    SOME(tagged_sort) => 
	       let val tagged_sort' = qualifySort(tagged_sort) 
                   val sort' = SymTerm.stripTags(tagged_sort')
                   val sort = Terms.replaceSymTermConstants(sort',fn sym => MS.find(Data.sort_abbreviations,sym))
	       in
                  if SymTerm.isLegalFlex(sort,Data.sortConstructorArity,fn _ => true,Names.fun_name_msym)
	          then SOME(translateSort(sort,true)) 
                  else invalidSort(tagged_sort',pos)
               end
         | _ => NONE)
    fun getFTermSortFromSTermSortAux(sort_as_sym_term_opt,name,pos:Position.PosType) = 
       (case sort_as_sym_term_opt of
	    SOME(tagged_sort) => 
	       let val tagged_sort' = qualifySort(tagged_sort)
                   val sort' = SymTerm.stripTags(tagged_sort')
                   val sort = Terms.replaceSymTermConstants(sort',fn sym => MS.find(Data.sort_abbreviations,sym))
	       in
                  if SymTerm.isLegalFlex(sort,Data.sortConstructorArity,fn _ => true,Names.fun_name_msym)
	          then SOME(translateSortAux(sort)) 
		  else invalidSort(tagged_sort',pos)
               end
         | _ => NONE)
    fun ppExp(e as A.idExp({msym,pos,sym,no_mods,...}),vars,bound_ids) = 
      let val full_name = MS.name(msym)
          val name' = qualifyFSym(msym)
	  val igb = isGloballyBound(name',sym)
	  val cond = (Data.isConstantTermConstructor(name') andalso Data.isPolySymbol(name') andalso 
                       (not(no_mods) orelse (not(Symbol.isMember(sym,bound_ids)) andalso not(igb))))
      in
        if cond
        then let val sym_sig as (arg_sorts,res_sort,is_poly,involves_pred_based_sorts) = Data.getSignature(name')
                 val sort_string = F.toStringDefault(res_sort)
                 fun isVar(str) = let val str_lst = explode str
  	        	   	  in not(null(str_lst)) andalso 
			             hd(str_lst) = Names.sort_variable_prefix_as_char
			          end
		 val sort_as_tagged_sym_term = (case Terms.parseSymTerm(sort_string,isVar) of 
                                                   SOME(sort_as_sym_term) => Terms.putBogusTags(sort_as_sym_term,A.dum_pos)
                                                 | _ => Basic.fail("Failed to translate custom-inserted symbol f-term sort into a sym-term sort!\n"))
                 val sort_as_tagged_symterm' = qualifySort(sort_as_tagged_sym_term)
                 val sort_as_symterm = SymTerm.stripTags(sort_as_tagged_symterm')
		 val sort = translateSort(sort_as_symterm,true)
                 val e' = A.taggedConSym({name=name',sort_as_tagged_symterm=sort_as_tagged_symterm',sort_as_fterm=SOME(sort),pos=pos})
             in
                (e',vars,MS.singleton(msym))
             end
        else
          (case A.getAthNumber(full_name) of
              SOME(athena_number) => 
			(A.numExp({number=athena_number,pos=pos}),vars,MS.empty_set)
             | _ => let val free_ids = if full_name = "." then MS.empty_set else MS.singleton(msym)
                    in
                       (e,vars,free_ids)
                    end)
      end
  | ppExp(e as A.opExp({op_exp,pos}),vars,bound_ids) = 
           let val (op_exp',vars',fids) = ppExp(op_exp,vars,bound_ids)
           in
              (A.opExp({op_exp=op_exp',pos=pos}),vars',fids)
           end
  | ppExp(e as A.numExp({number=num as A.int_num(_,str),...}),vars,_) = (e,vars,MS.empty_set)
  | ppExp(e as A.numExp({number=num as A.real_num(_,str),...}),vars,_) = (e,vars,MS.empty_set)
  | ppExp(e as A.taggedConSym({name,sort_as_tagged_symterm,pos,...}),vars,_) = 
     let val name' = qualifyFSym(name)
     in
	if not(Data.isConstantTermConstructor(name')) then 
	   Data.genEx("Only variables and term constants can be annotated\nwith sorts; "^
		     (MS.name(name))^" is neither.",SOME(pos),!Paths.current_file)
	else
	     let val sort_as_tagged_symterm' = qualifySort(sort_as_tagged_symterm)
                 val sort_as_tagged_symterm = sort_as_tagged_symterm'
                 val sort_as_symterm = SymTerm.stripTags(sort_as_tagged_symterm)
		 fun invalidSort() = let val pos' = {line = #line(pos),file = #file(pos),
					      pos = #pos(pos)+(String.size(MS.name(name))+1)}
					 val is = (SymTerm.toPrettyString(0,sort_as_symterm,printSymTermVar))
					 val is' = (SymTerm.toString(sort_as_symterm,printSymTermVar))
				     in
				        Data.genEx("Invalid sort given for "^(MS.name(name))^": "^
					(if Basic.oneLine(is) then is' else "\n"^is^"."),
			   		SOME(pos'),!Paths.current_file)
				     end
		 val _ = if SymTerm.isLegalFlex(sort_as_symterm,Data.sortConstructorArity,fn _ => true,Names.fun_name_msym) then ()
			 else invalidSort()
		 val sort = translateSort(sort_as_symterm,true)
		 val (param_sorts,result_sort,is_poly,has_pred_based_sorts) = Data.getSignature(name')
		 val _ = if FTerm.isInstanceOf(sort,result_sort) orelse FTerm.isSubSortBool(result_sort,sort) then ()
			 else invalidSort()
	     in
                 case A.getAthNumber(MS.name(name)) of
                     SOME(athena_number) => (A.numExp({number=athena_number,pos=pos}),vars,MS.singleton(name))
                   | _ => (A.taggedConSym({name=name',sort_as_tagged_symterm=sort_as_tagged_symterm,pos=pos,
    		 	                   sort_as_fterm=SOME(sort)}),vars,MS.singleton(name))
	     end
     end
  | ppExp(e as A.termVarExp({term_var,pos,user_sort=SOME(sort_as_tagged_symterm)}),vars,bound_ids) = 
	     let val sort_as_tagged_symterm' = qualifySort(sort_as_tagged_symterm)
                 val sort_as_tagged_symterm = sort_as_tagged_symterm'
                 val sort_as_symterm' = SymTerm.stripTags(sort_as_tagged_symterm)
                 val sort_as_symterm = Terms.replaceSymTermConstants(sort_as_symterm',fn sym => MS.find(Data.sort_abbreviations,sym))
		 fun printSymTermVar(sym) = (Names.sort_variable_prefix)^(S.name sym)
                 val is_legal = SymTerm.isLegalFlex(sort_as_symterm,Data.sortConstructorArity,fn _ => true,Names.fun_name_msym)
		 val _ = 
                        (if is_legal then ()
			 else let val pos' = {line = #line(pos), file = #file(pos), 
					      pos = #pos(pos)+(String.size(ATV.name(term_var))+2)}
			      in
				   Data.genEx("Invalid sort: "^
					      (SymTerm.toPrettyString(14,sort_as_symterm,printSymTermVar)),
			   		      SOME(pos'),!Paths.current_file)
			      end)
		 val sort = translateSort(sort_as_symterm,true)
		 val v = AthTermVar.swapSorts(term_var,sort)
		 val e' = A.termVarExp({term_var=v,pos=pos,user_sort=SOME(sort_as_tagged_symterm)})
	     in
		(e',ATV.add(v,vars),MS.empty_set) 
	     end
  | ppExp(e as A.termVarExp({term_var,pos,user_sort=NONE}),vars,_) = (e,ATV.add(term_var,vars),MS.empty_set)
  | ppExp(A.logicalAndExp({args,pos}),vars,bound_ids) = 
                                              let val (phrases,vars',fids) = ppPhraseLst(args,vars,bound_ids)
                                              in
                                                (A.logicalAndExp({args=phrases,pos=pos}),vars',fids)
                                              end
  | ppExp(A.logicalOrExp({args,pos}),vars,bound_ids) = 
                                             let val (args',vars',fids) = ppPhraseLst(args,vars,bound_ids)
                                             in
                                                (A.logicalOrExp({args=args',pos=pos}),vars',fids)
                                             end
  | ppExp(A.whileExp({test,body,pos}),vars,bound_ids) = 
                                              let val (test',vars',fids1) = ppPhrase(test,vars,bound_ids)
                                                  val (body',vars'',fids2) = ppPhrase(body,vars',bound_ids)
                                              in
                                                (A.whileExp({test=test',body=body',pos=pos}),vars'',MS.union(fids1,fids2))
                                              end
  | ppExp(A.beginExp({members,pos}),vars,bound_ids) = 
                                            let val (members',vars',fids) = ppPhraseLst(members,vars,bound_ids)
                                            in
                                               (A.beginExp({members=members',pos=pos}),vars',fids)
                                            end
  | ppExp(A.tryExp({choices,pos}),vars,bound_ids) = 
                                          let val (choices',vars',fids) = ppExpLst(choices,vars,bound_ids)
                                          in
                                             (A.tryExp({choices=choices',pos=pos}),vars',fids)
                                          end
  | ppExp(A.checkExp({clauses,pos}),vars,bound_ids) = 
                                             (A.checkClauses(clauses,pos);
                                             let val (clauses',vars',fids) = ppCheckClauseLst(clauses,vars,bound_ids)
                                             in
                                                (A.checkExp({clauses=clauses',pos=pos}),vars',fids)
                                             end)
  | ppExp(A.functionExp({params,body,pos}),vars,bound_ids) = 
     let fun doParams([],results) = rev results
           | doParams((p as (A.wildCard _))::more,results) = doParams(more,p::results)
           | doParams((A.someParam ptp)::more,results) = (case doPossiblyTypedParam(ptp,vars,bound_ids) of
                                                             (_,ptp',sort_vars,sort_fids) => doParams(more,(A.someParam ptp')::results))
         val params' = doParams(params,[])
         val param_names_as_syms = (A.getPWParamNames(params))
         val param_names = MS.symListToSet(map msym param_names_as_syms)                                           
         val (body',vars',fids) = ppExp(body,vars,Symbol.union(Symbol.symListToSet(param_names_as_syms),bound_ids))
     in
        (A.functionExp({params=params',body=body',pos=pos}),vars',
         MS.difference(fids,param_names))
     end
  | ppExp(A.BAppExp({proc,arg1,arg2,pos}),vars,bound_ids) = 
      let val (proc',vars',fids1) = ppPhrase(proc,vars,bound_ids)
          val ([arg1',arg2'],vars'',fids2) = ppPhraseLst([arg1,arg2],vars',bound_ids)
      in
         (A.BAppExp({proc=proc',arg1=arg1',arg2=arg2',pos=pos}),vars'',MS.union(fids1,fids2))
      end 
  | ppExp(A.UAppExp({proc,arg,pos}),vars,bound_ids) = 
      let val (proc',vars',fids1) = ppPhrase(proc,vars,bound_ids)
          val (arg',vars'',fids2) = ppPhrase(arg,vars',bound_ids)
      in
         (A.UAppExp({proc=proc',arg=arg',pos=pos}),vars'',MS.union(fids1,fids2))
      end 
  | ppExp(A.appExp({proc,args,pos,alt_exp=ref(NONE)}),vars,bound_ids) = 
      let val (proc',vars',fids1) = ppPhrase(proc,vars,bound_ids)
          val (args',vars'',fids2) = ppPhraseLst(args,vars',bound_ids)
      in
         (A.appExp({proc=proc',args=args',alt_exp=ref(NONE),pos=pos}),vars'',MS.union(fids1,fids2))
      end

  | ppExp(A.appExp({proc,args,pos,alt_exp=ref(SOME(e'))}),vars,bound_ids) = 
      let val (proc',vars',fids1) = ppPhrase(proc,vars,bound_ids)
          val (args',vars'',fids2) = ppPhraseLst(args,vars',bound_ids)
          val (e'',vars''',fids3) = ppExp(e',vars'',bound_ids)
      in
         (A.appExp({proc=proc',args=args',alt_exp=ref(SOME(e'')),pos=pos}),vars'',MS.union(fids1,fids2))
      end
  | ppExp(A.listExp({members,pos}),vars,bound_ids) = 
       let val (members',vars',fids) = ppPhraseLst(members,vars,bound_ids)
       in
          (A.listExp({members=members',pos=pos}),vars',fids)
       end
  | ppExp(A.methodExp({params,body,pos,name}),vars,bound_ids) = 
       let val param_names_as_syms = (A.getPWParamNames(params))
           val param_names = MS.symListToSet(map msym param_names_as_syms)                                           
           val (body',vars',fids) = ppDed(body,vars,Symbol.union(Symbol.symListToSet(param_names_as_syms),bound_ids))
       in
          (A.methodExp({params=params,body=body',pos=pos,name=name}),vars',
           MS.difference(fids,param_names))
       end
  | ppExp(A.matchExp({discriminant,clauses,pos}),vars,bound_ids) = 
       let val (discriminant',vars',fids1) = ppPhrase(discriminant,vars,bound_ids)
           val (clauses',vars'',fids2) = ppMatchClauseLst(clauses,vars',bound_ids)
       in
          (A.matchExp({discriminant=discriminant',clauses=clauses',pos=pos}),
           vars'',MS.union(fids1,fids2))
       end
  | ppExp(A.letExp({bindings,body,pos}),vars,bound_ids) = 
       let 
           val (bpat_lst,nameset_lst,defs,pos_lst) = A.splitBindings(bindings)
           val pat_ids = S.unionLst(nameset_lst)
           val (bindings',vars',fids) = ppBindingLst(bpat_lst,defs,pos_lst,vars,bound_ids)
           val (body',vars'',body_fids) = ppExp(body,vars',Symbol.union(bound_ids,pat_ids))
       in
          (A.letExp({bindings=bindings',body=body',pos=pos}),vars'',
           MS.union(fids,MS.difference(body_fids,msyms(pat_ids))))
       end
  | ppExp(A.letRecExp({bindings,body,pos}),vars,bound_ids) = 
       let val (bpat_lst,nameset_lst,defs,pos_lst) = A.splitBindings(bindings)
           val (bindings',vars',fids) = ppLetRecBindingLst(bpat_lst,nameset_lst,defs,pos_lst,vars,bound_ids)
	   val rec_syms = S.unionLst(nameset_lst)
           val rec_msyms = msyms(rec_syms)
           val (body',vars'',body_fids) = ppExp(body,vars',Symbol.union(rec_syms,bound_ids))
           val res_fids = MS.difference(MS.union(fids,body_fids),rec_msyms)
       in
          (A.letRecExp({bindings=bindings',body=body',pos=pos}),vars'',
           res_fids)
       end
  | ppExp(A.cellExp({contents,pos}),vars,bound_ids) = 
       let val (contents',vars',fids) = ppPhrase(contents,vars,bound_ids)
       in
          (A.cellExp({contents=contents',pos=pos}),vars',fids)
       end
  | ppExp(A.refExp({cell_exp,pos}),vars,bound_ids) = 
       let val (cell_exp',vars',fids) = ppExp(cell_exp,vars,bound_ids)
       in
          (A.refExp({cell_exp=cell_exp',pos=pos}),vars',fids)
       end
  | ppExp(A.setCellExp({cell_exp,set_phrase,pos}),vars,bound_ids) = 
       let val (cell_exp',vars',fids1) = ppExp(cell_exp,vars,bound_ids)
           val (set_phrase',vars'',fids2) = ppPhrase(set_phrase,vars',bound_ids)
       in
          (A.setCellExp({cell_exp=cell_exp',set_phrase=set_phrase',pos=pos}),vars'',MS.union(fids1,fids2))
       end
  | ppExp(A.vectorInitExp({length_exp,init_val,pos}),vars,bound_ids) = 
       let val (length_exp',vars',fids1) = ppExp(length_exp,vars,bound_ids)
           val (init_val',vars'',fids2) = ppPhrase(init_val,vars',bound_ids)
       in
          (A.vectorInitExp({length_exp=length_exp',
			    init_val=init_val',pos=pos}),vars'',MS.union(fids1,fids2))
       end
  | ppExp(A.vectorSetExp({vector_exp,index_exp,new_val,pos}),vars,bound_ids) = 
       let val (vector_exp',vars',fids1) = ppExp(vector_exp,vars,bound_ids)
           val (index_exp',vars'',fids2) = ppExp(index_exp,vars',bound_ids)
           val (new_val',vars''',fids3) = ppPhrase(new_val,vars'',bound_ids)
       in
          (A.vectorSetExp({vector_exp=vector_exp',index_exp=index_exp',
			    new_val=new_val',pos=pos}),vars''',MS.union(fids3,MS.union(fids1,fids2)))
       end
  | ppExp(A.vectorSubExp({vector_exp,index_exp,pos}),vars,bound_ids) = 
       let val (vector_exp',vars',fids1) = ppExp(vector_exp,vars,bound_ids)
           val (index_exp',vars'',fids2) = ppExp(index_exp,vars',bound_ids)
       in 
          (A.vectorSubExp({vector_exp=vector_exp',index_exp=index_exp',
			   pos=pos}),vars'',MS.union(fids1,fids2))
       end
  | ppExp(e as A.charExp({code,pos,...}),vars,bound_ids) = 
          if ((code >= 0) andalso (code <= 127)) then 
             (e,vars,MS.empty_set)
          else 
             genError("Illegal character",SOME(pos)) 
  | ppExp(e as A.stringExp({str,pos,...}),vars,bound_ids) = 
          let val cvl = (map charVal str)
              val index = Basic.returnAndInc(global_string_literal_array_index)
              val _ = RSA.updateDefault(string_literals,index,listVal(cvl))
          in
             (A.stringExp({str=str,pos=pos,mem_index=index}),vars,MS.empty_set)
          end
  | ppExp(e,vars,_) = (e,vars,MS.empty_set)
and 
    ppDed(A.assumeDed({assumption,body,pos}),vars,bound_ids) = 
        let val (assumption',vars',fids1) = ppPhrase(assumption,vars,bound_ids) 
            val (body',vars'',fids2) = ppDed(body,vars',bound_ids)
        in
           (A.assumeDed({assumption=assumption',body=body',pos=pos}),vars'',MS.union(fids1,fids2))
        end
  | ppDed(A.byCasesDed({disj,from_exps=SOME(exps),arms,pos}),vars,bound_ids) = 
       let val (disj',vars',fids') = ppPhrase(disj,vars,bound_ids)
           val (exps',vars'',fids'') = ppExpLst(exps,vars',bound_ids)
           val (arms',vars''',fids''') = ppCaseClauseLst(arms,vars'',bound_ids)
       in
           (A.byCasesDed({disj=disj',from_exps=SOME(exps'),arms=arms',pos=pos}),vars''',
           MS.unionLst([fids',fids'',fids''',
                            msyms(S.symListToSet([Names.vpfPrimMethod_symbol,Names.spfPrimMethod_symbol]))]))
       end
  | ppDed(A.byCasesDed({disj,from_exps=NONE,arms,pos}),vars,bound_ids) = 
       let val (disj',vars',fids') = ppPhrase(disj,vars,bound_ids)
           val (arms',vars'',fids'') = ppCaseClauseLst(arms,vars',bound_ids)
       in
           (A.byCasesDed({disj=disj',from_exps=NONE,arms=arms',pos=pos}),vars'',
           MS.unionLst([fids',fids'']))
       end
  | ppDed(A.infixAssumeDed({bindings,body,pos}),vars,bound_ids) = 
        let val (bpat_lst,nameset_lst,defs,pos_lst) = A.splitBindings(bindings)
            val (bindings',vars',fids) = ppBindingLst(bpat_lst,defs,pos_lst,vars,bound_ids)
            val (body',vars'',body_fids) = ppDed(body,vars',bound_ids)
        in
           (A.infixAssumeDed({bindings=bindings',body=body',pos=pos}),vars'',
           MS.union(fids,MS.difference(body_fids,msyms(S.unionLst(nameset_lst)))))
        end
  | ppDed(A.assumeLetDed({bindings,body,pos}),vars,bound_ids) = 
        let val (bpat_lst,nameset_lst,defs,pos_lst) = A.splitBindings(bindings)	     
            val (bindings',vars',fids) = ppBindingLst(bpat_lst,defs,pos_lst,vars,bound_ids)
	    val pat_ids = S.unionLst(nameset_lst)
            val (body',vars'',body_fids) = ppDed(body,vars',Symbol.union(pat_ids,bound_ids))
        in
           (A.assumeLetDed({bindings=bindings',body=body',pos=pos}),vars'',
            MS.union(fids,MS.difference(body_fids,msyms(pat_ids))))
        end
  | ppDed(A.absurdDed({hyp,body,pos}),vars,bound_ids) = 
        let val (hyp',vars',fids1) = ppPhrase(hyp,vars,bound_ids)
            val (body',vars'',fids2) = ppDed(body,vars',bound_ids)
        in
           (A.absurdDed({hyp=hyp',body=body',pos=pos}),vars'',MS.union(fids1,fids2))
        end
  | ppDed(A.absurdLetDed({named_hyp,body,pos}),vars,bound_ids) = 
        let val (named_hyp',vars',hyp_fids) = ppBinding((#bpat(named_hyp),#def(named_hyp),#pos(named_hyp)),
                                                        vars,MS.empty_set,bound_ids)
            val pat_ids = A.patBindableIds(#bpat(named_hyp'))							
            val (body',vars'',body_fids) = ppDed(body,vars',Symbol.union(pat_ids,bound_ids))
        in
           (A.absurdLetDed({named_hyp=named_hyp',body=body',pos=pos}),vars'',
            MS.union(hyp_fids,MS.difference(body_fids,msyms(pat_ids))))
        end
  | ppDed(A.methodAppDed({method,args,pos}),vars,bound_ids) = 
        let val (method',vars',fids1) = ppExp(method,vars,bound_ids)
            val (args',vars'',fids2) = ppPhraseLst(args,vars',bound_ids)
        in
           (A.methodAppDed({method=method',args=args',pos=pos}),vars'',MS.union(fids1,fids2))
        end
  | ppDed(A.BMethAppDed({method,arg1,arg2,pos}),vars,bound_ids) = 
        let val (method',vars',fids1) = ppExp(method,vars,bound_ids)
            val ([arg1',arg2'],vars'',fids2) = ppPhraseLst([arg1,arg2],vars',bound_ids)
        in
           (A.BMethAppDed({method=method',arg1=arg1',arg2=arg2',pos=pos}),vars'',MS.union(fids1,fids2))
        end
  | ppDed(A.UMethAppDed({method,arg,pos}),vars,bound_ids) = 
        let val (method',vars',fids1) = ppExp(method,vars,bound_ids)
            val ([arg'],vars'',fids2) = ppPhraseLst([arg],vars',bound_ids)
        in
           (A.UMethAppDed({method=method',arg=arg',pos=pos}),vars'',MS.union(fids1,fids2))
        end
  | ppDed(A.matchDed({discriminant,clauses,pos}),vars,bound_ids) = 
        let val (discriminant',vars',dis_fids) = ppPhrase(discriminant,vars,bound_ids)
            val (clauses',vars'',clause_fids) = ppDMatchClauseLst(clauses,vars',true,bound_ids)
        in
           (A.matchDed({discriminant=discriminant',clauses=clauses',pos=pos}),vars'',
            MS.union(dis_fids,clause_fids))
        end
  | ppDed(d as A.inductionDed({prop,clauses,pos}),vars,bound_ids) = 
        let val (prop',vars'',fids2) = ppPhrase(prop,vars,bound_ids)
            val (clauses',vars''',fids3) = ppDMatchClauseLst(clauses,vars'',false,bound_ids)
            val res_ded = A.inductionDed({prop=prop',clauses=clauses',pos=pos})
            val _ = A.checkInductionSyntax(res_ded)
        in
           (res_ded,vars''',MS.union(fids2,fids3))
        end
  | ppDed(d as A.structureCasesDed({prop,term,clauses,pos}),vars,bound_ids) = 
        let val (prop',vars'',fids1) = ppPhrase(prop,vars,bound_ids)
            val (clauses',vars''',fids2) = ppDMatchClauseLst(clauses,vars'',false,bound_ids)
            val (term',vars'''',fids3) =  
                   (case term of
                       NONE => (NONE,vars''',MS.empty_set)
                    | SOME(dt_exp) => let val (dt_exp',vars'''',fids3) = ppExp(dt_exp,vars''',bound_ids)
                                      in
                                         (SOME(dt_exp'),vars'''',fids3)
                                      end)
            val res_ded = A.structureCasesDed({prop=prop',clauses=clauses',term=term',pos=pos})
            val _ = A.checkStructureCasesSyntax(res_ded)
        in
           (res_ded,vars'''',MS.unionLst([fids1,fids2,fids3]))
        end
  | ppDed(A.tryDed({choices,pos}),vars,bound_ids) = 
        let val (choices',vars',fids) = ppDedLst(choices,vars,bound_ids)
        in
           (A.tryDed({choices=choices',pos=pos}),vars',fids)
        end
  | ppDed(A.letDed({bindings,body,pos}),vars,bound_ids) = 
       let val (bpat_lst,nameset_lst,defs,pos_lst) = A.splitBindings(bindings)
           val pat_ids = S.unionLst(nameset_lst)
           val (bindings',vars',fids) = ppBindingLst(bpat_lst,defs,pos_lst,vars,bound_ids)
           val (body',vars'',body_fids) = ppDed(body,vars',Symbol.union(bound_ids,pat_ids))
       in
          (A.letDed({bindings=bindings',body=body',pos=pos}),vars'',
           MS.union(fids,MS.difference(body_fids,msyms(pat_ids))))
       end
  | ppDed(A.letRecDed({bindings,body,pos}),vars,bound_ids) = 
       let val (bpat_lst,nameset_lst,defs,pos_lst) = A.splitBindings(bindings)
           val (bindings',vars',fids) = ppLetRecBindingLst(bpat_lst,nameset_lst,defs,pos_lst,vars,bound_ids)
           val rec_syms = S.unionLst(nameset_lst)
           val rec_msyms = msyms(rec_syms)
           val (body',vars'',body_fids) = ppDed(body,vars',Symbol.union(rec_syms,bound_ids))
       in
          (A.letRecDed({bindings=bindings',body=body',pos=pos}),vars'',
           MS.union(fids,MS.difference(body_fids,rec_msyms)))
       end
  | ppDed(A.beginDed({members,pos}),vars,bound_ids) = 
       let val (members',vars',fids) = ppDedLst(members,vars,bound_ids)
       in
          (A.beginDed({members=members',pos=pos}),vars',fids)
       end
  | ppDed(A.checkDed({clauses,pos}),vars,bound_ids) = 
        (A.checkClauses(clauses,pos);
         let val (clauses',vars',fids) = ppDCheckClauseLst(clauses,vars,bound_ids)
         in
           (A.checkDed({clauses=clauses',pos=pos}),vars',fids)
         end)
  | ppDed(A.byDed({wanted_res,body,pos,conc_name=NONE}),vars,bound_ids) = 
        let val (wanted_res',vars',fids1) = ppExp(wanted_res,vars,bound_ids)
            val (body',vars'',fids2) = ppDed(body,vars',bound_ids)
        in
           (A.byDed({wanted_res=wanted_res',body=body',conc_name=NONE,pos=pos}),vars'',
            MS.union(fids1,fids2))  
        end
  | ppDed(A.byDed({wanted_res,body,pos,conc_name=SOME(cp as {name=cname,pos=cname_pos})}),vars,bound_ids) = 
        let val (wanted_res',vars',fids1) = ppExp(wanted_res,vars,bound_ids)
            val (body',vars'',fids2) = ppDed(body,vars',bound_ids)
        in
           (A.byDed({wanted_res=wanted_res',body=body',pos=pos,conc_name=SOME cp}),vars'',
            MS.union(fids1,MS.difference(fids2,MS.singleton(msym cname))))
        end
  | ppDed(A.fromDed({conclusion,premises,pos}),vars,bound_ids) = 
        let val (conclusion',vars',fids1) = ppExp(conclusion,vars,bound_ids)
            val (premises',vars'',fids2) = ppExp(premises,vars',bound_ids)
        in
           (A.fromDed({conclusion=conclusion',premises=premises',pos=pos}),vars'',
	    MS.union(fids1,fids2))
	end
  | ppDed(A.genOverDed({eigenvar_exp,body,pos}),vars,bound_ids) = 
        let val (eigenvar_exp',vars',fids1) = ppExp(eigenvar_exp,vars,bound_ids)
            val (body',vars'',fids2) = ppDed(body,vars',bound_ids)
        in
           (A.genOverDed({eigenvar_exp=eigenvar_exp',body=body',pos=pos}),vars'',MS.union(fids1,fids2))
        end
  | ppDed(A.pickAnyDed({eigenvars,body,pos}),vars,bound_ids) = 
        let fun doEigenVar(ptp:AbstractSyntax.possibly_typed_param) = doPossiblyTypedParam(ptp,vars,bound_ids)
            fun loop([],names,new_eigenvars,sort_vars,sort_fids) = (names,rev(new_eigenvars),sort_vars,sort_fids)
              | loop(ev::more,names,new_eigenvars,sort_vars,sort_fids) = 
                       let val (name,ev',sort_vars',sort_fids') = doEigenVar(ev) 
                       in
                           loop(more,name::names,ev'::new_eigenvars,ATV.union(sort_vars',sort_vars),
                                                                    MS.union(sort_fids,sort_fids'))
                       end
	    val (names,new_eigenvars,sort_vars,sort_fids) = loop(eigenvars,[],[],vars,MS.empty_set)
	    val name_set = S.symListToSet(names)
            val (body',vars',body_fids) = ppDed(body,vars,Symbol.union(name_set,bound_ids))
	    val res = (A.pickAnyDed({eigenvars=new_eigenvars,body=body',pos=pos}),ATV.union(sort_vars,vars'),
 	               MS.union(sort_fids,MS.difference(body_fids,msyms(name_set))))	
        in
    	   res
        end
  | ppDed(A.withWitnessDed({eigenvar_exp,ex_gen,body,pos}),vars,bound_ids) = 
        let val (eigenvar_exp',vars',fids1) = ppExp(eigenvar_exp,vars,bound_ids)
            val (ex_gen',vars'',fids2) = ppPhrase(ex_gen,vars',bound_ids)
            val (body',vars''',fids3) = ppDed(body,vars'',bound_ids)
        in
           (A.withWitnessDed({eigenvar_exp=eigenvar_exp',ex_gen=ex_gen',body=body',pos=pos}),vars''',
            MS.union(fids1,MS.union(fids2,fids3)))
        end
  | ppDed(A.pickWitnessDed({ex_gen,var_id,inst_id=SOME(ii),body,pos}),vars,bound_ids) = 
        let val (ex_gen',vars',fids1) = ppPhrase(ex_gen,vars,bound_ids)
	    val name_set = S.symListToSet([var_id,ii])
            val (body',vars'',fids2) = ppDed(body,vars',Symbol.union(name_set,bound_ids))
        in
           (A.pickWitnessDed({ex_gen=ex_gen',var_id=var_id,inst_id=SOME(ii),body=body',pos=pos}),vars'',
            MS.union(fids1,MS.difference(fids2,msyms(name_set))))
        end
  | ppDed(A.pickWitnessesDed({ex_gen,var_ids,inst_id=SOME(ii),body,pos}),vars,bound_ids) = 
        let val (ex_gen',vars',fids1) = ppPhrase(ex_gen,vars,bound_ids)
            val name_set = S.symListToSet([ii]@var_ids)
            val (body',vars'',fids2) = ppDed(body,vars',Symbol.union(name_set,bound_ids))
        in
           (A.pickWitnessesDed({ex_gen=ex_gen',var_ids=var_ids,inst_id=SOME(ii),body=body',pos=pos}),vars'',
            MS.union(fids1,MS.difference(fids2,msyms(name_set))))
        end
  | ppDed(A.pickWitnessDed({ex_gen,var_id,inst_id=NONE,body,pos}),vars,bound_ids) = 
        let val (ex_gen',vars',fids1) = ppPhrase(ex_gen,vars,bound_ids)
            val name_set = S.symListToSet([var_id])
            val (body',vars'',fids2) = ppDed(body,vars',Symbol.union(name_set,bound_ids))
        in
           (A.pickWitnessDed({ex_gen=ex_gen',var_id=var_id,inst_id=NONE,body=body',pos=pos}),vars'',
            MS.union(fids1,MS.difference(fids2,msyms(name_set))))
        end
  | ppDed(A.pickWitnessesDed({ex_gen,var_ids,inst_id=NONE,body,pos}),vars,bound_ids) = 
        let val (ex_gen',vars',fids1) = ppPhrase(ex_gen,vars,bound_ids)
	    val name_set = S.symListToSet(var_ids)
            val (body',vars'',fids2) = ppDed(body,vars',Symbol.union(name_set,bound_ids))
        in
           (A.pickWitnessesDed({ex_gen=ex_gen',var_ids=var_ids,inst_id=NONE,body=body',pos=pos}),vars'',
            MS.union(fids1,MS.difference(fids2,msyms(name_set))))
        end
and
    ppBinding((binding_pat,def,pos),vars,previous_ids,bound_ids) = 
         let val (binding_pat',vars',val_of_ids) = ppPattern(binding_pat,vars,MS.empty_set,true,true,bound_ids)
             val pat_pos = A.posOfPat(binding_pat)
             val binding_pat_2 = binding_pat'
             val (def',vars'',fids) = ppPhrase(def,vars',bound_ids)
             val fids' = MS.union(fids,val_of_ids)
             val new_binding:A.binding = {bpat=binding_pat_2,def=def',pos=pos}
         in
            (new_binding,vars'',MS.difference(fids',previous_ids))
         end
and
  doPossiblyTypedParam({name,pos,sort_as_sym_term,sort_as_fterm,sort_as_exp,op_tag}:AbstractSyntax.possibly_typed_param,vars,bound_ids) = 
		let val fterm_sort_opt = getFTermSortFromSTermSort(sort_as_sym_term,name,pos)
		    val _ = (case fterm_sort_opt of 
                               SOME(fsort) => dbprint("\nHere's the fterm_sort obtained from the eigenvar " ^  (S.name(name)) ^ ": " ^ 
			                              (F.toStringDefault(fsort)) ^ "\n")
                             | _ => if debug() then print("\nNo fterm_sort obtained from this eigenvar " ^  (S.name(name)) ^ "\n") else ())
                    val (sort_vars,sort_fids,sort_as_exp_opt) = 
                                    (case (sort_as_sym_term,fterm_sort_opt) of 
                                        (SOME(sym_term),NONE) => 
                                          ((let val sort_as_athena_exp = A.symTermAppToExp(sym_term) 
                                                val (_,svars,sfids) = ppExp(sort_as_athena_exp,vars,bound_ids)
                                            in
                                               (svars,sfids,SOME(sort_as_athena_exp))
                                            end) handle _ => invalidSort(sym_term,pos))
                                      | _ => let val _ = ()
                                             in
                                                (ATV.empty,MS.empty_set,NONE)
                                             end
                                    )
	            val ev:AbstractSyntax.possibly_typed_param =  
			  {name=name,pos=pos,sort_as_sym_term=sort_as_sym_term,op_tag=op_tag,
                           sort_as_fterm=fterm_sort_opt,sort_as_exp=sort_as_exp_opt}
                in
                   (name,ev,sort_vars,sort_fids)
                end
and
    ppBindingLstAux([],[],[],bindings,vars,fids,previous_ids,bound_ids) = (rev(bindings),vars,fids)
  | ppBindingLstAux(binding_pat::more_bpats,def::more_defs,pos::more_pos,bindings,vars,fids,previous_ids,bound_ids) = 
          let val (new_binding,vars',new_fids) = ppBinding((binding_pat,def,pos),vars,previous_ids,bound_ids)
	      val new_pat_ids = A.patBindableIds(binding_pat)
          in
             ppBindingLstAux(more_bpats,
                             more_defs,
                             more_pos,
                             new_binding::bindings,
                             vars',
                             MS.union(fids,new_fids),
                             MS.union(msyms(new_pat_ids),previous_ids),
                             Symbol.union(new_pat_ids,bound_ids))
          end
  | ppBindingLstAux(_) = raise Basic.Never
and
    ppBindingLst(bpats,defs,pos_lst,vars,bound_ids) = 
         ppBindingLstAux(bpats,defs,pos_lst,[],vars,MS.empty_set,MS.empty_set,bound_ids)
and 
    ppLetRecBindingLst(bpats,nameset_lst,defs,pos_lst,vars,bound_ids) = 
        redoBindings(ppBindingLstAux(bpats,defs,pos_lst,[],vars,MS.empty_set,msyms(S.unionLst(nameset_lst)),bound_ids))
and
   redoBindings(x as (bindings,vars,fids)) =
        let fun getNameAndArity(p:A.binding as {bpat,def,pos}) = 
                  (case (bpat,def) of 
                      (pat as A.idPat({name,pos,sort_as_sym_term,sort_as_fterm,sort_as_exp,op_tag}),A.exp(A.functionExp({params,...}))) => 
                             (case op_tag of
                                 SOME(_) => {bpat=pat,def=def,pos=pos}
                               | _ => {bpat=A.idPat({name=name,pos=pos,sort_as_sym_term=sort_as_sym_term,
                                                    sort_as_fterm=sort_as_fterm,sort_as_exp=sort_as_exp,op_tag=SOME(List.length params,~1)}),def=def,pos=pos})
                    | _ => p)
             val names_and_arities = map getNameAndArity bindings
        in
          (map getNameAndArity bindings,vars,fids)
        end                  
and
    ppCaseClause({case_name=SOME(parameter as {name,...}),alt,proof}:A.case_clause,vars,bound_ids) = 
      let val (alt',vars',fids') = ppExp(alt,vars,bound_ids)
          val (proof',vars'',fids'') = ppDed(proof,vars',bound_ids)
      in
       ({case_name=SOME(parameter),alt=alt',proof=proof'},vars'',
         MS.union(fids',MS.difference(fids'',msyms(S.symListToSet([name])))))
      end
  | ppCaseClause({case_name=NONE,alt,proof}:A.case_clause,vars,bound_ids) = 
      let val (alt',vars',fids') = ppExp(alt,vars,bound_ids)
          val (proof',vars'',fids'') = ppDed(proof,vars',bound_ids)
      in
       ({case_name=NONE,alt=alt',proof=proof'},vars'',MS.union(fids',fids''))
      end
and
    ppCaseClauseLstAux([]:A.case_clause list,vars,fids,cclist,_) = (rev(cclist),vars,fids)
  | ppCaseClauseLstAux(cc::rest,vars,fids,cclist,bound_ids) = 
       let val (cc',vars',fids') = ppCaseClause(cc,vars,bound_ids)
       in
         ppCaseClauseLstAux(rest,vars',MS.union(fids,fids'),cc'::cclist,bound_ids)
       end
and
   ppCaseClauseLst(x,y,bound_ids) = ppCaseClauseLstAux(x,y,MS.empty_set,[],bound_ids) 
and
    ppMatchClause({pat,exp}:A.match_clause,vars,bound_ids) = 
          let val (pat',vars',val_of_ids) = ppPattern(pat,vars,MS.empty_set,true,false,bound_ids)
	      val pat_ids = A.patBindableIds(pat')
              val (exp',vars'',fids) = ppExp(exp,vars',S.union(pat_ids,bound_ids))
              val new_clause:A.match_clause = {pat=pat',exp=exp'}

          in
             (new_clause,vars'',MS.union(val_of_ids,MS.difference(fids,msyms(pat_ids))))
          end
and
    ppMatchClauseLstAux([],clist,vars,fids,bound_ids) = (rev(clist),vars,fids)
  | ppMatchClauseLstAux(c::more,clist,vars,fids,bound_ids) = 
                                                 let val (c',vars',new_fids) = ppMatchClause(c,vars,bound_ids)
                                                 in
                                                    ppMatchClauseLstAux(more,c'::clist,vars',
                                                                        MS.union(new_fids,fids),bound_ids)
                                                 end
and
    ppMatchClauseLst(clauses,vars,bound_ids) = ppMatchClauseLstAux(clauses,[],vars,MS.empty_set,bound_ids)
and
    ppDMatchClause({pat,ded}:A.dmatch_clause,vars,is_match_pat,bound_ids) = 
          let val (pat',vars',val_of_ids) = ppPattern(pat,vars,MS.empty_set,is_match_pat,false,bound_ids)
              val pat_ids = A.patBindableIds(pat')
              val (ded',vars'',fids) = ppDed(ded,vars',S.union(pat_ids,bound_ids))
              val new_clause:A.dmatch_clause = {pat=pat',ded=ded'}
          in
             (new_clause,vars'',MS.union(val_of_ids,MS.difference(fids,msyms(pat_ids))))
          end
and
    ppDMatchClauseLstAux([],clist,vars,fids,_,_) = (rev(clist),vars,fids)
  | ppDMatchClauseLstAux(c::more,clist,vars,fids,is_match_pat,bound_ids) = 
                                                  let val (c',vars',new_fids) = ppDMatchClause(c,vars,is_match_pat,bound_ids)
                                                  in
                                                     ppDMatchClauseLstAux(more,c'::clist,vars',
                                                                          MS.union(new_fids,fids),is_match_pat,bound_ids)
                                                  end
and
    ppDMatchClauseLst(clauses,vars,is_match_pat,bound_ids) = ppDMatchClauseLstAux(clauses,[],vars,MS.empty_set,is_match_pat,bound_ids)
and
    ppCheckClause({test=A.elseCond,result}:A.check_clause,vars,bound_ids) = 
           let val (result',vars',fids) = ppExp(result,vars,bound_ids)
           in
              ({test=A.elseCond,result=result'}:A.check_clause,vars',fids)
           end
  | ppCheckClause({test=A.boolCond(p),result},vars,bound_ids) = 
           let val (p',vars',fids1) = ppPhrase(p,vars,bound_ids)
               val (result',vars'',fids2) = ppExp(result,vars',bound_ids)
           in
              ({test=A.boolCond(p'),result=result'},vars'',MS.union(fids1,fids2))
           end
and
    ppCheckClauseLstAux([],clist,vars,fids,_) = (rev(clist),vars,fids)
  | ppCheckClauseLstAux(c::more,clist,vars,fids,bound_ids) = 
                                                 let val (c',vars',new_fids) = ppCheckClause(c,vars,bound_ids)
                                                 in
                                                    ppCheckClauseLstAux(more,c'::clist,vars',MS.union(fids,new_fids),bound_ids)
                                                 end
and
    ppCheckClauseLst(clauses,vars,bound_ids) = ppCheckClauseLstAux(clauses,[],vars,MS.empty_set,bound_ids)
and
    ppDCheckClause({test=A.elseCond,result}:A.dcheck_clause,vars,bound_ids) = 
           let val (result',vars',fids) = ppDed(result,vars,bound_ids)
           in
              ({test=A.elseCond,result=result'}:A.dcheck_clause,vars',fids)
           end
  | ppDCheckClause({test=A.boolCond(p),result},vars,bound_ids) = 
           let val (p',vars',fids1) = ppPhrase(p,vars,bound_ids)
               val (result',vars'',fids2) = ppDed(result,vars',bound_ids)
           in
              ({test=A.boolCond(p'),result=result'},vars'',MS.union(fids1,fids2))
           end
and
    ppDCheckClauseLstAux([],clist,vars,fids,_) = (rev(clist),vars,fids)
  | ppDCheckClauseLstAux(c::more,clist,vars,fids,bound_ids) = 
                                                  let val (c',vars',new_fids) = ppDCheckClause(c,vars,bound_ids)
                                                  in
                                                    ppDCheckClauseLstAux(more,c'::clist,vars',MS.union(new_fids,fids),bound_ids)
                                                  end
and
    ppDCheckClauseLst(clauses,vars,bound_ids) = ppDCheckClauseLstAux(clauses,[],vars,MS.empty_set,bound_ids)
and
   decide(is_match_pat) = if is_match_pat then getFTermSortFromSTermSortAux else getFTermSortFromSTermSort 
and 
    ppPattern(p as A.idPat({name,pos,sort_as_sym_term,sort_as_exp,op_tag,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
      if is_let_pat then 
           (case A.getAthNumber(S.name(name)) of 
               SOME(athena_number) => (A.numPat({ath_num=athena_number,pos=pos}),vars,val_of_ids)
              | _ => (case sort_as_sym_term of 
                        NONE => (p,vars,val_of_ids)
                      | SOME(tagged_sort) => let val getFTerm = decide(is_match_pat)
                                                 val fsort_opt = getFTerm(sort_as_sym_term,name,pos)
                                             in
                                                (A.idPat({name=name,pos=pos,sort_as_sym_term=sort_as_sym_term,op_tag=op_tag,
                                                                    sort_as_fterm=fsort_opt,sort_as_exp=NONE}),
		   					  	    vars,val_of_ids)
                                             end))
      else
       let val mname = A.makeMS(Symbol.name(name),SOME(pos))
           val mname' = qualifyFSym(mname)
       in
       (case Data.isTermConstructor(mname') of
           SOME(ar) => (case sort_as_sym_term of 
                           NONE => let val _ = ()
                                   in
                                      (A.funSymPat({name=mname',sort_opt=NONE,sort_as_exp=sort_as_exp,arity=ar,pos=pos}),vars,val_of_ids)
                                   end
                         | SOME(tagged_sort) => 
                             let val getFTerm = decide(is_match_pat)
                                 val fsort_opt = getFTerm(sort_as_sym_term,name,pos)
                                 val sort_as_exp' = (case fsort_opt of 
                                                        SOME(_) => NONE 
                                                      | _ => let val res = A.symTermAppToExp(tagged_sort)
                                                             in
                                                               SOME(res)
                                                             end)
				 val (sort_as_exp_option,_,sort_fids) = 
                                                   (case sort_as_exp' of
                                                        NONE => let 
                                                                in
                                                                   (NONE,[],MS.empty_set)
                                                                end
                                                      | SOME(e) => let 
                                                                       val (sort_as_exp'',_,sort_fids) = ppExp(e,vars,bound_ids)
                                                                   in
                                                                     (SOME(sort_as_exp''),[],sort_fids)
                                                                   end)

				 val fsort_opt' = fsort_opt 
                             in 
                                (A.funSymPat({name=mname',sort_opt=fsort_opt',sort_as_exp=sort_as_exp_option,arity=ar,pos=pos}),vars,MS.union(val_of_ids,sort_fids))
                             end)
         | _ => (case A.isPropConOpt(name) of
                    SOME(pc) => (A.propConPat({pcon=pc,pos=pos}),vars,val_of_ids)
                  | _ => (case A.getAthNumber(S.name(name)) of 
                             SOME(athena_number) => (A.numPat({ath_num=athena_number,pos=pos}),vars,val_of_ids)
                           | _ => (case sort_as_sym_term of 
                                      NONE => (p,vars,val_of_ids)
                                    | SOME(tagged_sort) => 
                                        let val getFTerm = decide(is_match_pat)
                                            val fsort_opt = getFTerm(sort_as_sym_term,name,pos)
                                            val sort_as_exp' = (case fsort_opt of 
                                                                   SOME(_) => NONE 
                                                                 | _ => let val res = A.symTermAppToExp(tagged_sort)
                                                                        in
                                                                           SOME(res)
                                                                        end)
				            val (sort_as_exp_option,_,sort_fids) = 
                                                   (case sort_as_exp' of
                                                        NONE => (NONE,[],MS.empty_set)
                                                      | SOME(e) => let val (sort_as_exp'',_,sort_fids) = ppExp(e,vars,bound_ids)
                                                                   in
                                                                     (SOME(sort_as_exp''),[],sort_fids)
                                                                   end)
                                        in
                                          (A.idPat({name=name,pos=pos,sort_as_sym_term=sort_as_sym_term,op_tag=op_tag,
                                                                sort_as_fterm=fsort_opt,sort_as_exp=sort_as_exp_option}),
							  	vars,MS.union(val_of_ids,sort_fids))
                                        end))))
       end
  | ppPattern(pat as A.valOfPat({id,pos,...}),vars,val_of_ids,_,_,bound_ids) = 
       let val name = #name(id) 
       in  
          (case A.getAthNumber(S.name(name)) of 
              SOME(athena_number) => 
                 (A.valOfPat1({id=id,num=athena_number,pos=pos}),vars,MS.add(msym(name),val_of_ids))
            | _ => (pat,vars,MS.add(msym name,val_of_ids)))
       end
  | ppPattern(pat as A.constantTermVarPat({term_var,pos}),vars,val_of_ids,_,_,bound_ids) = (pat,ATV.add(term_var,vars),val_of_ids)
  | ppPattern(A.listPats({member_pats,pos}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
        let val (new_pats,vars',val_of_ids') = ppPatternLst(member_pats,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
        in
           (A.listPats({member_pats=new_pats,pos=pos}),vars',val_of_ids')
        end
  | ppPattern(A.listPat({head_pat,tail_pat,pos}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
        let val (head_pat',vars',val_of_ids') = ppPattern(head_pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
            val (tail_pat',vars'',val_of_ids'') = ppPattern(tail_pat,vars',val_of_ids',is_match_pat,is_let_pat,bound_ids)
        in
           (A.listPat({head_pat=head_pat',tail_pat=tail_pat',pos=pos}),vars'',val_of_ids'')
        end
  | ppPattern(A.cellPat({pat,pos}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                               let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
                               in 
                                 (A.cellPat({pat=pat',pos=pos}),vars',val_of_ids')
                               end
  | ppPattern(A.reStarPat({pat,pos,re_form,code,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                               let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
                               in 
                                 (A.reStarPat({pat=pat',pos=pos,code=code,re_form=A.patToRegEx(A.reStarPat({pat=pat',pos=pos,code=code,re_form=re_form}))}),vars',val_of_ids')
                               end
  | ppPattern(A.rePlusPat({pat,pos,code,re_form,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                               let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
                               in 
                                 (A.rePlusPat({pat=pat',pos=pos,code=code,re_form=A.patToRegEx(A.rePlusPat({pat=pat',pos=pos,re_form=re_form,code=code}))}),vars',val_of_ids')
                               end

  | ppPattern(A.reRangePat({from_pat,to_pat,lo,hi,pos,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                               let val (from_pat',vars',val_of_ids') = ppPattern(from_pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
                                   val (to_pat',vars'',val_of_ids'') = ppPattern(to_pat,vars,val_of_ids',is_match_pat,is_let_pat,bound_ids)
                               in
                                 (A.reRangePat({from_pat=from_pat',to_pat=to_pat',lo=lo,hi=hi,pos=pos}),vars'',val_of_ids'')
                               end
  | ppPattern(A.reRepPat({pat,times,pos,code,re_form,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                               let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
                               in 
                                 (A.reRepPat({pat=pat',times=times,pos=pos,code=code,re_form=A.patToRegEx(A.reRepPat({pat=pat',times=times,pos=pos,code=code,re_form=re_form}))}),
                                  vars',val_of_ids')
                               end
  | ppPattern(A.reOptPat({pat,pos,code,re_form,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                               let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
                               in 
                                 (A.reOptPat({pat=pat',pos=pos,code=code,re_form=A.patToRegEx(A.reOptPat({pat=pat',pos=pos,re_form=re_form,code=code}))}),vars',val_of_ids')
                               end
  | ppPattern(top_pat as A.splitPat({pats,pos,re_form,code}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
        let val (pats',vars',val_of_ids') = ppPatternLst(pats,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
            val new_split_pat as A.splitPat({pats=pats'',pos=pos'',...}) = A.makeBinarySplitPats(pats',pos,code)
        in
           (A.splitPat({pats=pats'',pos=pos'',code=code,re_form=A.patToRegEx(A.splitPat({pats=pats',pos=pos,code=code,re_form=re_form}))}),vars',val_of_ids')
        end
  | ppPattern(A.namedPat({name,pat,pos}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
       let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) 
       in
          (A.namedPat({name=name,pat=pat',pos=pos}),vars',val_of_ids')
       end
  | ppPattern(A.disjPat({pats,pos}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
        let val (pats',vars',val_of_ids') = ppPatternLst(pats,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
        in
          (A.disjPat({pats=pats',pos=pos}),vars',val_of_ids')
        end
  | ppPattern(given_pat as A.compoundPat({head_pat,rest_pats,pos}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
       let val _ = () 
           val (head_pat',vars',val_of_ids') = ppPattern(head_pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
           val (rest_pats',vars'',val_of_ids'') = ppPatternLst(rest_pats,vars',val_of_ids',is_match_pat,is_let_pat,bound_ids)
       in 
         (case rest_pats' of
             [op_pat as (A.funSymPat({name,sort_opt,arity=2,pos,...})),second_pat] => 
                    (A.compoundPat({head_pat=op_pat,rest_pats=[head_pat',second_pat],pos=pos}),vars'',val_of_ids'')
           | [op_pat as (A.propConPat({pcon=pc,pos=pos})),second_pat] => 
                    (A.compoundPat({head_pat=op_pat,rest_pats=[head_pat',second_pat],pos=pos}),vars'',val_of_ids'')
           | _ => (A.compoundPat({head_pat=head_pat',rest_pats=rest_pats',pos=pos}),vars'',val_of_ids''))
       end

  | ppPattern(A.wherePat({pat,guard,pos,...}),vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
       let val (pat',vars',val_of_ids') = ppPattern(pat,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
           val (guard',vars'',fids) = ppExp(guard,vars',bound_ids)
           val pat_ids = A.patBindableIds(pat')
	   val non_free_syms = Symbol.union(bound_ids,pat_ids)
	   val fids' = MS.difference(fids,msyms(non_free_syms))
       in
          (A.wherePat({pat=pat',guard=guard',pos=pos}),vars'',MS.union(val_of_ids',fids'))
       end
  | ppPattern(p,vars,val_of_ids,_,_,_) = (p,vars,val_of_ids)
and
    ppPatternLstAux([],pats,vars,val_of_ids,_,_,_) = (rev(pats),vars,val_of_ids)
  | ppPatternLstAux(p::more,pats,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = 
                                       let val (p',vars',val_of_ids') = ppPattern(p,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) 
   				           (**   07/16/2016: Defined bounds_ids' as shown below and then threaded bound_ids' instead of bound_ids
                                                 in the recursive call to ppPatternLst1 in the body of this let. This way, the bindable identifiers
						 of the present patterm become bound in subsequent patterns. **)
				           val bound_ids' = S.union(A.patBindableIds(p'),bound_ids)
                                       in
                                          ppPatternLstAux(more,p'::pats,vars',val_of_ids',is_match_pat,is_let_pat,bound_ids')
                                       end
and
    ppPatternLst(pats,vars,val_of_ids,is_match_pat,is_let_pat,bound_ids) = ppPatternLstAux(pats,[],vars,val_of_ids,is_match_pat,is_let_pat,bound_ids)
and
    ppPhrase(A.exp(e),vars,bound_ids) = 
                             let val (e',vars',fids) = ppExp(e,vars,bound_ids) 
                             in
                                (A.exp(e'),vars',fids)
                             end
  | ppPhrase(A.ded(d),vars,bound_ids) = 
                             let val (d',vars',fids) = ppDed(d,vars,bound_ids) 
                             in
                                (A.ded(d'),vars',fids)
                             end
and
    ppExpLstAux([],expressions,vars,fids,bound_ids) = (rev(expressions),vars,fids)
  | ppExpLstAux(e::more,expressions,vars,fids,bound_ids) = 
        let val (e',vars',new_fids) = ppExp(e,vars,bound_ids)
        in
          ppExpLstAux(more,e'::expressions,vars',MS.union(new_fids,fids),bound_ids)
        end
and
    ppDedLstAux([],deductions,vars,fids,bound_ids) = (rev(deductions),vars,fids)
  | ppDedLstAux(d::more,deductions,vars,fids,bound_ids) = 
        let val (d',vars',new_fids) = ppDed(d,vars,bound_ids)
        in
          ppDedLstAux(more,d'::deductions,vars',MS.union(new_fids,fids),bound_ids)
        end
and
    ppPhraseLstAux([],phrases,vars,fids,bound_ids) = (rev(phrases),vars,fids)
  | ppPhraseLstAux(p::more,phrases,vars,fids,bound_ids) = 
                                              let val (p',vars',new_fids) = ppPhrase(p,vars,bound_ids)
                                              in
                                                ppPhraseLstAux(more,p'::phrases,vars',MS.union(new_fids,fids),bound_ids)
                                              end
and
   ppExpLst(exps,vars,bound_ids) = ppExpLstAux(exps,[],vars,MS.empty_set,bound_ids)                                                             
and
   ppPhraseLst(phrases,vars,bound_ids) = ppPhraseLstAux(phrases,[],vars,MS.empty_set,bound_ids)
and
  ppDedLst(deds,vars,bound_ids) = ppDedLstAux(deds,[],vars,MS.empty_set,bound_ids)
in
   (fn (e,mod_path:Symbol.symbol list) => 
            let val _ =  clearSortVarTables()
                val _ = mod_path_cell := mod_path
		val _ = if false then
                           print("\nAbout to preprocess this exp: " ^ (A.unparseExp(e)))
                        else ()
                val res = ppExp(e,ATV.empty,Symbol.empty_set)
	    in 
               res
            end,
    fn (d,mod_path:Symbol.symbol list) => 
            let val _ =  clearSortVarTables() 
                val _ = mod_path_cell := mod_path
	    in ppDed(d,ATV.empty,Symbol.empty_set)
            end,
    fn (p,mod_path:Symbol.symbol list) => 
            let val _ =  clearSortVarTables()
                val _ = mod_path_cell := mod_path
		val _ = if false then
                           print("\nAbout to preprocess this phrase: " ^ (A.unparsePhrase(p)))
                        else ()
                val res = ppPhrase(p,ATV.empty,Symbol.empty_set)
            in 
               res
            end,
    fn (elist,mod_path:Symbol.symbol list) => 
                let val _ =  clearSortVarTables() 
                    val _ = mod_path_cell := mod_path
                in ppExpLst(elist,ATV.empty,Symbol.empty_set) 
                end,
    fn (dlist,mod_path:Symbol.symbol list) => 
                let val _ =  clearSortVarTables()
                val _ = mod_path_cell := mod_path
                in ppDedLst(dlist,ATV.empty,Symbol.empty_set)
                end,
    fn (plist,mod_path:Symbol.symbol list) => 
                let 
		    val _ =  clearSortVarTables() 
                    val _ = mod_path_cell := mod_path
                in ppPhraseLst(plist,ATV.empty,Symbol.empty_set) 
                end,
   fn (some_pat,mod_path:Symbol.symbol list) => 
                  let val _ = clearSortVarTables()
                     val _ = mod_path_cell := mod_path
                  in ppPattern(some_pat,ATV.empty,MS.empty_set,true,false,Symbol.empty_set)
                  end,
   fn (some_pat,mod_path:Symbol.symbol list) => 
                  let val _ = clearSortVarTables()
                      val _ = mod_path_cell := mod_path
                  in ppPattern(some_pat,ATV.empty,MS.empty_set,true,true,Symbol.empty_set)
                  end,
   fn (some_pat_list,mod_path:Symbol.symbol list) => 
                       let val _ = clearSortVarTables() 
                           val _ = mod_path_cell := mod_path
                       in ppPatternLst(some_pat_list,ATV.empty,MS.empty_set,true,false,Symbol.empty_set)
                      end,
   fn (some_pat_list,mod_path:Symbol.symbol list) => 
                       let val _ = clearSortVarTables() 
                           val _ = mod_path_cell := mod_path
                       in ppPatternLst(some_pat_list,ATV.empty,MS.empty_set,true,true,Symbol.empty_set)
                      end)
end

end
