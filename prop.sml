structure Prop: PROP = 

struct

exception SpassTranslation of string
exception PropHashConsEx

type clause = int list
type clauses = clause list
  
structure A = AbstractSyntax

structure S = Symbol

structure MS = ModSymbol

structure N = Names

structure F = FTerm

structure D = Data

structure B = Basic

structure ATV = AthTermVar

structure AT = AthTerm

val (failLst,mark,continue) = (Basic.failLst,Basic.mark,Basic.continue)

type variable = ATV.ath_term_var

type symbol = S.symbol

type msymbol = MS.mod_symbol

type fsymbol = S.symbol

type sort = F.term

type term = AT.term

val _ = RSA.setIncrement(500000)

exception SortError of string

fun sortError(str) = raise SortError(str)

type code_option_ref = int option ref

type prop_flags = code_option_ref * Word8.word 

fun msymEq(s1,s2) = MS.modSymEq(s1,s2)

fun defaultFlags() = let val res:prop_flags = (ref(NONE),0w7) in res end

fun combineFlags((_,w1),(_,w2)) = (ref(NONE),Word8.orb(w1,w2))

fun getFlagWord(_,w) = w

fun getFlagCode(c,_) = c

fun hasFreeVarsW(w) = Word8.andb(w,0w1) = 0w1

fun hasBoundVarsW(w) = Word8.andb(w,0w2) = 0w2

fun isPolyW(w) = Word8.andb(w,0w4) = 0w4

fun involvesPredBasedSortsW(w) = Word8.andb(w,0w8) = 0w8

val zero_word: Word8.word = 0w0 

(**
	Sentence bit flags:

Lowest bit (1): has free vars
Next highest bit (2): has bvars
Next highest bit (4): is poly 
Highest bit (8): involves predicate-based sorts

**)

fun makeWord({involves_pred_based_sorts=false,poly=false,fvars=false,bvars=false}) = zero_word
  | makeWord({involves_pred_based_sorts=true,poly=false,fvars=false,bvars=false}) = 0w8

  | makeWord({involves_pred_based_sorts=false,poly=false,bvars=false,fvars=true}) = 0w1
  | makeWord({involves_pred_based_sorts=true, poly=false,bvars=false,fvars=true}) = 0w9

  | makeWord({involves_pred_based_sorts=false,poly=false,bvars=true,fvars=false}) = 0w2
  | makeWord({involves_pred_based_sorts=true, poly=false,bvars=true,fvars=false}) = 0w10

  | makeWord({involves_pred_based_sorts=false,poly=false,bvars=true,fvars=true}) = 0w3
  | makeWord({involves_pred_based_sorts=true, poly=false,bvars=true,fvars=true}) = 0w11

  | makeWord({involves_pred_based_sorts=false,poly=true,bvars=false,fvars=false}) = 0w4
  | makeWord({involves_pred_based_sorts=true, poly=true,bvars=false,fvars=false}) = 0w12

  | makeWord({involves_pred_based_sorts=false,poly=true,bvars=false,fvars=true}) = 0w5
  | makeWord({involves_pred_based_sorts=true, poly=true,bvars=false,fvars=true}) = 0w13

  | makeWord({involves_pred_based_sorts=false,poly=true,bvars=true,fvars=false}) = 0w6
  | makeWord({involves_pred_based_sorts=true, poly=true,bvars=true,fvars=false}) = 0w14

  | makeWord({involves_pred_based_sorts=false,poly=true,bvars=true,fvars=true}) = 0w7
  | makeWord({involves_pred_based_sorts=true, poly=true,bvars=true,fvars=true}) = 0w15

fun printWord(w:Word8.word) = 
  (case w of
      0w0 => "involves-pred-based-sorts: no, poly: no, fvars: no, bvars: no"
    | 0w1 => "involves-pred-based-sorts: no, poly: no, fvars: yes, bvars: no"
    | 0w2 => "involves-pred-based-sorts: no, poly: no, fvars: no, bvars: yes"
    | 0w3 => "involves-pred-based-sorts: no, poly: no, fvars: yes, bvars: yes"
    | 0w4 => "involves-pred-based-sorts:no, poly: yes, fvars: no, bvars: no"
    | 0w5 => "involves-pred-based-sorts:no, poly: yes, fvars: yes, bvars: no"
    | 0w6 => "involves-pred-based-sorts: no, poly: yes, fvars: no, bvars: yes"
    | 0w7 => "involves-pred-based-sorts: no, poly: yes, fvars: yes, bvars: yes"
    | 0w8 => "involves-pred-based-sorts: yes, poly: no, fvars: no, bvars: no"
    | 0w9 => "involves-pred-based-sorts: yes, poly: no, fvars: yes, bvars: no"
    | 0w10 => "involves-pred-based-sorts: yes, poly: no, fvars: no, bvars: yes"
    | 0w11 => "involves-pred-based-sorts: yes, poly: no, fvars: yes, bvars: yes"
    | 0w12 => "involves-pred-based-sorts: yes, poly: yes, fvars: no, bvars: no"
    | 0w13 => "involves-pred-based-sorts: yes, poly: yes, fvars: yes, bvars: no"
    | 0w14 => "involves-pred-based-sorts: yes, poly: yes, fvars: no, bvars: yes"
    | 0w15 => "involves-pred-based-sorts: yes, poly: yes, fvars: yes, bvars: yes"
    | _ => "Invalid word (greater than 15)")

fun printFlags(ref(SOME(i)),w) = print("Code: "^Int.toString(i)^", word: "^(printWord w))
  | printFlags(ref(NONE),w) = print("No code. Word: "^(printWord w))

fun makeFlagsFromWord(w:Word8.word):prop_flags = (ref NONE,w)

val neg_code = Basic.hashInt(10)
val and_code = Basic.hashInt(513)
val or_code = Basic.hashInt(1000)
val if_code = Basic.hashInt(2305)
val iff_code = Basic.hashInt(4305)

abstype prop =  atom of {term:AthTerm.term,flags:prop_flags,hash_code:Word.word}
               | neg of {arg:prop,flags:prop_flags,fvars:variable list,poly_constants: (msymbol * sort) list,hash_code:Word.word}
               | conj of {args:prop list,flags:prop_flags,fvars:variable list,poly_constants: (msymbol * sort) list,hash_code:Word.word}
               | disj of {args:prop list,flags:prop_flags,fvars:variable list,poly_constants: (msymbol * sort) list,hash_code:Word.word}
               | cond of {ant:prop,con:prop,flags:prop_flags,fvars:variable list,poly_constants: (msymbol * sort) list,hash_code:Word.word}
               | biCond of {left:prop,right:prop,flags:prop_flags,fvars:variable list,poly_constants: (msymbol * sort) list,hash_code:Word.word}
               | uGen of {qvar:variable,body:prop,flags:prop_flags,fvars:variable list}
               | eGen of {qvar:variable,body:prop,flags:prop_flags,fvars:variable list}
               | eGenUnique of {qvar:variable,body:prop,flags:prop_flags,fvars:variable list}

with

fun fastHash(atom({hash_code,...})) = hash_code
  | fastHash(neg({hash_code,...})) = hash_code
  | fastHash(conj({hash_code,...})) = hash_code
  | fastHash(disj({hash_code,...})) = hash_code
  | fastHash(cond({hash_code,...})) = hash_code
  | fastHash(biCond({hash_code,...})) = hash_code
  | fastHash(_) = neg_code

val (size,sizeLst) = 
  let fun f(atom({term,...}),n) = AT.sizeCumulative(term,n)
        | f(neg({arg,...}),n) = f(arg,n+1)
        | f(conj({args,...}),n) = fLst(args,n+1)
        | f(disj({args,...}),n) = fLst(args,n+1)
        | f(cond({ant,con,...}),n) = f2(ant,con,n+1)
        | f(biCond({left,right,...}),n) = f2(right,left,n+1)
        | f(uGen({body,...}),n) = f(body,n+2)
        | f(eGen({body,...}),n) = f(body,n+2)
        | f(eGenUnique({body,...}),n) = f(body,n+2)
      and fLst([],n) = n
        | fLst(p::more,n) = fLst(more,f(p,n))
      and f2(p1,p2,n) = f(p2,f(p1,n))
  in
     (fn p => f(p,0), fn props => fLst(props,0))
  end

val true_prop = atom({term=AT.true_term,hash_code=AT.fastHash(AT.true_term),flags=(ref NONE,zero_word)})
val false_prop = atom({term=AT.false_term,hash_code=AT.fastHash(AT.false_term),flags=(ref NONE,zero_word)})

fun makeFalseProp() = atom({term=AT.false_term,hash_code=AT.fastHash(AT.false_term),flags=(ref NONE,zero_word)})
fun makeTrueProp() = atom({term=AT.true_term,hash_code=AT.fastHash(AT.true_term),flags=(ref NONE,zero_word)})

fun decomposeConjunctions(p as conj({args,...})) = p::(Basic.flatten (map decomposeConjunctions args))
  | decomposeConjunctions(p) = [p]

fun decomposeConjunctionsStrict(conj({args,...})) = (Basic.flatten (map decomposeConjunctions args))
  | decomposeConjunctionsStrict(p) = [p]

fun getConjuncts(p as conj({args,...})) = (List.foldl op@ [] (map getConjuncts args))
  | getConjuncts(p) = [p]

fun getConjunctsOnly(p as conj({args,...})) = (List.foldl op@ args (map getConjunctsOnly args))
  | getConjunctsOnly(p) = []

fun getConjunctsLst(props) = 
       let fun loop([],res) = res
             | loop(p::more,res) = loop(more,(getConjuncts p)@res)
       in 
         loop(props,[])
       end

fun leaves(atom({term,...})) = AT.leaves(term)
  | leaves(conj({args,...})) = Basic.flatten (List.map leaves args)
  | leaves(disj({args,...})) = Basic.flatten (List.map leaves args)
  | leaves(cond({ant,con,...})) = Basic.flatten (List.map leaves [ant,con])
  | leaves(biCond({left,right,...})) = Basic.flatten (List.map leaves [left,right])
  | leaves(uGen({body,...})) = leaves body
  | leaves(eGen({body,...})) = leaves body
  | leaves(eGenUnique({body,...})) = leaves body

fun propKind(atom(_)) = "Atom" 
  |  propKind(neg(_)) = "Negation"
  |  propKind(conj(_)) = "Conjunction"
  |  propKind(disj(_)) = "Disjunction"
  |  propKind(cond(_)) = "Implication"
  |  propKind(biCond(_)) = "Biconditional"
  |  propKind(uGen(_)) = "Universal quantification"
  |  propKind(eGen(_)) = "Existential quantification"
  |  propKind(eGenUnique(_)) = "Unique-existential quantification"

fun subProps(P as atom(_)) = [P]
  | subProps(P as neg({arg,...})) = P::(subProps arg)
  | subProps(P as conj({args,...})) = P::(foldl op@ [] (map subProps args))
  | subProps(P as disj({args,...})) = P::(foldl op@ [] (map subProps args))
  | subProps(P as cond({ant,con,...})) = P::((subProps ant)@(subProps con))
  | subProps(P as biCond({left,right,...})) = P::((subProps left)@(subProps right))
  | subProps(P as uGen({body,...})) = P::(subProps body)
  | subProps(P as eGen({body,...})) = P::(subProps body)
  | subProps(P as eGenUnique({body,...})) = P::(subProps body)

fun boundVars(uGen({qvar,body,...})) = qvar::(boundVars body)
  | boundVars(eGen({qvar,body,...})) = qvar::(boundVars body)
  | boundVars(eGenUnique({qvar,body,...})) = qvar::(boundVars body)
  | boundVars(conj({args,...})) = (foldl op@ [] (map boundVars args))
  | boundVars(disj({args,...})) = (foldl op@ [] (map boundVars args))
  | boundVars(cond({ant,con,...})) = (boundVars ant)@(boundVars con)
  | boundVars(biCond({left,right,...})) = (boundVars left)@(boundVars right)
  | boundVars(neg({arg,...})) = boundVars arg 
  | boundVars(_) = []

fun freeVars(atom({term,...})) = AT.getVars(term)
  | freeVars(neg({fvars,...})) = fvars
  | freeVars(conj({fvars,...})) = fvars
  | freeVars(disj({fvars,...})) = fvars
  | freeVars(cond({fvars,...})) = fvars
  | freeVars(biCond({fvars,...})) = fvars
  | freeVars(uGen({fvars,...})) = fvars
  | freeVars(eGen({fvars,...})) = fvars
  | freeVars(eGenUnique({fvars,...})) = fvars

fun freeVarsLst(props) = List.foldr op@ [] (map freeVars props)

fun freeVarsSet(p) = ATV.addLst(freeVars(p),ATV.empty)

fun freeVarsSetLst(props) =
  let fun loop([],res) = res
        | loop(p::more,res) = loop(more,ATV.union(freeVarsSet(p),res))
  in
     loop(props,ATV.empty)
  end

fun getPolyConstants(atom({term,...})) = AT.getPolyConstants(term)
  | getPolyConstants(neg({poly_constants,...})) = poly_constants
  | getPolyConstants(conj({poly_constants,...})) = poly_constants
  | getPolyConstants(disj({poly_constants,...})) = poly_constants
  | getPolyConstants(cond({poly_constants,...})) = poly_constants
  | getPolyConstants(biCond({poly_constants,...})) = poly_constants
  | getPolyConstants(uGen({body,...})) = getPolyConstants(body)
  | getPolyConstants(eGen({body,...})) = getPolyConstants(body)
  | getPolyConstants(eGenUnique({body,...})) = getPolyConstants(body)

fun occursFree(v,P) = Basic.isMemberEq(v,freeVars P,ATV.athTermVarEq)

fun occursFreeUpToSubsorting(v,P) = 
     let fun compare(v1,v2) = let val (sort1,sort2)  = (ATV.getSort(v1),ATV.getSort(v2))
                              in
                                ATV.nameEq(v1,v2)
				andalso (F.isSubSortBool(sort1,sort2)
				orelse F.isSubSortBool(sort2,sort1))
                              end
     in 
        Basic.isMemberEq(v,freeVars P,compare)
     end

fun getFlags(atom({flags,...})) = flags
  | getFlags(neg({flags,...})) = flags
  | getFlags(conj({flags,...})) = flags
  | getFlags(disj({flags,...})) = flags
  | getFlags(cond({flags,...})) = flags
  | getFlags(biCond({flags,...})) = flags
  | getFlags(uGen({flags,...})) = flags
  | getFlags(eGen({flags,...})) = flags
  | getFlags(eGenUnique({flags,...})) = flags

fun combinePropFlags(P1,P2) = combineFlags(getFlags(P1),getFlags(P2))

fun combinePropFlagsLst(props) = 
 let val init_flag = (ref NONE,zero_word)
     fun f([],res) = res
       | f(P::more,res) = f(more,combineFlags(getFlags(P),res)) 
 in
   f(props,init_flag)
 end

fun getWord(P) = getFlagWord(getFlags(P))

fun getCode(P) = getFlagCode(getFlags(P))

fun involvesPredBasedSorts(p) = involvesPredBasedSortsW(getWord(p))

fun inheritWordFromProp(P) = (ref(NONE),getWord(P))

fun inheritWordFromFlag(flag) = (ref(NONE),getFlagWord(flag))

fun makeQPropWord(v,body,free_vars) = 
	makeWord({poly=isPolyW(getWord(body)) orelse ATV.isPoly(v),bvars=true,
                  involves_pred_based_sorts=involvesPredBasedSorts(body),
		  fvars=not(null(free_vars))})
						       	
fun setCode(P,i) = let val c = getCode(P)
		   in
		      c := SOME(i)
  		   end

fun hasFreeVars(P) = hasFreeVarsW(getWord(P))

fun hasBoundVars(P) = hasBoundVarsW(getWord(P))

fun isPoly(P) = isPolyW(getWord(P))

val sz = String.size
    
val (not_len,and_len,or_len,if_len,iff_len,all_len,ex_len,ex_unique_len) = 
     (sz N.not_name,sz N.and_name,sz N.or_name,sz N.if_name,sz N.iff_name,
      sz N.forall_name,sz N.exists_name,sz N.exists_unique_name)

fun isZeroHeightTerm(t) = AT.isGeneralConstant(t) orelse AT.isVar(t)

fun isZeroHeightProp(atom({term,...})) = isZeroHeightTerm(term)
  | isZeroHeightProp(_) = false

val (lp,rp,nl,blank,colon) = ("(",")",Basic.new_line," ",":")

fun toPrettyString(start,P,printSortVar) =
let val variable_prefix = Names.variable_prefix
    val variable_prefix_length = String.size(variable_prefix)
    fun loop(s,[P],res,offset) = 
	   let val blanks = s + offset
	       val str = nl^(Basic.spaces blanks)^(pp(blanks,P))
           in 
	      rev(str::res)
           end
     | loop(s,P::rest,res,offset) = 
	    let val blanks = s + offset 
	        val str = nl^(Basic.spaces blanks)^pp(blanks,P)
            in
               loop(s,rest,str::res,offset)
            end
     | loop(_) = []
    and doBinary(s,props as P1::rest,connective_name,connective_len) = 
		let val offset = connective_len + 2
		    val first_str = pp(s+offset,P1)
	            val first_len = String.size(first_str)
		in
		   if length(props) < 3 then
		      let val zero_height = isZeroHeightProp(P1) 
			  fun doRest() = if null(rest) then ""
					 else decide(s+offset,first_len+1,hd rest,zero_height)
		      in                                    
			lp^connective_name^" "^first_str^(doRest())^rp
		      end
		   else
                       lp^connective_name^" "^first_str^
                       (List.foldr op^ "" (loop(s,rest,[],offset)))^rp
		end
     | doBinary(_) = ""
    and printVarSort(s,v) = 
         let val sort = ATV.getSort(v)
         in
            F.toPrettyString(s,sort,printSortVar)
         end
    and doQProp(s,qvar,body,quant_name) = 
		let val qvar_name = ATV.name(qvar)
                    val offset = s + String.size(quant_name) + 3 + String.size(qvar_name) + variable_prefix_length
		    val var_sort_string = if (!Options.print_qvar_sorts) then colon^printVarSort(offset,qvar) else ""
		    val rest = if isZeroHeightProp(body) then
			          blank^pp(offset + (sz var_sort_string),body)
			       else nl^(Basic.spaces(s+2))^pp(s+2,body)
                in 
                  lp^quant_name^blank^variable_prefix^qvar_name^var_sort_string^rest^rp
		end
    and pp(s,atom({term,...})) = AT.toPrettyString(s,term,printSortVar)
      | pp(s,neg({arg,...})) = lp^N.not_name^" "^pp(s+not_len+2,arg)^rp  
      | pp(s,conj({args as P1::rest,...})) = doBinary(s,args,N.and_name,and_len)
      | pp(s,disj({args as P1::rest,...})) = doBinary(s,args,N.or_name,or_len)
      | pp(s,cond({ant,con,...})) = 
		let val offset = if_len + 2
		    val ant_str = pp(s+offset,ant)
		    val ant_len = String.size(ant_str)
		in
		   lp^N.if_name^" "^ant_str^decide(s+offset,ant_len+1,con,isZeroHeightProp ant)^rp
		end
      | pp(s,biCond({left,right,...})) = 
		let val offset = iff_len + 2
		    val left_str = pp(s+offset,left)
		    val left_len = String.size(left_str)
		in
		   lp^N.iff_name^" "^left_str^decide(s+offset,left_len+1,right,isZeroHeightProp left)^rp
		end
      | pp(s,uGen({qvar,body,...})) = doQProp(s,qvar,body,N.forall_name)
      | pp(s,eGen({qvar,body,...})) = doQProp(s,qvar,body,N.exists_name)
      | pp(s,eGenUnique({qvar,body,...})) = doQProp(s,qvar,body,N.exists_unique_name)
      | pp(_) = ""
    and decide(s,offset,P,is_previous_zero_height) = 
	if is_previous_zero_height andalso isZeroHeightProp(P)
	then " "^pp(s+offset,P) else Basic.new_line^(Basic.spaces s)^(pp(s,P))
					      
in
  pp(start,P)
end

fun toPrettyStringDefault(start,P) = toPrettyString(start,P,F.makeVarSortPrinter())

fun toString(P,printSortVar) = toPrettyString(0,P,printSortVar)  

fun toString1(P) = toString(P,F.makeVarSortPrinter())

fun toStringDefault(P) = toString(P,F.makeVarSortPrinter())

fun toStringWithVarSortsAsTheyAre(P) = toString(P,F.varToString)

fun printProp(P) = print(toString1(P))

fun printTerm(t) = print(AT.toPrettyString(0,t,F.varToString))

fun fauxPropToPrettyString(start,pcon_name,args) = 
  let val sortVarPrinter = FTerm.makeVarSortPrinter()
      val str = pcon_name
      val break_up = List.exists (fn P => not(isZeroHeightProp(P))) args 
      fun doArgs(_,[]) = ""
        | doArgs(s,[P]) = toPrettyString(s,P,sortVarPrinter)
        | doArgs(s,P1::P2::more) = (toPrettyString(s,P1,sortVarPrinter))^
				   Basic.new_line^Basic.spaces(s)^(doArgs(s,P2::more))
     and ppArgs(s,args,false) = Basic.printSExpListStr(args,fn P => toString(P,sortVarPrinter))
       | ppArgs(s,args,true) = doArgs(s,args)
  in
    "("^str^" "^ppArgs(start+String.size(str)+2,args,break_up)^")"
  end

fun fauxQuantPropToPrettyString(start,quant_name,qvar,body) = 
	        let val sortVarPrinter = FTerm.makeVarSortPrinter()
		    val qvar_name = ATV.name(qvar)
		    val blank = Basic.blank
                    val offset = start + String.size(quant_name) + 3 + 
				 String.size(qvar_name) + String.size(Names.variable_prefix)
		    fun printVarSort(s,v) = F.toPrettyString(s,ATV.getSort(v),sortVarPrinter)
		    val var_sort_string = printVarSort(offset,qvar)
		    val rest = if isZeroHeightProp(body) then
			          blank^(toPrettyString(offset + (String.size(var_sort_string)),
							     body,sortVarPrinter))
			       else (Basic.new_line)^(Basic.spaces(start+2))^
				    (toPrettyString(start+2,body,sortVarPrinter))
                in 
                  (Basic.lparen)^quant_name^blank^(Names.variable_prefix)^qvar_name^(Basic.colon)^
		  var_sort_string^rest^(Basic.rparen)
		end

fun applySortSub(sub,P) = 
  let fun f(atom({term,hash_code,flags,...})) = 
                                      let val term' = AT.applySortSub(sub,term) 
					  val flags' =  makeFlagsFromWord(makeWord({poly=AT.isPoly(term'), 
                                                                                    involves_pred_based_sorts=AT.involvesPredBasedSorts(term'),
										    bvars=false,
									            fvars=AT.hasVars(term')}))
				      in
					 atom({term=term',flags=flags',hash_code=hash_code})
				      end
       | f(neg({arg,flags,fvars,poly_constants,hash_code})) = 
                                                    let val arg' = g(arg)
                                                        val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars
                                                        val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                                                          (List.map (fn (c,sort) => (c,F.applySub(sub,sort))) poly_constants)
				     in 
					neg({arg=arg',flags=inheritWordFromProp(arg'),fvars=fvars,hash_code=hash_code,poly_constants=poly_constants'})
				     end
       | f(conj({args,flags,fvars,poly_constants,hash_code,...})) = 
                                       let val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars
                                           val poly_constants' = List.filter (fn (_,s) => not(F.isGround(s)))
                                                                             (List.map (fn (c,sort) => (c,F.applySub(sub,sort))) poly_constants)
					   val args' = map g args
                                           val flags' = combinePropFlagsLst(args') 
				       in
				          conj({args=args',fvars=fvars',flags=flags',poly_constants=poly_constants',hash_code=hash_code})
				       end
       | f(disj({args,flags,fvars,poly_constants,hash_code})) = 
                                       let val args' = map g args
                                           val flags' = combinePropFlagsLst(args') 
					   val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars
                                           val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                                             (List.map (fn (c,sort) => (c,F.applySub(sub,sort))) poly_constants)
				       in
				          disj({args=args',fvars=fvars',poly_constants=poly_constants',flags=flags',hash_code=hash_code})
				       end
       | f(cond({ant,con,flags,fvars,poly_constants,hash_code,...})) = 
                                          let val ant' = g ant
					      val con' = g con
					      val flags' = combineFlags(getFlags(ant'),getFlags(con'))
                                              val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                                             (List.map (fn (c,sort) => (c,F.applySub(sub,sort))) poly_constants)
   					      val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars	
					  in
					    cond({ant=ant',con=con',fvars=fvars',poly_constants=poly_constants',flags=flags',hash_code=hash_code})
					  end 
       | f(biCond({left,right,flags,fvars,poly_constants,hash_code})) = 
                                               let val left' = g left
				        	   val right' = g right
					           val flags' = combineFlags(getFlags(left'),getFlags(right'))
   					           val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars	
                                                   val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                                                     (List.map (fn (c,sort) => (c,F.applySub(sub,sort))) poly_constants)
 					       in	
					           biCond({left=left',right=right',fvars=fvars',poly_constants=poly_constants',flags=flags',hash_code=hash_code})
					       end 
       | f(p as uGen({qvar,body,flags,fvars})) = 
		let val qvar' = ATV.applySortSub(sub,qvar)
		    val body' = g body
		    val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars	
		    val w = makeWord({poly=isPoly(body') orelse ATV.isPoly(qvar'),
                                      involves_pred_based_sorts=involvesPredBasedSorts(body'), 
				      bvars=true,fvars=hasFreeVars(p)})
	            val flags' = makeFlagsFromWord(w)
		in
		   uGen({qvar=qvar',body=body',flags=flags',fvars=fvars'})
		end
       | f(p as eGen({qvar,body,flags,fvars})) = 
		let val qvar' = ATV.applySortSub(sub,qvar)
		    val body' = g body
		    val w = makeWord({poly=isPoly(body') orelse ATV.isPoly(qvar'),involves_pred_based_sorts=involvesPredBasedSorts(body'), 
				      bvars=true,fvars=hasFreeVars(p)})
	            val flags' = makeFlagsFromWord(w)
		    val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars	
		in
		   eGen({qvar=qvar',body=body',flags=flags',fvars=fvars'})
		end
       | f(p as eGenUnique({qvar,body,flags,fvars})) = 
		let val qvar' = ATV.applySortSub(sub,qvar)
		    val body' = g body
		    val w = makeWord({poly=isPoly(body') orelse ATV.isPoly(qvar'),involves_pred_based_sorts=involvesPredBasedSorts(body'), 
				      bvars=true,fvars=hasFreeVars(p)})
	            val flags' = makeFlagsFromWord(w)
		    val fvars' = map (fn v => ATV.applySortSub(sub,v)) fvars	
		in
		   eGenUnique({qvar=qvar',body=body',flags=flags',fvars=fvars'})
		end
     and g(p) = if not(isPoly(p)) then p else f(p)
  in 
     if F.isEmptySub(sub) then P else g P
  end 

fun applySortSubLst(sub,props) = map (fn P => applySortSub(sub,P)) props

fun apply(sort_sub,new_fvars,new_poly_constants_and_sorts,P) = 
 let fun f(atom({term=t,flags,hash_code,...})) = 
            let val t' = AT.apply(sort_sub,new_fvars,new_poly_constants_and_sorts,t)
            in
	      atom({term=t',hash_code=AT.fastHash(t'),flags=makeFlagsFromWord(makeWord({involves_pred_based_sorts=AT.involvesPredBasedSorts(t'),
                                                                                        poly=AT.isPoly(t'),bvars=false,fvars=AT.hasVars(t')}))})
	    end
      | f(neg({arg=Q,flags,hash_code,fvars,...})) = 
                                          let val Q' = f(Q)
					  in 
					    neg({arg=Q',hash_code=hash_code,
                                                 flags=inheritWordFromProp(Q'),fvars=freeVars(Q'),poly_constants=getPolyConstants(Q)})
					  end
      | f(P as conj({args,flags,fvars,hash_code,poly_constants,...})) = 
	   if null(fvars) then applySortSub(sort_sub,P) 
	   else let val fvars' = ATV.update(fvars,new_fvars)
                    val poly_constants' = ATV.updatePolyConstants(poly_constants,new_poly_constants_and_sorts)
		    val args' = map f args
		    val flags' = combinePropFlagsLst(args')
	        in 
		   conj({args=args',fvars=fvars',hash_code=hash_code,poly_constants=poly_constants',flags=flags'})
		end
      | f(P as disj({args,flags,fvars,hash_code,poly_constants,...})) = 
	   if null(fvars) then applySortSub(sort_sub,P) 
	   else let val fvars' = ATV.update(fvars,new_fvars)
                    val poly_constants' = ATV.updatePolyConstants(poly_constants,new_poly_constants_and_sorts)
		    val args' = map f args
		    val flags' = combinePropFlagsLst(args')
	        in 
		   disj({args=args',fvars=fvars',hash_code=hash_code,poly_constants=poly_constants',flags=flags'})
		end
      | f(P as cond({ant,con,flags,fvars,hash_code,poly_constants,...})) = 
	   if null(fvars) then applySortSub(sort_sub,P) 
	   else let val fvars' = ATV.update(fvars,new_fvars)
                    val poly_constants' = ATV.updatePolyConstants(poly_constants,new_poly_constants_and_sorts)
		    val (ant',con') = (f ant,f con)
		    val flags' = combinePropFlags(ant',con')
	        in 
		   cond({ant=ant',con=con',fvars=fvars',hash_code=hash_code,poly_constants=poly_constants',flags=flags'})
		end
      | f(P as biCond({left,right,flags,fvars,hash_code,poly_constants,...})) = 
	   if null(fvars) then applySortSub(sort_sub,P) 
	   else let val fvars' = ATV.update(fvars,new_fvars)
                    val poly_constants' = ATV.updatePolyConstants(poly_constants,new_poly_constants_and_sorts)
		    val (left',right') = (f left,f right)
		    val flags' = combinePropFlags(left',right')
	        in 
		   biCond({left=left',right=right',hash_code=hash_code,fvars=fvars',poly_constants=poly_constants',flags=flags'})
		end
      | f(P as uGen({qvar,body,flags,fvars,...})) = 
	    let val qvar' = ATV.applySortSub(sort_sub,qvar)
		val fvars' = ATV.update(fvars,new_fvars)
	        val body' = apply(sort_sub,Basic.insertIntoSortedList(qvar',new_fvars,ATV.compareNames),new_poly_constants_and_sorts,body)
		val w = makeQPropWord(qvar',body',fvars')
	    in
		uGen({qvar=qvar',body=body',flags=makeFlagsFromWord(w),fvars=fvars'})
	    end
      | f(P as eGen({qvar,body,flags,fvars,...})) = 
	    let val qvar' = ATV.applySortSub(sort_sub,qvar)
		val fvars' = ATV.update(fvars,new_fvars)
	        val body' = apply(sort_sub,Basic.insertIntoSortedList(qvar',new_fvars,ATV.compareNames),new_poly_constants_and_sorts,body)
		val w = makeQPropWord(qvar',body',fvars')
	    in
		eGen({qvar=qvar',body=body',flags=makeFlagsFromWord(w),fvars=fvars'})
	    end
      | f(P as eGenUnique({qvar,body,flags,fvars,...})) = 
	    let val qvar' = ATV.applySortSub(sort_sub,qvar)
		val fvars' = ATV.update(fvars,new_fvars)
	        val body' = apply(sort_sub,Basic.insertIntoSortedList(qvar',new_fvars,ATV.compareNames),new_poly_constants_and_sorts,body)
		val w = makeQPropWord(qvar',body',fvars')
	    in
		eGenUnique({qvar=qvar',body=body',flags=makeFlagsFromWord(w),fvars=fvars'})
	    end
 in
    f P
 end

fun applyLst(sort_sub,new_fvars,new_poly_constants_and_sorts,props) = map (fn P => apply(sort_sub,new_fvars,new_poly_constants_and_sorts,P)) props

fun sortVars(p) = 
  let fun loop(atom({term,...}),res) = let val vars = AT.sortVars term
                                       in vars@res
                                       end
        | loop(neg({arg,...}),res) = loop(arg,res)
        | loop(conj({args,...}),res) = loopLst(args,res)
        | loop(disj({args,...}),res) = loopLst(args,res)
        | loop(cond({ant,con,...}),res) = loopLst([ant,con],res)
        | loop(biCond({left,right,...}),res) = loopLst([left,right],res)
        | loop(uGen({qvar,body,...}),res) = loop(body,(F.getVars (ATV.getSort qvar))@res)
        | loop(eGen({qvar,body,...}),res) = loop(body,(F.getVars (ATV.getSort qvar))@res)
        | loop(eGenUnique({qvar,body,...}),res) = loop(body,(F.getVars (ATV.getSort qvar))@res)
      and loopLst([],res) = res
        | loopLst(p::more,res) = loopLst(more,loop(p,res))
  in
     Basic.removeDuplicatesEq(loop(p,[]),F.varEq)
  end


fun makeMonomorphicInstance(p) = 
       let val svars = sortVars(p)
           val sort_sub  = F.makeMonoSortSub(svars)
       in
         applySortSub(sort_sub,p)
       end

fun makeAtom(t) = 
	let val bool_sort = FTerm.sortEq(AT.getSort(t),D.boolean_sort) 
            fun error() = sortError("Attempt to make an atomic sentence from the following "^
             		            "non-Boolean term:\n"^AT.toPrettyString(0,t,F.makeVarSortPrinter()))
        in
          if bool_sort then
	     atom({term=t,hash_code=AT.fastHash(t),flags=makeFlagsFromWord(makeWord({involves_pred_based_sorts=AT.involvesPredBasedSorts(t),
                                                                                     poly=AT.isPoly(t),bvars=false,fvars=AT.hasVars(t)}))})
          else
               (case FTerm.unify(AT.getSort(t),D.boolean_sort) of
                   SOME(sort_sub) => let val t' = AT.applySortSub(sort_sub,t) 
                                     in
                                       atom({term=t',hash_code=AT.fastHash(t'),
                                            flags=makeFlagsFromWord(makeWord({involves_pred_based_sorts=AT.involvesPredBasedSorts(t'),
                                                                              poly=AT.isPoly(t'),bvars=false,fvars=AT.hasVars(t')}))})
                                     end
                 | _ => error())
	end

fun makeAtomOpt(t) = 
	let val bool_sort = FTerm.sortEq(AT.getSort(t),D.boolean_sort) 
        in
          if bool_sort then
	     SOME(atom({term=t,hash_code=AT.fastHash(t),flags=makeFlagsFromWord(makeWord({involves_pred_based_sorts=AT.involvesPredBasedSorts(t),
                                                                                          poly=AT.isPoly(t),bvars=false,fvars=AT.hasVars(t)}))}))
          else
               (case FTerm.unify(AT.getSort(t),D.boolean_sort) of
                   SOME(sort_sub) => let val t' = AT.applySortSub(sort_sub,t) 
                                     in
                                       SOME(atom({term=t',hash_code=AT.fastHash(t'),
                                                  flags=makeFlagsFromWord(makeWord({involves_pred_based_sorts=AT.involvesPredBasedSorts(t'),
                                                                                    poly=AT.isPoly(t'),bvars=false,fvars=AT.hasVars(t')}))}))
                                     end
                 | _ => NONE)
        end

fun makeEquality(t1,t2) = 
      let val equality = AthTerm.makeEquality(t1,t2) 
      in 
         atom({term=equality,hash_code=AT.fastHash(equality),
               flags=makeFlagsFromWord(makeWord({involves_pred_based_sorts=AT.involvesPredBasedSorts(equality),
                                                 poly=AT.isPoly(equality),bvars=false,fvars=AT.hasVars(equality)}))})
      end

fun getRootCode(neg(_)) = ~8
  | getRootCode(conj(_)) = ~7
  | getRootCode(disj(_)) = ~6
  | getRootCode(cond(_)) = ~5
  | getRootCode(biCond(_)) = ~4
  | getRootCode(uGen(_)) = ~3
  | getRootCode(eGen(_)) = ~2
  | getRootCode(eGenUnique(_)) = ~1
  | getRootCode(_) = 0

fun getSubtrees(neg({arg,...})) = [arg]
  | getSubtrees(conj({args,...})) = args
  | getSubtrees(disj({args,...})) = args
  | getSubtrees(cond({ant,con,...})) = [ant,con]
  | getSubtrees(biCond({left,right,...})) = [left,right]
  | getSubtrees(uGen({qvar,body,...})) = let val t = AT.makeVar(qvar)
                                         in
                                            [makeEquality(t,t),body]
                                         end
  | getSubtrees(eGen({qvar,body,...})) = let val t = AT.makeVar(qvar)
                                         in
                                            [makeEquality(t,t),body]
                                         end
  | getSubtrees(eGenUnique({qvar,body,...})) = 
                                         let val t = AT.makeVar(qvar)
                                         in
                                            [makeEquality(t,t),body]
                                         end
  | getSubtrees(_) = []

fun swapEquality(p as atom({term=equality,...})) = 
  (case AthTerm.isApp(equality) of 
     SOME(f,[t1,t2]) => if msymEq(N.mequal_logical_symbol,f) then
                           makeEquality(t2,t1)
                        else p)

fun isEquality(p as atom({term=equality,...})) = 
      (case AthTerm.isApp(equality) of 
         SOME(f,[t1,t2]) => if msymEq(N.mequal_logical_symbol,f) then SOME(t1,t2) else NONE
       | _ => NONE)
  | isEquality(_) = NONE

fun isRefEquality(p as atom({term=equality,...})) = 
  (case AthTerm.isApp(equality) of 
     SOME(f,[t1,t2]) => if msymEq(N.mequal_logical_symbol,f) then
                           AthTerm.termEq(t1,t2)
                        else false)
  | isRefEquality(_) = false

fun makeNegation(P) = 
      let val flags' = inheritWordFromProp P
          val involves_pred_based_sorts = involvesPredBasedSortsW(getFlagWord(flags'))
      in
         neg({arg=P,flags= flags',fvars=freeVars(P),hash_code=Basic.hashTwoWords(neg_code,fastHash(P)),poly_constants=getPolyConstants(P)})
      end

fun makeComplement(neg({arg=P,...})) = P
  | makeComplement(p) = makeNegation(p)

fun showProps(props) = Basic.printLnList(props,fn P => toPrettyString(0,P,F.varToString))
fun showTerms(terms) = Basic.printLnList(terms,fn t => AT.toPrettyString(0,t,F.varToString))
fun showVars([]) = ()
  | showVars(vars::rest) = (List.app (fn v => (print(ATV.toPrettyString(0,v,F.varToString));print("\n"))) vars;
			    if null(rest) then print("\n") else print("\nand\n");
			    showVars(rest))

fun displayProp(P) = 
	(print("\n"^(propKind P)^":\n");print(toPrettyString(0,P,F.varToString));
	print("\n\nIts free variables: ");showVars([freeVars(P)]);
	print("\nIts flags: ");printFlags(getFlags(P));print("\n"))

fun displayPropDetailed(P) =  List.app displayProp (subProps P)

val display = displayProp

fun makeConjunction(props) = 
(let val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(props,freeVars,F.empty_sub)
     val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(props,getPolyConstants,theta)
     val not_empty_theta' = not(F.isEmptySub(theta'))
     val var_change = not_empty_theta' orelse vars_diff
     val poly_constant_change = not_empty_theta' orelse constants_diff
     val fvars' = if var_change orelse poly_constant_change then ATV.applySortSubLst(theta',new_fvars) else new_fvars
     val new_poly_constants_and_their_sorts' =  if poly_constant_change then (List.map (fn (c,sort) => (c,F.applySub(theta',sort))) new_poly_constants_and_their_sorts)
                                                else new_poly_constants_and_their_sorts
     val props' = if  not(var_change) andalso not(poly_constant_change) then props else applyLst(theta',fvars',new_poly_constants_and_their_sorts',props)
     val hc = Basic.hashTwoWords(and_code,Basic.hashWordList(props',fastHash))
     val flags = combinePropFlagsLst(props')
     val involves_preds = involvesPredBasedSortsW(getFlagWord(flags))
 in 
    conj({args=props',flags=flags,fvars=fvars',hash_code=hc,poly_constants=new_poly_constants_and_their_sorts'})
 end)
     handle Basic.FailLst(msgs) => 
		failLst(("Unable to verify that this sentence is well-sorted:\n"^
		         (fauxPropToPrettyString(0,Names.and_name,props)))::msgs)

fun makeDisjunction(props) = 
(let val _ = if (!Options.fundef_mlstyle_option) then
                  print("\nHere are the freeVars of all the disjuncts, before reconciliation: " ^
		        (Basic.printListStr(props,fn p => Basic.printListStr(freeVars(p),ATV.toStringWithSort,", "),", ")) ^ "\n")
             else ()
     val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(props,freeVars,F.empty_sub)
     val _ = if (!Options.fundef_mlstyle_option) then
                  print("\nAnd here they are after reconciliation: " ^
		        (Basic.printListStr(new_fvars,ATV.toStringWithSort,", ")) ^ "\n")
             else ()
     val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(props,getPolyConstants,theta)
     val not_empty_theta' = not(F.isEmptySub(theta'))
     val var_change = not_empty_theta' orelse vars_diff
     val poly_constant_change = not_empty_theta' orelse constants_diff
     val fvars' = if var_change orelse poly_constant_change then ATV.applySortSubLst(theta',new_fvars) else new_fvars  
     val new_poly_constants_and_their_sorts' = if poly_constant_change then (List.map (fn (c,sort) => (c,F.applySub(theta',sort))) new_poly_constants_and_their_sorts)
                                               else new_poly_constants_and_their_sorts
     val props' = if not(var_change) andalso not(poly_constant_change) then props else applyLst(theta',fvars',new_poly_constants_and_their_sorts',props)
     val flags = combinePropFlagsLst(props')
     val hc = Basic.hashTwoWords(or_code,Basic.hashWordList(props',fastHash))
     val involves_preds = involvesPredBasedSortsW(getFlagWord(flags))
 in
    disj({args=props',flags=flags,fvars=fvars',hash_code=hc,poly_constants=new_poly_constants_and_their_sorts'})
 end)
     handle Basic.FailLst(msgs) => 
		failLst(("Unable to verify that this sentence is well-sorted:\n"^
	                (fauxPropToPrettyString(0,Names.or_name,props)))::msgs)

fun makeConditional(a,c) = 
(let val props = [a,c]
     val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(props,freeVars,F.empty_sub)
     val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(props,getPolyConstants,theta)
     val not_empty_theta' = not(F.isEmptySub(theta'))
     val var_change = not_empty_theta' orelse vars_diff
     val poly_constant_change = not_empty_theta' orelse constants_diff
     val fvars' = if var_change orelse poly_constant_change then ATV.applySortSubLst(theta',new_fvars) else new_fvars 
     val new_poly_constants_and_their_sorts' = if poly_constant_change then (List.map (fn (c,sort) => (c,F.applySub(theta',sort))) new_poly_constants_and_their_sorts)
                                               else new_poly_constants_and_their_sorts
     val (a',c') = if var_change orelse poly_constant_change then 
                (apply(theta',fvars',new_poly_constants_and_their_sorts',a),
                 apply(theta',fvars',new_poly_constants_and_their_sorts',c)) else (a,c)
     val flags = combinePropFlags(a',c')
     val hc = Basic.hashTwoWords(if_code,Basic.hashTwoWords(fastHash(a'),fastHash(c')))
     val involves_preds = involvesPredBasedSortsW(getFlagWord(flags))
 in
    cond({ant=a',con=c',flags=flags,fvars=fvars',hash_code=hc,poly_constants=new_poly_constants_and_their_sorts'})
 end)
     handle Basic.FailLst(msgs) => 
		failLst(("Unable to verify that this sentence is well-sorted:\n"^
                        (fauxPropToPrettyString(0,Names.if_name,[a,c])))::msgs)

fun makeBiConditional(l,r) = 
(let val props = [l,r]
     val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(props,freeVars,F.empty_sub)
     val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(props,getPolyConstants,theta)
     val not_empty_theta' = not(F.isEmptySub(theta'))
     val var_change = not_empty_theta' orelse vars_diff
     val poly_constant_change = not_empty_theta' orelse constants_diff
     val fvars' = if var_change orelse poly_constant_change then ATV.applySortSubLst(theta',new_fvars) else new_fvars 
     val new_poly_constants_and_their_sorts' = if poly_constant_change then (List.map (fn (c,sort) => (c,F.applySub(theta',sort))) new_poly_constants_and_their_sorts)
                                               else new_poly_constants_and_their_sorts
     val (l',r') = if var_change orelse poly_constant_change then (apply(theta',fvars',new_poly_constants_and_their_sorts',l),
                                                                   apply(theta',fvars',new_poly_constants_and_their_sorts',r)) else (l,r)
     val hc = Basic.hashTwoWords(iff_code,Basic.hashTwoWords(fastHash(l'),fastHash(r')))
     val flags = combinePropFlags(l',r')
     val involves_preds = involvesPredBasedSortsW(getFlagWord(flags))
 in
    biCond({left=l',right=r',flags=flags,fvars=fvars',hash_code=hc,poly_constants=new_poly_constants_and_their_sorts'})
 end)
     handle Basic.FailLst(msgs) => 
		failLst(("Unable to verify that this sentence is well-sorted:\n"^
                        (fauxPropToPrettyString(0,Names.iff_name,[l,r])))::msgs)

fun getFrontQuantVars(P) = 
 let fun f(uGen({qvar,...}),"u",res) = f(P,"u",qvar::res)
       | f(eGen({qvar,...}),"e",res) = f(P,"e",qvar::res)
       | f(eGenUnique({qvar,...}),"eu",res) = f(P,"eu",qvar::res)
       | f(_,_,res) = res
 in
   (case P of
     uGen(_) => f(P,"u",[])
   | eGen(_) => f(P,"e",[])  
   | eGenUnique(_) => f(P,"eu",[])  
   | _ => [])
 end

fun isAtom(atom({term,...})) = SOME(term)
  | isAtom(_) = NONE

fun isVarAtom(p) = (case isAtom(p) of SOME(_) => true | _ => false)

fun isNeg(neg({arg,...})) = SOME(arg)
  | isNeg(_) = NONE

fun isConj(conj({args,...})) = SOME(args)
  | isConj(_) = NONE

fun isDisj(disj({args,...})) = SOME(args)
  | isDisj(_) = NONE

fun getDisjuncts(p) = 
        let fun f(disj({args,...})) = Basic.flatten(List.map getDisjuncts args)
              | f(p) = [p]
        in 
           f p
        end

fun isCond(cond({ant,con,...})) = SOME(ant,con)
  | isCond(_) = NONE

fun isBiCond(biCond({left,right,...})) = SOME(left,right)
  | isBiCond(_) = NONE

fun isUGen(uGen({qvar,body,...})) = SOME(qvar,body)
  | isUGen(_) = NONE

fun isEGen(eGen({qvar,body,...})) = SOME(qvar,body)
  | isEGen(_) = NONE

fun isEGenUnique(eGenUnique({qvar,body,...})) = SOME(qvar,body)
  | isEGenUnique(_) = NONE

fun isQuant(uGen({qvar,body,...})) = SOME(A.forallCon,qvar,body)
  | isQuant(eGen({qvar,body,...})) = SOME(A.existsCon,qvar,body)
  | isQuant(eGenUnique({qvar,body,...})) = SOME(A.existsUniqueCon,qvar,body)
  | isQuant(_) = NONE

fun isCompound(neg({arg,...})) = SOME(A.notCon,[arg])
  | isCompound(conj({args,...})) = SOME(A.andCon,args)
  | isCompound(disj({args,...})) = SOME(A.orCon,args)
  | isCompound(cond({ant,con,...})) = SOME(A.ifCon,[ant,con])
  | isCompound(biCond({left,right,...})) = SOME(A.iffCon,[left,right])
  | isCompound(uGen({body,...})) = SOME(A.forallCon,[body])
  | isCompound(eGen({body,...})) = SOME(A.existsCon,[body])
  | isCompound(eGenUnique({body,...})) = SOME(A.existsUniqueCon,[body])
  | isCompound(_) = NONE

fun isBoolCompound(neg({arg,...})) = SOME(A.notCon,[arg])
  | isBoolCompound(conj({args,...})) = SOME(A.andCon,args)
  | isBoolCompound(disj({args,...})) = SOME(A.orCon,args)
  | isBoolCompound(cond({ant,con,...})) = SOME(A.ifCon,[ant,con])
  | isBoolCompound(biCond({left,right,...})) = SOME(A.iffCon,[left,right])
  | isBoolCompound(_) = NONE

fun foldConditionals(assumptions,conclusion) = 
  let fun doIfs([]) = conclusion
        | doIfs(p1::rest) = makeConditional(p1,doIfs(rest))
  in
     doIfs(assumptions)
  end

val max_hash_length = ref 110

fun getMaxHashLength() = !max_hash_length

fun setMaxHashLength(i) = max_hash_length := i

fun allAtoms(p) = 
  let fun f(atom({term=t,...}),res) = t::res
        | f(neg({arg=p,...}),res) = f(p,res)
        | f(conj({args=props,...}),res) = fLst(props,res)
        | f(disj({args=props,...}),res) = fLst(props,res)
        | f(cond({ant=P1,con=P2,...}),res) = fLst([P1,P2],res)
        | f(biCond({left=P1,right=P2,...}),res) = fLst([P1,P2],res)
        | f(uGen({body=B,...}),res) = f(B,res)
        | f(eGen({body=B,...}),res) = f(B,res)
        | f(eGenUnique({body=B,...}),res) = f(B,res)
     and fLst([],res) = res
       | fLst(p::more,res) = fLst(more,f(p,res))
  in
    f(p,[])
  end

fun hashProp(P,max) = 
 let val i = ref(0)
     fun f(atom({term=t,...}),seed,n,map) = AthTerm.hash(t,seed,n,max,map)
       | f(neg({arg=P,...}),seed,n,map) = 
		let val res as (hash_code,char_count) = Basic.hashAccum("~",seed,n)
		in
		   if char_count > max then res else f(P,hash_code,char_count,map)
		end
       | f(conj({args=props,...}),seed,n,map) = doList("&",props,seed,n,map)
       | f(disj({args=props,...}),seed,n,map) = doList("|",props,seed,n,map)
       | f(cond({ant=P1,con=P2,...}),seed,n,map) = doBinary("<",P1,P2,seed,n,map)
       | f(biCond({left=P1,right=P2,...}),seed,n,map) = doBinary(">",P1,P2,seed,n,map)
       | f(uGen({qvar=v,body=B,...}),seed,n,map) = 
				     let val _ = i := !i + 1
                                         val var_str = Int.toString(!i)
                                         val map' = ATV.enter(map,v,var_str)
                                         val str = "!A"^var_str^":"
                                         val res as (hash_code,char_count) = Basic.hashAccum(str,seed,n)
                                     in 
                                         if char_count > max then res 
                                         else
                                            f(B,hash_code,char_count,map')
                                     end
       | f(eGen({qvar=v,body=B,...}),seed,n,map) = 
				     let val _ = i := !i + 1
                                         val var_str = Int.toString(!i)
                                         val map' = ATV.enter(map,v,var_str)
                                         val str = "!E"^var_str^":"
                                         val res as (hash_code,char_count) = Basic.hashAccum(str,seed,n)
                                     in 
                                         if char_count > max then res 
                                         else
                                            f(B,hash_code,char_count,map')
                                     end
       | f(eGenUnique({qvar=v,body=B,...}),seed,n,map) = 
					   let val _ = i := !i + 1
                                               val var_str = Int.toString(!i)
                                               val map' = ATV.enter(map,v,var_str)
                                               val str = "!U"^var_str^":"
                                               val res as (hash_code,char_count) = Basic.hashAccum(str,seed,n)
                                           in 
                                               if char_count > max then res 
                                               else
                                                  f(B,hash_code,char_count,map')
                                           end
     and doList(str,props,seed,n,map) = 
          let fun loop([P],seed,n,map) = f(P,seed,n,map)
                | loop(P::more,seed,n,map) = 
	            let val res as (hash_code,char_count) = f(P,seed,n,map)
		    in
		       if char_count > max then res
		       else 
			   loop(more,hash_code,char_count,map)
		    end
                | loop(_) = raise Basic.Never 
              val res as (hash_code,char_count) = Basic.hashAccum(str,seed,n)
          in
             if char_count > max then res
	     else loop(props,hash_code,char_count,map)
	  end
     and doBinary(str,P1,P2,seed,n,map) = 
          let val res as (hash_code,char_count) = Basic.hashAccum(str,seed,n)
          in
             if char_count > max then res 
             else 
                let val res' as (hash_code',char_count') = f(P1,hash_code,char_count,map)
                in
                   if char_count' > max then res' 
                   else
                       f(P2,hash_code',char_count',map)
                end
          end
     val (hash_code,_) = f(P,0w0,0,ATV.empty_mapping)
 in       
    hash_code
 end  

fun hash(P) = hashProp(P,!max_hash_length)

fun replaceFSymsByFsyms(p,fmap) = 
    let fun loop(p as atom({term,flags,hash_code})) = 
                     (case AT.isApp(term) of
                         SOME(root,args) => let val root' = root
                                                val args' = map (fn t => AT.replaceFSymsByFsyms(t,fmap)) args 
                                                fun involvePredBasedSorts(terms) = List.exists AT.involvesPredBasedSorts terms;
                                                 val (_,res_sort,_,has_pred_based_sorts) = Data.getSignature(root')
                                                 val arg_bits = if involvePredBasedSorts(args') orelse has_pred_based_sorts then 0w8 else 0w0
                                                 val hc' = Basic.hashTwoWords(Basic.hashInt(MS.code(root')),Basic.hashWordList(args',AT.fastHash))
                                                 val bits' = Word8.orb(AT.getBits(term),arg_bits)
                                                 val term' = AT.makeInternalAppTerm(root',args',hc',AT.getSort(term),bits',
                                                                                    AT.getPolyConstants(term),AT.getVars(term))
                                            in
                                              atom({term=term',hash_code=AT.fastHash(term'),flags=flags})                                                
                                            end 
                       | _ => p)
          | loop(neg({arg,flags,fvars,poly_constants,hash_code})) = 
                let val arg' = loop(arg)
                    val hc = Basic.hashTwoWords(neg_code,fastHash(arg'))
                in 
                   neg({arg=arg',flags=inheritWordFromProp(arg'),fvars=fvars,poly_constants=poly_constants,hash_code=hc})
                end
          | loop(conj({args,flags,fvars,poly_constants,hash_code})) = 
                let val args' = map loop args
                    val hc = B.hashTwoWords(and_code,B.hashWordList(args',fastHash))
                in 
                   conj({args=args',flags=inheritWordFromFlag(flags),fvars=fvars,poly_constants=poly_constants,hash_code=hc})
                end
          | loop(disj({args,flags,fvars,poly_constants,hash_code})) = 
                let val args' = map loop args
                    val hc = B.hashTwoWords(and_code,B.hashWordList(args',fastHash))
                in 
                   disj({args=args',flags=inheritWordFromFlag(flags),fvars=fvars,poly_constants=poly_constants,hash_code=hc})
                end
          | loop(cond({ant,con,flags,fvars,poly_constants,hash_code})) = 
             let val (ant',con') = (loop ant,loop con)
                 val hc = B.hashTwoWords(if_code,B.hashTwoWords(fastHash(ant'),fastHash(con')))
             in
		cond({ant=ant',con=con',hash_code=hc,flags=inheritWordFromFlag(flags),fvars=fvars,poly_constants=poly_constants})
             end
          | loop(biCond({left,right,flags,fvars,poly_constants,hash_code})) = 
             let val (left',right') = (loop left,loop right)
                 val hc = B.hashTwoWords(iff_code,B.hashTwoWords(fastHash(left'),fastHash(right')))
             in
		biCond({left=left',right=right',hash_code=hc,flags=inheritWordFromFlag(flags),fvars=fvars,poly_constants=poly_constants})
             end
          | loop(uGen({qvar,body,flags,fvars})) = uGen({qvar=qvar,body=loop body,flags=(inheritWordFromFlag flags),fvars=fvars})
          | loop(eGen({qvar,body,flags,fvars})) = eGen({qvar=qvar,body=loop body,flags=(inheritWordFromFlag flags),fvars=fvars})
          | loop(eGenUnique({qvar,body,flags,fvars})) = eGenUnique({qvar=qvar,body=loop body,flags=(inheritWordFromFlag flags),fvars=fvars})
    in
      loop(p)
    end

val (predSymbols,predSymbolsLst) = 
    let fun f(p as atom({term,...})) = (case AT.isApp(term) of
                                           SOME(f,args) => [(f,length(args))])
          | f(neg({arg,...})) = f(arg)
          | f(conj({args,...})) = fLst(args,[])
          | f(disj({args,...})) = fLst(args,[])
          | f(cond({ant,con,...})) = fLst([ant,con],[])
          | f(biCond({left,right,...})) = fLst([left,right],[])
          | f(uGen({body,...})) = f(body)
          | f(eGen({body,...})) = f(body)
          | f(eGenUnique({body,...})) = f(body)
        and fLst([],res) = res
          | fLst(p::more,res) = fLst(more,(f p)@res)
    in
      (f, fn props => fLst(props,[]))
    end

fun funSymbolsCore(p,ht:MS.mod_symbol MS.htable) =
    let fun f(p as atom({term,...})) = AT.termSymbolsFastAux(term,ht)
          | f(neg({arg,...})) = f(arg)
          | f(conj({args,...})) = List.app f args
          | f(disj({args,...})) = List.app f args
          | f(cond({ant,con,...})) = List.app f [ant,con]
          | f(biCond({left,right,...})) = List.app f [left,right]
          | f(uGen({body,...})) = f(body)
          | f(eGen({body,...})) = f(body)
          | f(eGenUnique({body,...})) = f(body)
    in
      f(p) 
    end

fun funSymbols(p) = 
       let val ht: MS.mod_symbol MS.htable = MS.makeHTable() 
           val _ = funSymbolsCore(p,ht)
       in
         MS.listItems(ht)
       end

fun funSymbolsLst(props) = 
       let val ht: MS.mod_symbol MS.htable = MS.makeHTable() 
           val _ = List.app (fn t => funSymbolsCore(t,ht)) props
       in
         MS.listItems(ht)
       end

fun replaceVarByVar(v,v',P) = 
       (* Replaces every free occurrence of v inside P by v' **)
       (* We assume that v and v' have identical sorts. **)
       (* and that v' is fresh, and hence cannot be captured *)
       (* by the replacement. *)  
 let fun g(var_list) = if Basic.findInSorted(v,var_list,ATV.compareNames) then 
                          Basic.removeAndInsertInSortedList(v,v',var_list,ATV.compareNames)
                       else var_list
     fun f(A as atom({term,flags,...})) = let val t = AT.replaceVarByVar(v,v',term)
                                          in atom({term=t,hash_code=AT.fastHash(t),flags=inheritWordFromProp(A)}) end
       | f(neg({arg,flags,fvars,poly_constants,...})) = 
                                     let val arg' = f arg 
                                         val hc = Basic.hashTwoWords(neg_code,fastHash(arg'))
				     in
					neg({arg=arg',hash_code=hc,flags=inheritWordFromProp(arg'),fvars=g fvars,poly_constants=poly_constants})
				     end 
       | f(conj({args,flags,fvars,poly_constants,...})) = 
            let val args' = map f args
                val hc = B.hashTwoWords(and_code,B.hashWordList(args',fastHash))
            in
             conj({args=args',hash_code=hc,flags=inheritWordFromFlag(flags),fvars=g fvars,poly_constants=poly_constants})
            end
       | f(disj({args,flags,fvars,poly_constants,...})) = 
            let val args' = map f args
                val hc = B.hashTwoWords(or_code,B.hashWordList(args',fastHash))
            in
               disj({args=args',hash_code=hc,flags=inheritWordFromFlag(flags),fvars=g fvars,poly_constants=poly_constants})
            end
       | f(cond({ant,con,flags,fvars,poly_constants,...})) = 
             let val (ant',con') = (f ant,f con)
                 val hc = B.hashTwoWords(if_code,B.hashTwoWords(fastHash(ant'),fastHash(con')))
             in
		cond({ant=ant',con=con',hash_code=hc,flags=inheritWordFromFlag(flags),fvars=g fvars,poly_constants=poly_constants})
             end
       | f(biCond({left,right,flags,fvars,poly_constants,...})) = 
             let val (left',right') = (f left,f right)
                 val hc = B.hashTwoWords(if_code,B.hashTwoWords(fastHash(left'),fastHash(right')))
             in
		biCond({left=left',right=right',hash_code=hc,flags=(inheritWordFromFlag flags),fvars=g fvars,poly_constants=poly_constants})
             end
       | f(P as uGen({qvar,body,flags,fvars})) = 
		if ATV.athTermVarEq(qvar,v) then P
	        else uGen({qvar=qvar,body=f body,flags=(inheritWordFromFlag flags),fvars=g fvars})
       | f(P as eGen({qvar,body,flags,fvars})) = 
		if ATV.athTermVarEq(qvar,v) then P
	        else eGen({qvar=qvar,body=f body,flags=(inheritWordFromFlag flags),fvars=g fvars})
       | f(P as eGenUnique({qvar,body,flags,fvars})) = 
		if ATV.athTermVarEq(qvar,v) then P
	        else eGenUnique({qvar=qvar,body=f body,flags=(inheritWordFromFlag flags),fvars=g fvars})
  in
     f P
  end

fun makeQPropAux(quant_name,v,body) = 
	let val body_fvars = freeVars(body)
	in
	  (case Basic.findInList(body_fvars,fn v' => ATV.nameEq(v',v)) of 
	      SOME(v') => ((let val (sort_v,sort_v') = (ATV.getSort(v),ATV.getSort(v')) 
                                val U = F.chooseUnificationProcedureForSorts(sort_v,sort_v') 
  			        val sub = U([sort_v],[sort_v'],~1)
			        val v'' = ATV.applySortSub(sub,v)
			        val body_fvars' = Basic.insertIntoSortedList(v'',
					  	  ATV.applySortSubLst(sub,
						  Basic.removeFromSortedList(v,body_fvars,ATV.compareNames)),
					          ATV.compareNames)
			        val body' = apply(sub,body_fvars',[],body)
			        val new_fvars = Basic.removeFromSortedList(v,freeVars(body'),ATV.compareNames)
			        val new_word = makeQPropWord(v'',body',new_fvars)
			    in 
			      {qvar=v'',body=body',flags=makeFlagsFromWord(new_word),fvars=new_fvars}
			    end)
		         handle Basic.FailLst(msgs) => 
				  failLst(("Unable to verify that this\n"^
				           "sentence is well-sorted:\n\n"^
			   	           (fauxQuantPropToPrettyString(0,quant_name,v,body)))::msgs))
            | _ => let val w = makeWord({poly=isPolyW(getWord(body)) orelse ATV.isPoly(v),bvars=true,
                                         involves_pred_based_sorts=involvesPredBasedSorts(body),
			                 fvars=not(null(body_fvars))})
		   in
		     {qvar=v,body=body,flags=makeFlagsFromWord(w),fvars=body_fvars}
		  end)
	end

val (unsafeReplace,makeQProp) = 
let
in
let fun unsafeReplace0(v,t,P) =
  let val t_sort = AT.getSort(t)
      val v_sort = ATV.getSort(v)
      val sub = AT.makeSub([(v,t)])
      fun f(A as atom({term,flags,hash_code,...})) = 
            let val term' = AT.applySub(sub,term)
		val w = makeWord({poly=AT.isPoly(term'),involves_pred_based_sorts=AT.involvesPredBasedSorts(term'),bvars=false,fvars=AT.hasVars(term')})
	    in
  	 	atom({term=term',hash_code=AT.fastHash(term'),flags=makeFlagsFromWord(w)})
	    end 
         | f(neg({arg,flags,fvars,poly_constants,...})) = 
                                      let val arg' = g arg
                                          val hc = Basic.hashTwoWords(neg_code,fastHash(arg'))
				      in
					neg({arg=arg',flags=inheritWordFromProp(arg'),hash_code=hc,fvars=freeVars(arg'),poly_constants=getPolyConstants(arg')})
				      end
        | f(conj({args,flags,fvars,poly_constants,...})) = 
		let val args' = map g args
		    val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(args',freeVars,F.empty_sub)
                    val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(args',getPolyConstants,theta)
		    val args' = map (fn p => applySortSub(theta',p)) args'
		    val flags' = combinePropFlagsLst(args') 
                    val hc = Basic.hashTwoWords(and_code,Basic.hashWordList(args',fastHash))
		in
		   conj({args=args',flags=flags',hash_code=hc,fvars=new_fvars,poly_constants=new_poly_constants_and_their_sorts})
		end
        | f(disj({args,flags,fvars,poly_constants,...})) = 
		let val args' = map g args
		    val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(args',freeVars,F.empty_sub)
                    val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(args',getPolyConstants,theta)
                    val hc = Basic.hashTwoWords(or_code,Basic.hashWordList(args',fastHash))
		    val flags' = combinePropFlagsLst(args') 
		    val args' = map (fn p => applySortSub(theta',p)) args'
		in
		   disj({args=args',flags=flags',hash_code=hc,fvars=new_fvars,poly_constants=new_poly_constants_and_their_sorts})
		end
        | f(cond({ant,con,flags,fvars,poly_constants,...})) = 
		  let val ant' = g ant
		      val con' = g con
		      val new_cond = makeConditional(ant',con')
                      val props = [ant',con']
		      val ((new_fvars,theta),vars_diff) = ATV.reconcileVars(props,freeVars,F.empty_sub)
                      val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = ATV.reconcilePolyConstants(props,getPolyConstants,theta)
		      val flags' = combinePropFlags(ant',con')
                      val hc = Basic.hashTwoWords(if_code,Basic.hashTwoWords(fastHash(ant'),fastHash(con')))
		      val (ant',con') =  (applySortSub(theta',ant'),applySortSub(theta',con'))
		  in
		       cond({ant=ant',con=con',hash_code=hc,flags=flags',fvars=new_fvars,poly_constants=new_poly_constants_and_their_sorts})
		  end
        | f(biCond({left,right,flags,fvars,poly_constants,...})) = 
		  let val left' = g left
		      val right' = g right
                      val props = [left',right']
		      val ((new_fvars,theta),vars_diff) = 
				ATV.reconcileVars(props,freeVars,F.empty_sub)	
                      val ((new_poly_constants_and_their_sorts,theta'),constants_diff) = 
		             ATV.reconcilePolyConstants(props,getPolyConstants,theta)
		      val flags' = combinePropFlags(left',right')
		      val (left',right') = (applySortSub(theta',left'),applySortSub(theta',right'))
                      val hc = Basic.hashTwoWords(if_code,Basic.hashTwoWords(fastHash(left'),fastHash(right')))                      
		  in
		       biCond({left=left',right=right',hash_code=hc,flags=flags',fvars=new_fvars,poly_constants=new_poly_constants_and_their_sorts})
		  end
	| f(P as uGen({qvar,body,flags,fvars,...})) =
		    if ATV.athTermVarEq(qvar,v) then P
		    else uGen(makeQProp(Names.forall_name,qvar,g body))
	| f(P as eGen({qvar,body,flags,fvars,...})) =
		    if ATV.athTermVarEq(qvar,v) then P
		    else eGen(makeQProp(Names.exists_name,qvar,g body))
	| f(P as eGenUnique({qvar,body,flags,fvars,...})) =
		    if ATV.athTermVarEq(qvar,v) then P
		    else eGenUnique(makeQProp(Names.exists_unique_name,qvar,g body))
      and g P = if not(hasFreeVars(P)) then P else f P
  in
    g P 
  end
and  makeQProp(quant_name,v,body) = 
     let val v_sort = ATV.getSort(v)
     in
       (case FTerm.isVarOpt(v_sort) of
           SOME(sort) =>  makeQPropAux(quant_name,v,body)
         | _ => if F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(v_sort) then 
                    let 
                        val body' = (case Basic.findInList(freeVars(body),fn v' => ATV.nameEq(v',v)) of 
                                        SOME(v') => let val fv = ATV.freshWithSort(v_sort)
                                                        val body' = unsafeReplace0(v',AT.makeVar(fv),body)
                                                        val body'' = unsafeReplace0(fv,AT.makeVar(v),body')
                                                     in  
                                                        body''
                                                     end
                                      | _ => body)
                    in 
                       makeQPropAux(quant_name,v,body')
                    end
                else (makeQPropAux(quant_name,v,body)))
     end
in 
(fn (v,t,P) => unsafeReplace0(v,t,P),
 makeQProp)
end
end

fun makeUGen(vars,body) = 
      let fun f([]) = body
            | f(v::more) = uGen(makeQProp(Names.forall_name,v,f(more)))
      in
        f(vars)
      end

fun close(p) = makeUGen(freeVars p,p)

fun makeEGen(vars,body) = 
      let fun f([]) = body
            | f(v::more) = eGen(makeQProp(Names.exists_name,v,f(more)))
   in
     f(vars)
   end

fun makeEGenUnique(vars,body) = 
      let fun f([]) = body
            | f(v::more) = eGenUnique(makeQProp(Names.exists_unique_name,v,f(more)))
   in
     f(vars) 
   end

fun unsafeReplaceLst([],[],p) = p 
  | unsafeReplaceLst(v::more_vars,t::more_terms,p) = unsafeReplaceLst(more_vars,more_terms,unsafeReplace(v,t,p))
  | unsafeReplaceLst(_,_,p) = p

fun renameQProp(names,P) = 
	let fun loop([],P) = P
	      | loop(name::more,uGen({qvar,body,flags,fvars})) = 
			let val body' = loop(more,body)
			    val new_var = ATV.athTermVarWithSort(name,ATV.getSort(qvar))
			    val body'' = unsafeReplace(qvar,AT.makeVar(new_var),body')
			in
			   makeUGen([new_var],body'')
		 	end
	     | loop(_) = raise Basic.failLst([])
	in
	   loop(names,P)
	end

fun replaceVarByVarLst([],[],P) = P
  | replaceVarByVarLst(v1::more1,v2::more2,P) = 
		replaceVarByVarLst(more1,more2,replaceVarByVar(v1,v2,P))
  | replaceVarByVarLst(_) = Basic.failLst(["replaceVarByVarLst called with lists of non-matching lengths"])

fun alphaRename(P) = 
  let fun f(P as atom(_)) = P
        | f(P as neg({arg,flags,fvars,hash_code,poly_constants,...})) = neg({arg=g arg,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})
        | f(P as conj({args,flags,fvars,hash_code,poly_constants,...})) = conj({args=map g args,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})
        | f(P as disj({args,flags,fvars,hash_code,poly_constants,...})) = disj({args=map g args,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})
        | f(P as cond({ant,con,flags,fvars,hash_code,poly_constants,...})) = cond({ant=g ant,con=g con,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})
        | f(P as biCond({left,right,flags,fvars,hash_code,poly_constants,...})) = 
		 biCond({left=g left,right=g right,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})
        | f(P as uGen({qvar,body,flags,fvars})) = 
		let val v = ATV.freshWithSort(ATV.getSort(qvar))
		    val body' = replaceVarByVar(qvar,v,body)
		in
		   uGen({qvar=v,body=g body',flags=flags,fvars=fvars})
		end
        | f(P as eGen({qvar,body,flags,fvars})) = 
		let val v = ATV.freshWithSort(ATV.getSort(qvar))
		    val body' = replaceVarByVar(qvar,v,body)
		in
		   eGen({qvar=v,body=g body',flags=flags,fvars=fvars})
		end
        | f(P as eGenUnique({qvar,body,flags,fvars})) = 
		let val v = ATV.freshWithSort(ATV.getSort(qvar))
		    val body' = replaceVarByVar(qvar,v,body)
		in
		   eGenUnique({qvar=v,body=g body',flags=flags,fvars=fvars})
		end
     and g(P) = if hasBoundVars(P) then f(P) else P
   in
     f P
   end

fun isBooleanFalse(atom({term,...})) = 
    (case AT.isConstant(term) of
        SOME(name) => msymEq(name,N.mfalse_logical_symbol)
      | _ => false)
  | isBooleanFalse(_) = false

fun isBooleanTrue(atom({term,...})) = 
    (case AT.isConstant(term) of
        SOME(name) => msymEq(name,N.mtrue_logical_symbol)
      | _ => false)
  | isBooleanTrue(_) = false

fun isBooleanConstant(atom({term,...})) = 
    (case AT.isConstant(term) of
        SOME(name) => if msymEq(name,N.mfalse_logical_symbol) then "false"
		      else (if msymEq(name,N.mtrue_logical_symbol) then "true"
			    else "")
      | _ => "")
  | isBooleanConstant(_) = ""

fun replace(v,t,P) = if not(hasFreeVars(P)) then P else 
	  	     let val P' = alphaRename P 
                         val res = unsafeReplace(v,t,P')
		     in
			res
		     end			

fun replaceLst([],[],p) = p 
  | replaceLst(v::more_vars,t::more_terms,p) = replaceLst(more_vars,more_terms,replace(v,t,p))
  | replaceLst(_,_,p) = p

fun litEq(atom({term=term1,flags=flags1,...}),atom({term=term2,flags=flags2,...})) = 
       getFlagWord(flags1)=getFlagWord(flags2) andalso AT.termEq(term1,term2)
  | litEq(neg({arg=arg1,flags=flags1,...}),neg({arg=arg2,flags=flags2,...})) = 
	getFlagWord(flags1)=getFlagWord(flags2) andalso litEq(arg1,arg2)
  | litEq(conj({args=args1,flags=flags1,...}),
	  conj({args=args2,flags=flags2,...})) = 
               getFlagWord(flags1)=getFlagWord(flags2) andalso litEqLst(args1,args2)
  | litEq(disj({args=args1,flags=flags1,...}),
	  disj({args=args2,flags=flags2,...})) = 
               getFlagWord(flags1)=getFlagWord(flags2) andalso litEqLst(args1,args2)
  | litEq(cond({ant=ant1,con=con1,flags=flags1,...}),
	  cond({ant=ant2,con=con2,flags=flags2,...})) = 
            getFlagWord(flags1)=getFlagWord(flags2) andalso litEq(ant1,ant2)
						    andalso litEq(con1,con2)
  | litEq(biCond({left=left1,right=right1,flags=flags1,...}),
	  biCond({left=left2,right=right2,flags=flags2,...})) = 
            getFlagWord(flags1)=getFlagWord(flags2) andalso litEq(left1,left2)
						    andalso litEq(right1,right2)
  | litEq(uGen({qvar=qvar1,body=body1,flags=flags1,...}),
	  uGen({qvar=qvar2,body=body2,flags=flags2,...})) = 
	     getFlagWord(flags1)=getFlagWord(flags2) andalso 
             ATV.athTermVarEq(qvar1,qvar2) andalso litEq(body1,body2)
  | litEq(eGen({qvar=qvar1,body=body1,flags=flags1,...}),
	  eGen({qvar=qvar2,body=body2,flags=flags2,...})) = 
	     getFlagWord(flags1)=getFlagWord(flags2) andalso 
             ATV.athTermVarEq(qvar1,qvar2) andalso litEq(body1,body2)
  | litEq(eGenUnique({qvar=qvar1,body=body1,flags=flags1,...}),
	  eGenUnique({qvar=qvar2,body=body2,flags=flags2,...})) = 
	     getFlagWord(flags1)=getFlagWord(flags2) andalso 
             ATV.athTermVarEq(qvar1,qvar2) andalso litEq(body1,body2)
  | litEq(_) = false
and litEqLst([],[]) = true
  | litEqLst(P1::more1,P2::more2) = litEq(P1,P2) andalso litEqLst(more1,more2)
  | litEqLst(_) = false

val literalEq = litEq

fun alEq(P1,P2) = 
  let val (flags1,flags2) = (getFlags P1,getFlags P2)
      val (word1,word2) = (getFlagWord flags1,getFlagWord flags2)
      val cell = ref([],[])
      fun sortsMatch(sorts1,sorts2) = 
	       (case (F.matchLst(sorts1,sorts2),F.matchLst(sorts2,sorts1)) of
	           (SOME(_),SOME(_)) => true
	         | _ => false)
      fun f(atom({term=term1,...}),atom({term=term2,...}),(sub1:AT.sub,sub2:AT.sub)) = 
	   let val term1' = AT.applySub(sub1,term1)
	       val term2' = AT.applySub(sub2,term2)
           in
	      AT.termEq(term1',term2')
           end
        | f(neg({arg=arg1,flags=flags1,fvars=fvars1,...}),
	    neg({arg=arg2,flags=flags2,fvars=fvars2,...}),subs) = 
             getFlagWord(flags1)=getFlagWord(flags2) andalso f(arg1,arg2,subs)
        | f(conj({args=args1,flags=flags1,fvars=fvars1,...}),
	    conj({args=args2,flags=flags2,fvars=fvars2,...}),subs) = 
               getFlagWord(flags1)=getFlagWord(flags2) andalso fLst(args1,args2,subs)
        | f(disj({args=args1,flags=flags1,fvars=fvars1,...}),
	    disj({args=args2,flags=flags2,fvars=fvars2,...}),subs) = 
               getFlagWord(flags1)=getFlagWord(flags2) andalso fLst(args1,args2,subs)
        | f(cond({ant=ant1,con=con1,flags=flags1,fvars=fvars1,...}),      
	    cond({ant=ant2,con=con2,flags=flags2,fvars=fvars2,...}),subs) = 
		getFlagWord(flags1)=getFlagWord(flags2) andalso f(ant1,ant2,subs) 
							andalso f(con1,con2,subs)
        | f(biCond({left=left1,right=right1,flags=flags1,fvars=fvars1,...}),      
	    biCond({left=left2,right=right2,flags=flags2,fvars=fvars2,...}),subs) = 
	 	getFlagWord(flags1)=getFlagWord(flags2) andalso f(left1,left2,subs) 
							andalso f(right1,right2,subs)
        | f(prop1 as uGen({qvar=qvar1,body=body1,flags=flags1,fvars=fvars1}),
	    prop2 as uGen({qvar=qvar2,body=body2,flags=flags2,fvars=fvars2}),(sub1,sub2)) = 
		let val (var_sort1,var_sort2) = (ATV.getSort(qvar1),ATV.getSort(qvar2))
		    val _ = let val (sorts1,sorts2) = !cell
                                 in
				   cell := (var_sort1::sorts1,var_sort2::sorts2)
				 end
	        in
		        let val z = ATV.freshVarName()
			    val qv1' = ATV.athTermVarWithSort(z,var_sort1)
	                    val qv2' = ATV.athTermVarWithSort(z,var_sort2)

	  		in 
			  getFlagWord(flags1) = getFlagWord(flags2) andalso
			  f(body1,body2,(AT.incSub(sub1,(qvar1,AT.makeVar(qv1'))),AT.incSub(sub2,(qvar2,AT.makeVar(qv2')))))
		        end
	       end
        | f(prop1 as eGen({qvar=qvar1,body=body1,flags=flags1,fvars=fvars1}),
	    prop2 as eGen({qvar=qvar2,body=body2,flags=flags2,fvars=fvars2}),(sub1,sub2)) = 
		let val (var_sort1,var_sort2) = (ATV.getSort(qvar1),ATV.getSort(qvar2))
		    val _ = let val (sorts1,sorts2) = !cell
                                 in
				   cell := (var_sort1::sorts1,var_sort2::sorts2)
				 end
	        in
		        let val z = ATV.freshVarName()
			    val qv1' = ATV.athTermVarWithSort(z,var_sort1)
	                    val qv2' = ATV.athTermVarWithSort(z,var_sort2)
	  		in 
			  getFlagWord(flags1) = getFlagWord(flags2) andalso
			  f(body1,body2,(AT.incSub(sub1,(qvar1,AT.makeVar(qv1'))),AT.incSub(sub2,(qvar2,AT.makeVar(qv2')))))
		        end
	       end
        | f(prop1 as eGenUnique({qvar=qvar1,body=body1,flags=flags1,fvars=fvars1}),
	    prop2 as eGenUnique({qvar=qvar2,body=body2,flags=flags2,fvars=fvars2}),(sub1,sub2)) = 
		let val (var_sort1,var_sort2) = (ATV.getSort(qvar1),ATV.getSort(qvar2))
		    val _ = let val (sorts1,sorts2) = !cell
                                 in
				   cell := (var_sort1::sorts1,var_sort2::sorts2)
				 end
	        in
		    let val z = ATV.freshVarName()
			    val qv1' = ATV.athTermVarWithSort(z,var_sort1)
	                    val qv2' = ATV.athTermVarWithSort(z,var_sort2)
	  		in 
			  getFlagWord(flags1) = getFlagWord(flags2) andalso
			  f(body1,body2,(AT.incSub(sub1,(qvar1,AT.makeVar(qv1'))),AT.incSub(sub2,(qvar2,AT.makeVar(qv2')))))
		        end
	       end
        | f(_) = false
      and fLst(L1,L2,(sub1,sub2)) = let fun loop([],[]) = true
  			  	   | loop(P1::rest1,P2::rest2) = 
				          f(P1,P2,(sub1,sub2)) andalso loop(rest1,rest2)
			          | loop(_) = false
	                    in
			       loop(L1,L2)
		            end
  in
    (if not(word1 = word2) then false
     else (case (!(getFlagCode flags1),!(getFlagCode flags2)) of 
             (SOME(c1),SOME(c2)) => c1 = c2 
           | _ => 
                     (let val esub = AT.empty_sub
                          val res1 = f(P1,P2,(esub,esub))
                   in 
                     (case cell of
     		        ref([],[]) => res1
   	              | ref(sorts1,sorts2) => res1 andalso sortsMatch(sorts1,sorts2))
                    end) handle _ => false))
  end

val alEqMemoized = 
 let fun hashFun(tag1,tag2) = Basic.hashPair(tag1,tag2)
     fun equalityFun((tag1,tag2),(tag1',tag2')) = tag1 = tag1'  andalso tag2 = tag2'
     val mtable: ((int * int),bool) HashTable.hash_table = HashTable.mkTable(hashFun, equalityFun) (8543,PropHashConsEx)
 in
   (fn (p1,p2) => (case (getCode(p1),getCode(p2)) of  
                     (ref(SOME(tag1)),ref(SOME(tag2))) => 
                        (case (HashTable.find mtable (tag1,tag2)) of 
                            SOME(res) => res
                          | NONE => let val res = alEq(p1,p2)
                                        val _ = HashTable.insert mtable ((tag1,tag2),res)
                                    in
                                       res
                                    end) 
                   | _ => alEq(p1,p2)))
 end

(* An alternative implementation of alphabetic equivalence with private caching; not currently used: *)
fun alEqAlternative(P1,P2) = if not(fastHash(P1) = fastHash(P2)) then false else alEqMemoized(P1,P2)

fun translateAthenaProp(p as atom({term,...})) = Sat.atom(S.symbol(AT.toStringDefault(term)))
  | translateAthenaProp(neg({arg,...})) = Sat.neg(translateAthenaProp(arg))
  | translateAthenaProp(conj({args,...})) = Sat.conjLst(List.map translateAthenaProp args)
  | translateAthenaProp(disj({args,...})) = Sat.disjLst(List.map translateAthenaProp args)
  | translateAthenaProp(cond({ant,con,...})) = Sat.cond(translateAthenaProp(ant),translateAthenaProp(con))
  | translateAthenaProp(biCond({left,right,...})) = Sat.equiv(translateAthenaProp(left),translateAthenaProp(right))
  | translateAthenaProp(p) = Sat.atom(S.symbol(toPrettyStringDefault(0,p)))

fun consistent((plits,pcount,res),(nlits,ncount)) = 
      let fun loop([],_) = (res := plits@nlits;true)
            | loop(neg({arg,...})::rest,L) = if Basic.isMemberEq(arg,L,alEq) then false else loop(rest,L)
            | loop(p::rest,L) = let val p' = makeNegation(p)
                                in if Basic.isMemberEq(p',L,alEq) then false else loop(rest,L)
                                end
      in 
           if pcount <= ncount then loop(plits,nlits) else loop(nlits,plits)
      end

fun isMember(atom({term=t,...}),lits) = 
     (case AT.isVarOpt(t) of
         SOME(v) => (case ATV.lookUp(lits,v) of 
                        SOME(_) => true
                      | _ => false))

fun insert(l as atom({term=t,...}),lits) = 
  let
      val res =  if isMember(l, lits) then lits else
                                         (case AT.isVarOpt(t) of
                                          SOME(v) => ATV.enter(lits,v,true))

  in
    res
  end

fun pNegOfq(p,q) = 
     (case p of
        neg({arg,...}) => alEq(arg,q) 
      | _ => false)

fun complements(p,q) = pNegOfq(p,q) orelse pNegOfq(q,p)
               
fun inconsistent(props) = Basic.exists(props,fn p => (Basic.exists(props,fn q => complements(p,q))))

fun literal(atom(_)) = true
  | literal(neg({arg,...})) = (case arg of atom(_) => true | _ => false) 
  | literal(_) = false

fun sat(props,plits,nlits) = 
  let  val counter = ref 0 
       fun getPosLits(lits) = let fun makeProp(v,_) = atom({term=AT.makeVar(v),hash_code=ATV.hash(v),flags=(ref NONE,zero_word)})
                              in 
                                 map makeProp (ATV.listAll lits)
                              end
       fun getNegLits(lits) = let fun makeProp(v,_) = makeNegation(atom({term=AT.makeVar(v),hash_code=ATV.hash(v),flags=(ref NONE,zero_word)}))
                              in 
                                 map makeProp (ATV.listAll lits)
                              end
       fun loop(props,plits,nlits) = 
       let val _ = counter := !counter + 1
(****
           val _ = print("\nIterating on these props: " ^ (Basic.printListStr(props,toString1,"\n"))
                         ^ "\nthese plits: " ^ (Basic.printListStr(getPosLits(plits),toString1,"\n"))
                         ^ "\nand these nlits:\n" ^ (Basic.printListStr(getNegLits(nlits),toString1,"\n")))
****)
       in
            (case props of
                conj({args=[p1,p2],...})::rest => if literal(p2) then loop(p2::p1::rest,plits,nlits) else loop(p1::p2::rest,plits,nlits)

              | disj({args=[p1,p2],...})::rest => loop(p1::rest,plits,nlits)  orelse loop(p2::rest,plits,nlits)
              | cond({ant,con,flags,fvars,hash_code,poly_constants,...})::rest => 
                   loop(neg({arg=ant,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::rest,plits,nlits)
		   orelse loop(con::rest,plits,nlits)
              | biCond({left,right,flags,hash_code,fvars,poly_constants,...})::rest => 
                loop(cond({ant=left,con=right,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::
                     cond({ant=right,con=left,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::rest,plits,nlits)
              | neg({arg=conj({args=[p1,p2],flags,fvars,hash_code,poly_constants,...}),...})::rest => 
                    loop(neg({arg=p1,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::rest,plits,nlits) orelse
                    loop(neg({arg=p2,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::rest,plits,nlits)
              | neg({arg=disj({args=[p1,p2],flags,fvars,hash_code,poly_constants,...}),...})::rest => 
                    if size(p1) <= size(p2) then 
                    loop(neg({arg=p1,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::
		              neg({arg=p2,flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants})::
			      rest,plits,nlits)
                   else  loop(neg({arg=p2,flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants})::
	       	               neg({arg=p1,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::
			       rest,plits,nlits)
              | neg({arg=cond({ant,con,hash_code,flags,fvars,poly_constants,...}),...})::rest => 
                    loop(ant::(neg({arg=con,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants}))::rest,plits,nlits)
              | neg({arg=biCond({left,right,flags,fvars,hash_code,poly_constants,...}),...})::rest => 
                 loop(left::(neg({arg=right,flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants}))::rest,plits,nlits) orelse
                 loop(right::(neg({arg=left,flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants}))::rest,plits,nlits)
              | neg({arg=neg({arg=p,...}),...})::rest => loop(p::rest,plits,nlits)

              | (l as (neg({arg=l',...})))::rest => if isMember(l',plits) then false else loop(rest,plits,(insert(l',nlits)))
              | l::rest => let 
                           in
                              if isMember(l,nlits) then false else loop(rest,insert(l,plits),nlits)
                           end
              | _ => true)
      end 
   in 
      loop(props,plits,nlits)
   end 

fun satSolvableTableau(props) =
   let val cell = ref []
       val res = sat(props,ATV.empty_mapping,ATV.empty_mapping)
   in 
     if res then SOME(res) else NONE
  end

(*****
 Slightly different redefinition of tableu satisfiability for the solver: 

fun sat((conj({args=[p1,p2],...}))::rest,plits,nlits) = sat(p1::p2::rest,plits,nlits)
  | sat((disj({args=[p1,p2],...}))::rest,plits,nlits) = sat(p1::rest,plits,nlits) orelse sat(p2::rest,plits,nlits)
  | sat((cond{ant,con,flags,fvars,hash_code,poly_constants,...})::rest,plits,nlits) = 
         sat(neg({arg=ant,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::rest,plits,nlits)
                                                                           orelse sat(con::rest,plits,nlits)
  | sat((biCond{left,right,flags,fvars,hash_code,poly_constants,...})::rest,plits,nlits) = 
                 sat(cond({ant=left,con=right,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::
                     cond({ant=right,con=left,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::rest,plits,nlits)
  | sat(neg({arg=conj({args=[p1,p2],hash_code,flags,fvars,poly_constants,...}),...})::rest,plits,nlits) = 
           sat(neg({arg=p1,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::rest,plits,nlits) orelse
           sat(neg({arg=p2,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::rest,plits,nlits)
  | sat(neg({arg=disj({args=[p1,p2],flags,fvars,hash_code,poly_constants,...}),...})::rest,plits,nlits) = 
           sat(neg({arg=p1,flags=flags,fvars=fvars,hash_code=hash_code,poly_constants=poly_constants})::neg({arg=p2,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants})::rest,plits,nlits)

  | sat(neg({arg=cond({ant,hash_code,con,flags,fvars,poly_constants,...}),...})::rest,plits,nlits) = 
           sat(ant::(neg({arg=con,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants}))::rest,plits,nlits)
  | sat(neg({arg=biCond({left,right,hash_code,flags,fvars,poly_constants,...}),...})::rest,plits,nlits) = 
           sat(left::(neg({arg=right,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants}))::rest,plits,nlits) orelse
           sat(right::(neg({arg=left,hash_code=hash_code,flags=flags,fvars=fvars,poly_constants=poly_constants}))::rest,plits,nlits)
  | sat(neg({arg=neg({arg=p,...}),...})::rest,plits,nlits) = sat(p::rest,plits,nlits)
  | sat((l as (neg({arg,...})))::rest,plits as (pl,_,_),(nlits,k)) = if Basic.isMemberEq(arg,pl,alEq) then false else sat(rest,plits,(l::nlits,k+1))
  | sat(l::rest,(plits,n,res),nlits as (nl,_)) = if Basic.isMemberEq(makeNegation(l),nl,alEq) then false else sat(rest,(l::plits,n+1,res),nlits)
  | sat(_,(plits,_,res),(nlits,_)) = (res := plits@nlits;true)

fun satSolveTableau(props) =
   let val cell = ref []
       val res = sat(props,([],0,cell),([],0))
   in 
      if res then SOME(!cell) else NONE
   end 

****)

fun satSolveTableauNew(props) =
   let val cell = ref []
       val res = sat(props,ATV.empty_mapping,ATV.empty_mapping)
   in 
     res
  end


fun isSortInstance(P1,P2) = 
  let val (word1,word2) = (getWord P1,getWord P2)
      fun sortsMatch(sorts1,sorts2) = 
	       (case (F.matchLst(sorts1,sorts2),F.matchLst(sorts2,sorts1)) of
	           (SOME(_),SOME(_)) => true
	         | _ => false)
      fun f(atom({term=term1,...}),atom({term=term2,...}),sub,sorts) = 
	   let val term1' = AT.applySub(sub,term1)
	       val term2' = AT.applySub(sub,term2)
           in 
              AT.isSortInstanceAux(term1',term2',sorts)
           end
        | f(neg({arg=arg1,flags=flags1,fvars=fvars1,...}),
	    neg({arg=arg2,flags=flags2,fvars=fvars2,...}),sub,sorts) = 
               f(arg1,arg2,sub,sorts)
        | f(conj({args=args1,flags=flags1,fvars=fvars1,...}),
	    conj({args=args2,flags=flags2,fvars=fvars2,...}),sub,sorts) = 
               fLst(args1,args2,sub,sorts)
        | f(disj({args=args1,flags=flags1,fvars=fvars1,...}),
	    disj({args=args2,flags=flags2,fvars=fvars2,...}),sub,sorts) = 
               fLst(args1,args2,sub,sorts)
        | f(cond({ant=ant1,con=con1,flags=flags1,fvars=fvars1,...}),      
	    cond({ant=ant2,con=con2,flags=flags2,fvars=fvars2,...}),sub,sorts) = 
               fLst([ant1,con1],[ant2,con2],sub,sorts)
        | f(biCond({left=left1,right=right1,flags=flags1,fvars=fvars1,...}),      
	    biCond({left=left2,right=right2,flags=flags2,fvars=fvars2,...}),sub,sorts) = 
               fLst([left1,right1],[left2,right2],sub,sorts)
        | f(prop1 as uGen({qvar=qvar1,body=body1,flags=flags1,fvars=fvars1}),
	    prop2 as uGen({qvar=qvar2,body=body2,flags=flags2,fvars=fvars2}),sub,(sorts1,sorts2)) = 
		let val (var_sort1,var_sort2) = (ATV.getSort(qvar1),ATV.getSort(qvar2))
		    val z = ATV.freshVarName()
		    val qv1' = ATV.athTermVarWithSort(z,var_sort1)
                    val qv2' = ATV.athTermVarWithSort(z,var_sort2)
  		in 
		  f(body1,body2,AT.extendSub(sub,[(qvar1,AT.makeVar(qv1')),(qvar2,AT.makeVar(qv2'))]),(var_sort1::sorts1,var_sort2::sorts2))
	        end
        | f(prop1 as eGen({qvar=qvar1,body=body1,flags=flags1,fvars=fvars1}),
	    prop2 as eGen({qvar=qvar2,body=body2,flags=flags2,fvars=fvars2}),sub,(sorts1,sorts2)) =  
		let val (var_sort1,var_sort2) = (ATV.getSort(qvar1),ATV.getSort(qvar2))
		    val z = ATV.freshVarName()
		    val qv1' = ATV.athTermVarWithSort(z,var_sort1)
                    val qv2' = ATV.athTermVarWithSort(z,var_sort2)
  		in 
		  f(body1,body2,AT.extendSub(sub,[(qvar1,AT.makeVar(qv1')),(qvar2,AT.makeVar(qv2'))]),(var_sort1::sorts1,var_sort2::sorts2))
	        end
        | f(prop1 as eGenUnique({qvar=qvar1,body=body1,flags=flags1,fvars=fvars1}),
	    prop2 as eGenUnique({qvar=qvar2,body=body2,flags=flags2,fvars=fvars2}),sub,(sorts1,sorts2)) = 
		let val (var_sort1,var_sort2) = (ATV.getSort(qvar1),ATV.getSort(qvar2))
		    val z = ATV.freshVarName()
		    val qv1' = ATV.athTermVarWithSort(z,var_sort1)
                    val qv2' = ATV.athTermVarWithSort(z,var_sort2)
  		in 
		  f(body1,body2,AT.extendSub(sub,[(qvar1,AT.makeVar(qv1')),(qvar2,AT.makeVar(qv2'))]),(var_sort1::sorts1,var_sort2::sorts2))
	        end
        | f(_) = (failLst [])
      and fLst(L1,L2,sub,sorts) = let fun loop([],[],sorts) = sorts 
  			  	        | loop(P1::rest1,P2::rest2,sorts) = 
                                             let val sorts' = f(P1,P2,sub,sorts)
                                             in 
				                 loop(rest1,rest2,sorts')
                                             end
			                | loop(_) = (failLst [])
	                          in
			             loop(L1,L2,sorts)
		                  end
  in
     (F.matchLst(f(P1,P2,AT.empty_sub,([],[])))) handle _ => NONE 
  end

fun copyStreams(istream,ostream) = 
      let fun copy() = let val v = TextIO.input(istream)
                       in 
                          if v = "" then () else (TextIO.output(ostream,v);copy())
                       end
  in
    copy()
  end

fun subterms(p) = 
      let  val ht : (AT.term,bool) HashTable.hash_table = HashTable.mkTable(AT.hashTerm,AT.termEq) (1024,PropHashConsEx)
           fun loop(atom({term,...})) = AT.subterms(term,ht)
             | loop(neg({arg,...})) = loop(arg)
             | loop(conj({args,...})) = List.app loop args
             | loop(disj({args,...})) = List.app loop args
             | loop(cond({ant,con,...})) = (loop(ant);loop(con))
             | loop(biCond({left,right,...})) = (loop(left);loop(right))
             | loop(uGen({body,...})) = loop(body)
             | loop(eGen({body,...})) = loop(body)
             | loop(eGenUnique({body,...})) = loop(body)
           val _ = loop(p)
      in
         List.map (fn (t,_) => t) (HashTable.listItemsi ht)
      end

fun applyExtractedSortSub(p:prop,t:term) = 
     (case AT.getSortSubForFirstTerm(subterms(p),t) of
       SOME(sub) => SOME(applySortSub(sub,p))
     | _ => NONE)

type cnf_conversion_result = {clauses: clauses,
                              table: (int,prop) HashTable.hash_table,
                              total_var_num: int,
			      tseitin_var_num: int,
			      clause_num: int,
			      array_n: int,
			      cnf_conversion_time: real}

     
(************************************************************************************

fastSat assumes that each element of props is in CNF already, i.e., it's a conjunction
of disjunctions of literals. However, a literal need not be an Athena variable or
constant. It can be an arbitrary atom (or negation of one).

************************************************************************************)

fun fastSat(props,is_selected) = 
 let fun debugPrint(str) = ()
     val (dimacs_file_name,dimacs_file_name_tmp,output_file_name,error_file_name,other_out_name) =  
         ("dimacs2.txt","dimacs2.tmp","sat_output2.txt","minisat_error2.txt","other_out_mini2.txt")
     fun deleteFiles() = (List.app OS.FileSys.remove [dimacs_file_name,dimacs_file_name_tmp,output_file_name,error_file_name,other_out_name]) handle _ => ()
     val  _ = deleteFiles()
     val (dimacs_stream,dimacs_stream_tmp) = (TextIO.openOut(dimacs_file_name),TextIO.openOut(dimacs_file_name_tmp))
     val sz = 50000
     val clause_count = List.length(props)
     fun teq(t1,t2) = (let val res = AT.termEq(t1,t2)
                           val _ = if not(res) andalso (AT.hashTerm(t1) = AT.hashTerm(t2)) then 
                                      print("\nDifferent terms with the same hash codes: "^(AT.toStringDefault(t1))^"\nand: "^(AT.toStringDefault(t2)))
                                   else ()
                       in res end)
     val ht : (AT.term,int) HashTable.hash_table = HashTable.mkTable(AT.hashTerm,AT.termEq) (sz,PropHashConsEx)
     val ht' : (int,AT.term) HashTable.hash_table = HashTable.mkTable(Basic.hashInt,op =) (sz,PropHashConsEx)
     val answer_ht : (AT.term,bool) HashTable.hash_table = HashTable.mkTable(AT.hashTerm,AT.termEq) (sz,PropHashConsEx)
     val index = ref 0
     fun getTermCode(term) = 
           (case (HashTable.find ht term) of 
              SOME(i) => i
            | _ => let val _ = index := !index + 1
                       val i = !index
                   in
                     (HashTable.insert ht (term,i);
                      HashTable.insert ht' (i,term); 
                      i)
                   end)
     fun getLiteralCodeString(atom({term,...})) = " "^Int.toString(getTermCode(term))
       | getLiteralCodeString(neg({arg=atom({term,...}),...})) = " -"^(Int.toString(getTermCode term))

     fun getLiteralCodeString1(atom({term,...})) = Int.toString(getTermCode(term))
       | getLiteralCodeString1(neg({arg=atom({term,...}),...})) = " -"^(Int.toString(getTermCode term))

     fun writeLiteral(l) = TextIO.output(dimacs_stream_tmp,getLiteralCodeString(l))

     fun processDisjunction(disj({args,...})) = 
           let val _ = List.app writeLiteral args
           in
              TextIO.output(dimacs_stream_tmp," 0\n")
           end
       | processDisjunction(literal as atom(_)) = (writeLiteral(literal);TextIO.output(dimacs_stream_tmp," 0\n"))
       | processDisjunction(literal as neg(_)) = (writeLiteral(literal);TextIO.output(dimacs_stream_tmp," 0\n"))
       | processDisjunction(_) = Basic.fail("\nThe procedure "^N.fastSatFun_name^" can only be used on sentences in CNF.\n")

     fun processDisjunction1(disj({args,...})) = 
           let val str = Basic.printListStr(args,getLiteralCodeString1," ")
           in
              (TextIO.output(dimacs_stream_tmp,str);
               TextIO.output(dimacs_stream_tmp," 0\n"))
           end
       | processDisjunction1(literal as atom(_)) = (writeLiteral(literal);TextIO.output(dimacs_stream_tmp," 0\n"))
       | processDisjunction1(literal as neg(_)) = (writeLiteral(literal);TextIO.output(dimacs_stream_tmp," 0\n"))
       | processDisjunction1(_) = Basic.fail("\nThe procedure "^N.fastSatFun_name^" can only be used on sentences in CNF.\n")

     val _ = debugPrint("\nAbout to write the main dimacs file...\n")
     val t1 = Time.toReal(Time.now())
     val _ = List.app processDisjunction1 props 
     val t2 = Time.toReal(Time.now())
     val _ = debugPrint("\nHashed everything and wrote the file in "^(Real.toString(Real.-(t2,t1)))^" seconds...\n")
     val _ = TextIO.output(dimacs_stream,"p cnf "^(Int.toString(!index))^" "^(Int.toString(clause_count))^"\n")
     val _ = TextIO.closeOut(dimacs_stream_tmp)
     val _ = debugPrint("\nSize of hash table: "^(Int.toString(HashTable.numItems(ht)))^"\n")
     val _ = debugPrint("\nAbout to copy the files...\n")
     val dimacs_stream_tmp_in = TextIO.openIn(dimacs_file_name_tmp)
     val _ = copyStreams(dimacs_stream_tmp_in,dimacs_stream)
     val _ = (TextIO.closeOut(dimacs_stream);TextIO.closeIn(dimacs_stream_tmp_in))
     val cmd = Names.minisat_binary ^ " -verbosity=0 "^dimacs_file_name^" "^output_file_name^" 1> "^other_out_name^" 2> "^error_file_name 
     val _ = debugPrint("\nAbout to call the SAT solver with this command: "^cmd^"\n")
     val _ = OS.Process.system(cmd)
     fun enterAnswer(i_str,b) = 
            (case Int.fromString(i_str) of
               SOME(i) => (case (HashTable.find ht' i) of 
                              SOME(t) => if is_selected(t,b) then
                                            (HashTable.insert answer_ht (t,b))
                                         else ()
                            | _ => ()))
     fun makeOutputTable(big_line) = 
              let val minus_sign = #"-"
                  fun processStingVal(str) = 
                        if String.sub(str,0) = minus_sign then  
                           enterAnswer(String.substring(str,1,String.size(str)-1),false)
                        else
                           enterAnswer(str,true)
                 fun pred(c) = c = #" " orelse c = #"\n"
                 val strings = String.tokens pred big_line
              in
                 List.app processStingVal strings
              end
     fun getAnswer(out_stream) = 
              let val first_line = TextIO.inputLine(out_stream)
              in
                (case (String.tokens (fn c => c = #" " orelse c = #"\n") first_line) of 
                    ("UNSAT"::_) => NONE
                  | _ => let val asgn_line = TextIO.inputLine(out_stream)
                             val _ = makeOutputTable(asgn_line)
                             val answer = HashTable.listItemsi answer_ht
                         in 
                            SOME(answer)
                         end)
              end
      val answer_stream = TextIO.openIn(output_file_name)
      val answer = getAnswer(answer_stream)
      val _ = TextIO.closeIn(answer_stream)
      val _ = debugPrint("\nFinished the SAT problem...\n")
      val _ = debugPrint("\nAbout to list all atoms...\n")
      val all_atoms = map #1 (HashTable.listItemsi ht)
      val _ = debugPrint("\nGot the atoms, about to look up all of them now...\n")
      val t1 = Time.toReal(Time.now())
      val _ = List.map (fn t => (case (HashTable.find ht t) of
                                    SOME(i) => i
                                  | _ => 0)) all_atoms
      val t2 = Time.toReal(Time.now())
      val _ = debugPrint("\nAtoms were looked up in "^(Real.toString(Real.-(t2,t1)))^" seconds...\n")
 in
   answer 
 end

fun propKind(atom(_)) = "an atom"
  | propKind(neg(_)) = "a negation"
  | propKind(conj(_)) = "a conjunction"
  | propKind(disj(_)) = "a disjunction"
  | propKind(cond(_)) = "a conditional"
  | propKind(biCond(_)) = "a biconditional"
  | propKind(uGen(_)) = "a universal generalization"
  | propKind(eGen(_)) = "an existential generalization"
  | propKind(eGenUnique(_)) = "a unique-existential generalization"

fun splitUVars(P) = 
  let fun split(uGen{qvar,body,...},vars) = split(body,qvar::vars)
        | split(P,vars) = (rev vars,P)
  in
     split(P,[])
  end

fun splitEVars(P) = 
  let fun split(eGen{qvar,body,...},vars) = split(body,qvar::vars)
        | split(P,vars) = (rev vars,P)
  in
     split(P,[])
  end

fun splitEUniqueVars(P) = 
  let fun split(eGenUnique{qvar,body,...},vars) = split(body,qvar::vars)
        | split(P,vars) = (rev vars,P)
  in
     split(P,[])
  end

fun splitVars(P as uGen(_)) = 
	let val (vars,body) = splitUVars(P)
	in  
	   (SOME(A.forallCon),vars,body) 
	end
  | splitVars(P as eGen(_)) = 
	let val (vars,body) = splitEVars(P)
	in  
	   (SOME(A.existsCon),vars,body) 
	end
  | splitVars(P as eGenUnique(_)) = 
	let val (vars,body) = splitEUniqueVars(P)
	in  
	   (SOME(A.existsCon),vars,body) 
	end
  |splitVars(P) = (NONE,[],P)


fun toStringInfix(p) = 
  let fun f(atom({term=t,...})) = (AT.toStringDefault t)
	| f(neg({arg=p,...})) = (case isAtom(p) of 
                                   SOME(_) => "~" ^ (f p)
				 | _ =>  "(~ " ^ (f p) ^ ")")
	| f(conj({args,...})) = "(" ^ (Basic.printListStr(args,f," & ")) ^ ")"
	| f(disj({args,...})) = "(" ^ (Basic.printListStr(args,f," | ")) ^ ")"
	| f(cond({ant,con,...})) = "(" ^ (f ant) ^ " ==> " ^ (f con) ^ ")"
	| f(biCond({left,right,...})) = "(" ^ (f left) ^ " <==> " ^ (f right) ^ ")"
        | f(uGen({qvar,body,...})) = "(forall "^ (AthTermVar.toStringDefault qvar) ^ " . " ^ (f body) ^ ")"
        | f(eGen({qvar,body,...})) = "(exists "^ (AthTermVar.toStringDefault qvar) ^ " . " ^ (f body) ^ ")"
        | f(eGenUnique({qvar,body,...})) = "(exists-unique "^ (AthTermVar.toStringDefault qvar) ^ " . " ^ (f body) ^ ")"
  in
     (case p of 
        neg({arg=p,...}) => "(~ " ^ (f p) ^ ")" 
      | _ => (f p))
  end

(***
fun jsonLeaf(p,subtype) = JSON.OBJECT([("type", JSON.STRING("formula")),
	   	 		       ("subtype", JSON.STRING(subtype)),
	  	 		       ("root", JSON.STRING(toStringInfix(p)))
	  	 		       ("children", JSON.ARRAY([]))])
***)

(* fun getRoot(json_value:JSON.value) =  *)
(*     (case (JSONUtil.findField json_value "root") of *)
(* 	SOME(v) => v  *)
(*       | _ => Basic.fail("Could not find root field!")) *)

(* fun getChildren(json_value) =  *)
(*     (case (JSONUtil.findField json_value "children") of *)
(* 	SOME(v) => v *)
(*       | _ => Basic.fail("Could not find children field!")) *)

fun toJson(atom({term,...})) = 
    let val t_json:JSON.value = AT.toJson(term)					 
        val (term_root,children,is_var) = 
                                 (case AT.isApp(term) of 
				      SOME((f,args)) => ((MS.name f), (map AT.toJson args),false)
        			    | _ => (case AT.isVarOpt(term) of 
					      SOME(v) => (AT.toStringDefault(term), [], true)
  				            | _ => (AT.toStringDefault(term), [],false)))
    in
	JSON.OBJECT([("type", JSON.STRING("formula")),
		     ("subtype", JSON.STRING("atom")),
		     ("root", JSON.STRING(term_root)),
		     ("isTermVariable", JSON.BOOL(is_var)),
		     ("children", JSON.ARRAY(children))])
    end 	
  | toJson(neg({arg,...})) = JSON.OBJECT([("type", JSON.STRING("formula")),
					  ("subtype", JSON.STRING("negation")),
					  ("root", JSON.STRING("~")),
					  ("children", JSON.ARRAY([toJson(arg)]))])
  | toJson(conj({args,...})) = JSON.OBJECT([("type", JSON.STRING("formula")),
					    ("subtype", JSON.STRING("conjunction")),
					    ("root", JSON.STRING("&")),
					    ("children", JSON.ARRAY((map toJson args)))])
  | toJson(disj({args,...})) = JSON.OBJECT([("type", JSON.STRING("formula")),
					    ("subtype", JSON.STRING("disjunction")),
					    ("root", JSON.STRING("|")),
					    ("children", JSON.ARRAY((map toJson args)))])
  | toJson(cond({ant,con,...})) = JSON.OBJECT([("type", JSON.STRING("formula")),
					       ("subtype", JSON.STRING("conditional")),
					       ("root", JSON.STRING("|")),
					       ("children", JSON.ARRAY((map toJson [ant,con])))])
  | toJson(biCond({left,right,...})) = JSON.OBJECT([("type", JSON.STRING("formula")),
						    ("subtype", JSON.STRING("biconditional")),
						    ("root", JSON.STRING("|")),
						    ("children", JSON.ARRAY((map toJson [left,right])))])
  | toJson(uGen({qvar,body,...})) = 
    JSON.OBJECT([("type", JSON.STRING("formula")),
		 ("subtype", JSON.STRING("uquant")),
		 ("root", JSON.STRING("forall")),
		 ("children", JSON.ARRAY([ATV.toJson(qvar),toJson(body)]))])
  | toJson(eGen({qvar,body,...})) = 
    JSON.OBJECT([("type", JSON.STRING("formula")),
		 ("subtype", JSON.STRING("equant")),
		 ("root", JSON.STRING("exists")),
		 ("children", JSON.ARRAY([ATV.toJson(qvar),toJson(body)]))])
  | toJson(eGenUnique({qvar,body,...})) = 
    JSON.OBJECT([("type", JSON.STRING("formula")),
		 ("subtype", JSON.STRING("equant-unique")),
		 ("root", JSON.STRING("exists-unique")),
		 ("children", JSON.ARRAY([ATV.toJson(qvar),toJson(body)]))])

fun makeTPTPPropAux(P,simple_only) = 
  let val P' = alphaRename(P)
      val (lp,rp,comma,blank) = ("(",")",","," ")
      val fvars = freeVars(P')
      val var_prefix = if simple_only then "" else "X"
      val bc_prefix = if simple_only then "" else "$"
      val constant_prefix = if simple_only then "" else "c"
      val fsym_prefix = if simple_only then "" else "f"
      fun f(P_in as atom({term=t,...})) = 
            let val bc = isBooleanConstant(P_in)
		val is_bc = not(bc = "") 
            in
	       if is_bc then bc_prefix^bc else 
	       (case AthTerm.isApp(t) of
                  SOME(g,[]) => constant_prefix^(Basic.fsymRenamer(MS.name(g)))
                | SOME(g,args) => let val is_eq = msymEq(g,N.mequal_logical_symbol)
				      val gname = if is_eq then "=" else fsym_prefix^(Basic.fsymRenamer(MS.name(g)))
                                      val arg_strings = map (fn t => AT.makeTPTPTerm(t,fvars)) args 
                                      val str = if is_eq then 
                                                   (case arg_strings of 
                                                       [s1,s2] => lp^s1^blank^gname^blank^s2^rp)
                                                else gname^lp^(Basic.printListStr(arg_strings,fn x => x,comma))^rp 
			          in
                                    str 
		                  end
                | _ => (case AT.isVarOpt(t) of
                           SOME(v) => if Basic.isMemberEq(v,fvars,ATV.athTermVarEq) then
                                         constant_prefix^(Basic.varRenamer(ATV.name(v)))
                                       else Basic.failLst(["Quantified Boolean variables are not allowed in TPTP formulas."])
                        | _ => raise Basic.Never))
            end
        | f(neg({arg,...})) = "(~ "^f(arg)^")"
        | f(conj({args,...})) = fLst(args," & ")
        | f(disj({args,...})) = fLst(args," | ")
        | f(cond({ant=P1,con=P2,...})) =  "("^f(P1)^" => "^f(P2)^")"
        | f(biCond({left=P1,right=P2,...})) = "("^f(P1)^" <=> "^f(P2)^")"
        | f(uGen({qvar,body,...})) = "! [ "^ var_prefix ^ (AthTerm.makeConservativeName(ATV.name(qvar)))^" ] : ( "^f(body)^")"
        | f(eGen({qvar,body,...})) = "? [ "^ var_prefix ^ (AthTerm.makeConservativeName(ATV.name(qvar)))^" ] : ( "^f(body)^")"
        | f(eGenUnique({qvar,body,...})) = 
		Basic.failLst(["Translation to TPTP failed on exists-unique sentence."])
      and fLst([],_) = ""
        | fLst([P],_) = f(P)
        | fLst(P1::(rest as (_::_)),sep) = "("^(f P1)^sep^(fLst(rest,sep))^")"
  in
     f P'
  end

fun makeTPTPProp(P) = makeTPTPPropAux(P,false)
fun makeTPTPPropSimple(P) = makeTPTPPropAux(P,true)

fun makeTPTPPropList(props) = List.map makeTPTPProp props

fun makeTSTPProp(P) = 
 let val P' = alphaRename(P)
     val fvars = freeVars(P')
     fun f(atom({term,...})) = if AthTerm.isGeneralConstant(term) then AthTerm.makeTSTPTerm(term,fvars,true) 
                               else AthTerm.makeTSTPTerm(term,fvars,false)
       | f(neg({arg,...})) = "( ~ ("^f(arg)^"))"
       | f(conj({args=[],...})) = ""
       | f(conj({args as [P],...})) = f(P)
       | f(conj({args as (P1::P2::rest),...})) = fLst(args," & ")
       | f(disj({args=[],...})) = ""
       | f(disj({args as [P],...})) = f(P)
       | f(disj({args as (P1::P2::rest),...})) = fLst(args," | ")
       | f(cond({ant=P1,con=P2,...})) =  "("^f(P1)^" => "^f(P2)^")"
       | f(biCond({left=P1,right=P2,...})) = "("^f(P1)^" <=> "^f(P2)^")"
       | f(uGen({qvar,body,...})) = "(! [ X"^(AthTerm.makeConservativeName(ATV.name(qvar)))^" ] : ( "^f(body)^"))"
       | f(eGen({qvar,body,...})) = "(? [ X"^(AthTerm.makeConservativeName(ATV.name(qvar)))^" ] : ( "^f(body)^"))"
       | f(eGenUnique({qvar,body,...})) = 
           Basic.failLst(["Translation to TSTP failed on exists-unique sentence."])
       and fLst([],_) = ""
         | fLst([P],_) = f(P)
         | fLst(P1::P2::rest,sep) = "("^(f P1)^sep^(fLst(P2::rest,sep))^")"
     in
       f(P')
     end

fun writeSMT(p,tables as {domain_stream,dec_stream,main_stream,var_table,fsym_table,domain_table,sel_counter,poly_to_mono_sort_table}) = 
  let fun writeMain(str) = (TextIO.output(main_stream,str))
      val domain_decs: (ModSymbol.mod_symbol * string) list ref = ref([])
      val var_prefix = "v"
      fun getSortSym(sort) = (case F.isApp(sort) of
                               SOME(sym,_) => sym)
      val (int_sort_code,real_sort_code,boolean_sort_code) = (MS.code(Names.mint_sort_symbol),MS.code(Names.mreal_sort_symbol),MS.code(Names.mboolean_sort_symbol))
      val (int_sort,real_sort,bool_sort) = ("int","real","bool")
      fun sortName(sort_sym) = 
                let val scode = MS.code(sort_sym) 
                in
                  if scode = int_sort_code then int_sort
                  else if scode = boolean_sort_code then bool_sort
                       else if scode = real_sort_code then real_sort
                             else MS.name(sort_sym)
                end
      fun writeAllDomains() = let fun getSortSym(msym) = 
                                         let val toks = String.tokens (fn c => c = Names.SMT_mono_sort_instantiation_of_poly_sort_char_separator)
                                                                      (MS.name msym)
                                             val str = hd toks
                                             val msym' = MS.makeModSymbol'([],Symbol.symbol str)
                                         in
                                           msym'
                                         end
                                  fun compare(sort_msym1,sort_msym2) = 
                                         let val is_sort1 = Data.isAnySort(sort_msym1)
                                             val is_sort2 = Data.isAnySort(sort_msym2)
                                             val sort_msym1' = if is_sort1 then sort_msym1 else getSortSym(sort_msym1)
                                             val sort_msym2' = if is_sort2 then sort_msym2 else getSortSym(sort_msym2)
                                             val (code1,code2) = (Data.getSequentialStructureCode(sort_msym1'),Data.getSequentialStructureCode(sort_msym2'))
                                             val res =  if (is_sort1 andalso is_sort2) then (code1 < code2) 
                                                        else (String.size(MS.name(sort_msym1)) < String.size(MS.name(sort_msym2)))
                                         in
                                           res 
                                         end
                                  val domain_decs' = Basic.mergeSortBuiltInComp(!domain_decs,fn ((s1,_),(s2,_)) => compare(s1,s2))
                              in
                                List.app (fn (_,str) => TextIO.output(domain_stream,str)) domain_decs'
                              end
      fun loop(atom({term,...})) = (case AT.writeSMT(term,tables) of
                                       [] => ()
                                     | L => domain_decs := L@(!domain_decs))
        | loop(conj({args,...})) = (writeMain("(and ");
                                    loopLst(args);
                                    writeMain(")"))
        | loop(disj({args,...})) = (writeMain("(or ");
                                    loopLst(args);
                                    writeMain(")"))
        | loop(neg({arg,...})) = (writeMain("(not ");loop(arg);writeMain(")"))
        | loop(cond({ant,con,...})) = (writeMain("(=> ");loop(ant); writeMain(blank); loop(con);writeMain(")"))
        | loop(biCond({left,right,flags,hash_code,fvars,poly_constants,...})) = 
                    let val arg1 = cond({ant=left,hash_code=hash_code,con=right,flags=flags,fvars=fvars,poly_constants=poly_constants})
                        val arg2 = cond({ant=right,hash_code=hash_code,con=left,flags=flags,fvars=fvars,poly_constants=poly_constants})
                    in
                       loop(conj({args=[arg1,arg2],flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants}))
                    end
        | loop(uGen({qvar,body,...})) = doQuant("forall",qvar,body)
        | loop(eGen({qvar,body,...})) = doQuant("exists",qvar,body)
        | loop(p) = (Basic.fail("\nExists-unique sentence given to SMT translator: "^(toString1(p))^"\n"))
      and doQuant(q,qvar,body) = 
              let val _ = writeMain("("^q^" (")
                  val there_before = ATV.exists(var_table,qvar)
                  val _ = ATV.insert(var_table,qvar,qvar)
                  val var_sort = ATV.getSort(qvar)
                  val sort_sym = getSortSym(var_sort)
                  val _ = writeMain(var_prefix^(ATV.name(qvar))^"::"^(AT.sortNameSMT(var_sort)))
                  val _ = writeMain(")")
                  val _ = loop(body)
                  val _ = writeMain(")")
              in
                if there_before then () else (ATV.removeHT(var_table,qvar);())
              end
      and loopLst([]) = ()
        | loopLst([p]) = loop(p)
        | loopLst(p::(more as (_::_))) = (loop(p);writeMain(" ");loopLst(more))
  in
     if isPoly(p) then Basic.fail("Polymorphic input given to "^(N.smtSolveFun_name)^": "^(toString1 p))
     else (loop(p);writeAllDomains())
  end

(**** The weights below are optional. If this is not a Max-SMT problem, simply pass an empty list as the value of weights. ****)

fun writeSMTLst(props,
                weights, 
		tables as {domain_stream,dec_stream,main_stream,var_table,fsym_table,domain_table,sel_counter,poly_to_mono_sort_table}) = 
  let val max_smt_problem = not(null(weights))
      fun writeMain(str) = TextIO.output(main_stream,str)
      val domain_decs: (ModSymbol.mod_symbol * string) list ref = ref([])
      val var_prefix = "v"
      fun getSortSym(sort) = (case F.isApp(sort) of
                               SOME(sym,_) => sym)
      val (int_sort_code,real_sort_code,boolean_sort_code) = (MS.code(Names.mint_sort_symbol),MS.code(Names.mreal_sort_symbol),MS.code(Names.mboolean_sort_symbol))
      val (int_sort,real_sort,bool_sort) = ("int","real","bool")
      fun sortName(sort_sym) = 
                let val scode = MS.code(sort_sym) 
                in
                  if scode = int_sort_code then int_sort
                  else if scode = boolean_sort_code then bool_sort
                       else if scode = real_sort_code then real_sort
                             else MS.name(sort_sym)
                end
      fun writeAllDomains() = let fun getSortSym(msym) = 
                                         let val toks = String.tokens (fn c => c = Names.SMT_mono_sort_instantiation_of_poly_sort_char_separator)
                                                                      (MS.name msym)
                                             val str = hd toks
                                             val msym' = MS.makeModSymbol'([],Symbol.symbol str)
                                         in
                                           msym'
                                         end
                                  fun compare(sort_msym1,sort_msym2) = 
                                         let val is_sort1 = Data.isAnySort(sort_msym1)
                                             val is_sort2 = Data.isAnySort(sort_msym2)
                                             val sort_msym1' = if is_sort1 then sort_msym1 else getSortSym(sort_msym1)
                                             val sort_msym2' = if is_sort2 then sort_msym2 else getSortSym(sort_msym2)
                                             val code1 = MS.code(sort_msym1')
                                             val code2 = MS.code(sort_msym2')
                                             val res =  if (is_sort1 andalso is_sort2) then (code1 < code2) 
                                                        else (String.size(MS.name(sort_msym1)) < String.size(MS.name(sort_msym2)))
                                         in
                                           res 
                                         end
                                  val domain_decs' = Basic.mergeSortBuiltInComp(!domain_decs,fn ((s1,_),(s2,_)) => compare(s1,s2))
                              in
                                List.app (fn (_,str) => TextIO.output(domain_stream,str)) domain_decs'
                              end
      fun loop(atom({term,...})) = (case AT.writeSMT(term,tables) of
                                       [] => ()
                                     | L => domain_decs := L@(!domain_decs))
        | loop(conj({args,...})) = (writeMain("(and ");
                                    loopLst(args);
                                    writeMain(")"))
        | loop(disj({args,...})) = (writeMain("(or ");
                                    loopLst(args);
                                    writeMain(")"))
        | loop(neg({arg,...})) = (writeMain("(not ");loop(arg);writeMain(")"))
        | loop(cond({ant,con,...})) = (writeMain("(=> ");loop(ant); writeMain(blank); loop(con);writeMain(")"))
        | loop(biCond({left,right,flags,hash_code,fvars,poly_constants,...})) = 
                    let val arg1 = cond({ant=left,hash_code=hash_code,con=right,flags=flags,fvars=fvars,poly_constants=poly_constants})
                        val arg2 = cond({ant=right,hash_code=hash_code,con=left,flags=flags,fvars=fvars,poly_constants=poly_constants})
                    in
                       loop(conj({args=[arg1,arg2],flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants}))
                    end
        | loop(uGen({qvar,body,...})) = doQuant("forall",qvar,body)
        | loop(eGen({qvar,body,...})) = doQuant("exists",qvar,body)
        | loop(p) = (Basic.fail("\nExists-unique sentence given to SMT translator: "^(toString1(p))^"\n"))
      and doQuant(q,qvar,body) = 
              let val _ = writeMain("("^q^" (")
                  val there_before = ATV.exists(var_table,qvar)
                  val _ = ATV.insert(var_table,qvar,qvar)
                  val var_sort = ATV.getSort(qvar)
                  val sort_sym = getSortSym(var_sort)
                  val _ = writeMain(var_prefix^(ATV.name(qvar))^"::"^(sortName(getSortSym(var_sort))))
                  val _ = writeMain(")")
                  val _ = loop(body)
                  val _ = writeMain(")")
              in
                if there_before then () else (ATV.removeHT(var_table,qvar);())
              end
      and loopLst([]) = ()
        | loopLst([p]) = loop(p)
        | loopLst(p::(more as (_::_))) = (loop(p);writeMain(" ");loopLst(more))	
      and doProp(p) = if isPoly(p) then Basic.fail("Polymorphic input given to "^(N.smtSolveFun_name)^": "^(toString1(p)))
                      else (writeMain("(assert ");
                            loop(p);writeMain(")\n"))
      and doPropWeightPair(p,w) = 
            if isPoly(p) then Basic.fail("Polymorphic input given to "^(N.smtSolveFun_name)^": "^(toString1(p)))
            else (writeMain("(assert+ ");
                            loop(p);
			    writeMain(" ");
			    writeMain(w);
                            writeMain(")\n"))
  in
    if (max_smt_problem) then
      ((List.app doPropWeightPair (Basic.zip(props,weights)));
       writeAllDomains())	 
    else  
      (List.app doProp props;writeAllDomains())
  end

fun writeSMTDefs(defs,file,file_extension) = 
     let val (dom_file,dec_file,main_file) = (file^"_dom."^file_extension,file^"_dec."^file_extension,file^"."^file_extension) 
         val (domain_stream,dec_stream,main_stream) = (TextIO.openOut(dom_file),TextIO.openOut(dec_file),TextIO.openOut(main_file))
         val domain_decs: (ModSymbol.mod_symbol * string) list ref = ref([])
         fun addDomain(pair as (sort_name,dec_string)) = domain_decs := pair::(!domain_decs)
         fun writeAllDomains() = let val domain_decs' = Basic.mergeSort(!domain_decs,fn ((s1,_),(s2,_)) => MS.code(s1)  < MS.code(s2))
                                 in
                                    List.app (fn (_,str) => TextIO.output(domain_stream,str)) domain_decs'
                                 end
         fun writeMain(str) = TextIO.output(main_stream,str)
         val var_table: variable ATV.htable = ATV.makeHTable()
         val fsym_table:bool MS.htable = MS.makeHTableWithInitialSize(3617)
         val dom_table: bool MS.htable = MS.makeHTableWithInitialSize(97)
	 val poly_to_mono_sort_table: (string,F.term list * F.term) HashTable.hash_table = HashTable.mkTable(Basic.hashString, op=) (100,Basic.Never)
         val _ = (MS.insert(dom_table,Names.mboolean_sort_symbol,true);MS.insert(dom_table,Names.mint_sort_symbol,true);
                  MS.insert(dom_table,Names.mreal_sort_symbol,true))
         val counter = ref 0 
         val (lp_define_blank,lp_define_type_blank,define,int_sort,real_sort,bool_sort,lp,rp,blank,double_rp_newline,double_colon) = 
             ("\n(define ","\n(define-type ", "define","int","real","bool","(",")"," ","))\n","::")
         val (var_prefix,fsym_prefix) = ("v","f")
         val table_rec = {domain_stream=domain_stream,dec_stream=dec_stream,main_stream=main_stream,poly_to_mono_sort_table=poly_to_mono_sort_table,
                          var_table=var_table,fsym_table=fsym_table,domain_table=dom_table,sel_counter=counter}
         val _ = (TextIO.output(dec_stream,"(include \""^dom_file^"\")\n");
                  TextIO.output(main_stream,"(include \""^dec_file^"\")\n"))
         val (int_sort,real_sort,bool_sort) = ("int","real","bool")
         val (int_sort_code,real_sort_code,boolean_sort_code) = (MS.code(Names.mint_sort_symbol),MS.code(Names.mreal_sort_symbol),MS.code(Names.mboolean_sort_symbol))
         fun getSortSym(sort) = (case F.isApp(sort) of
                                    SOME(sym,_) => sym)
         fun sortName(sort_sym) = 
                let val scode = MS.code(sort_sym) 
                in
                  if scode = int_sort_code then int_sort
                  else if scode = boolean_sort_code then bool_sort
                       else if scode = real_sort_code then real_sort
                             else MS.name(sort_sym)
                end
         fun constructorString(c:Data.ath_struc_constructor as {name,arity,selectors,argument_types,range_type,...}) = 
             (MS.insert(fsym_table,name,true);
              if arity < 1 then fsym_prefix^(MS.name name) 
               else let fun getSelName(NONE:MS.mod_symbol option) = fsym_prefix^(Names.smt_default_selector_fun_sym_prefix)^(Int.toString(Basic.incAndReturn(counter)))
                          | getSelName(SOME(ms)) = (MS.insert(fsym_table,ms,true);fsym_prefix^MS.name(ms))
                        val arg_sorts_and_sels = Basic.zip(argument_types,selectors) 
                        fun loop([]) = ""
                          | loop((arg_sort,sel)::more) = let val str = getSelName(sel)
                                                         in 
                                                            str^double_colon^(sortName(getSortSym arg_sort))
                                                         end
                        val sel_string = loop(arg_sorts_and_sels)
                    in 
                       lp^(fsym_prefix^(MS.name name))^blank^sel_string^rp
                    end)
         fun constructorsString([],res) = res
           | constructorsString(c::more,res) = constructorsString(more,blank^(constructorString c)^res)
         fun declareSort(sort_sym) = 
            (case Data.findStructure(sort_sym) of
                SOME(struc as {constructors,arity,obtype_params,...}) => 
                  let 
                      val str = lp_define_type_blank^(MS.name sort_sym)^" (datatype "^
                                (constructorsString(constructors,""))^double_rp_newline
                  in
                     addDomain(sort_sym,str)
                  end
               | _ => let 
                           val str = lp_define_type_blank^(MS.name sort_sym)^rp
                      in
                        addDomain(sort_sym,str)
                      end)
         fun possiblyDeclareSort(sort_sym) = 
             (case MS.find(dom_table,sort_sym) of
                 SOME(_) => ()
               | _ => (declareSort(sort_sym);
                       MS.insert(dom_table,sort_sym,true)))
         fun writeDef(def_term,body) = 
               let val vars = AT.getVars(def_term)
                   val _ = map (fn v => ATV.insert(var_table,v,v)) vars 
                   val fsym = (case AT.isApp(def_term) of
                                  SOME(f,_) => f)
                   val sym_name_and_sig = 
                            (case Data.getSignature(fsym) of
                               (arg_sorts,output_sort,_,has_pred_based_sorts) => 
                                    let val arg_sort_names = map (fn s => sortName(getSortSym(s))) arg_sorts
                                        val fsym_name = fsym_prefix^(MS.name(fsym))
                                        val output_sort_name = sortName(getSortSym(output_sort))
                                    in
                                     if null(vars) then
                                       fsym_name^"::"^output_sort_name
                                     else
                                       fsym_name^"::(-> "^(Basic.printListStr(arg_sort_names, fn x => x, " "))^" "^output_sort_name^")"
                                    end)
                   fun doVar(v) = 
                           let val var_sort = ATV.getSort(v)
                               val sort_sym = getSortSym(var_sort)
                           in
                               TextIO.output(main_stream,var_prefix^(ATV.name(v))^"::"^(sortName(getSortSym(var_sort))))
                           end
                   fun doParamList() = List.app doVar vars 
                   val _ = if null(vars) then
                                writeMain("\n(define " ^ sym_name_and_sig ^ " ")
                           else 
                                (writeMain("\n(define " ^ sym_name_and_sig ^ " " ^ "(lambda (");
                                 doParamList();
                                 writeMain(") "))
                   val _ = writeSMT(body,table_rec)               
               in 
                  if null(vars) then writeMain(")") else writeMain("))")
               end
         val _ = (List.app writeDef defs;writeMain("\n"))
         val _ = writeAllDomains()
     in
         (TextIO.closeOut(domain_stream);TextIO.closeOut(dec_stream);TextIO.closeOut(main_stream))
     end  

fun writeCVC(p,tables as {domain_stream,dec_stream,main_stream,var_table,inverse_var_table,fsym_table,
                          inverse_fsym_table,
                          domain_table,
                          inverse_domain_table,
                          sel_counter,fsym_counter,dom_counter,var_counter}) = 
  let fun writeMain(str) = TextIO.output(main_stream,str) 
      val domain_decs: (string * string) list ref = ref([])
      val var_prefix = "v"
      fun getSortSym(sort) = (case F.isApp(sort) of
                               SOME(sym,_) => sym)
      val (int_sort_code,real_sort_code,boolean_sort_code) = (MS.code(Names.mint_sort_symbol),MS.code(Names.mreal_sort_symbol),MS.code(Names.mboolean_sort_symbol))
      val (int_sort,real_sort,bool_sort) = ("INT","REAL","BOOLEAN")
      fun sortName(sort_sym) = 
                let val scode = MS.code(sort_sym) 
                in
                  if scode = int_sort_code then int_sort
                  else if scode = boolean_sort_code then bool_sort
                       else if scode = real_sort_code then real_sort
                             else MS.name(sort_sym)
                end
      fun writeAllDomains() = let fun getSortSym(msym) = 
                                         let val toks = String.tokens (fn c => c = Names.CVC_mono_sort_instantiation_of_poly_sort_char_separator)
                                                                      (MS.name msym)
                                             val str = hd toks
                                             val msym' = MS.makeModSymbol'([],Symbol.symbol str)
                                         in
                                           msym'
                                         end
                                  fun compare(sort_msym1,sort_msym2) = true
                                  val domain_decs' = Basic.mergeSortBuiltInComp(!domain_decs,fn ((s1,_),(s2,_)) => compare(s1,s2))
                              in
                                List.app (fn (_,str) => TextIO.output(domain_stream,str)) domain_decs'
                              end
      fun loop(atom({term,...})) = (let val res = AT.writeCVC(term,tables)
                                    in
				     (case res of
                                        [] => ()
                                      | L => domain_decs := L@(!domain_decs))
				    end)
        | loop(conj({args,...})) = (writeMain("(");
                                    loopLst(args, " AND ");
                                    writeMain(")"))
        | loop(disj({args,...})) = (writeMain("(");
                                    loopLst(args, " OR ");
                                    writeMain(")"))
        | loop(neg({arg,...})) = (writeMain("(NOT ");loop(arg);writeMain(")"))
        | loop(cond({ant,con,...})) = (writeMain("(");loop(ant); writeMain(" => "); loop(con);writeMain(")"))
        | loop(biCond({left,right,flags,hash_code,fvars,poly_constants,...})) = 
                    let val arg1 = cond({ant=left,hash_code=hash_code,con=right,flags=flags,fvars=fvars,poly_constants=poly_constants})
                        val arg2 = cond({ant=right,hash_code=hash_code,con=left,flags=flags,fvars=fvars,poly_constants=poly_constants})
                    in
                       loop(conj({args=[arg1,arg2],flags=flags,hash_code=hash_code,fvars=fvars,poly_constants=poly_constants}))
                    end
        | loop(uGen({qvar,body,...})) = doQuant("FORALL ",qvar,body)
        | loop(eGen({qvar,body,...})) = doQuant("EXISTS ",qvar,body)
        | loop(p) = (Basic.fail("\nExists-unique sentence given to SMT translator: "^(toString1(p))^"\n"))
      and doQuant(q,qvar,body) = 
              let val _ = writeMain("("^q^"(")
                  val there_before = ATV.exists(var_table,qvar)
                  val _ = ATV.insert(var_table,qvar,ATV.name(qvar))
                  val var_sort = ATV.getSort(qvar)
                  val sort_sym = getSortSym(var_sort)
                  val _ = writeMain(var_prefix^(ATV.name(qvar))^": "^(sortName(getSortSym(var_sort))))
                  val _ = writeMain(")")
                  val _ = loop(body)
                  val _ = writeMain(")")
              in
                if there_before then () else (ATV.removeHT(var_table,qvar);())
              end
      and loopLst([],_) = ()
        | loopLst([p],_) = loop(p)
        | loopLst(p::(more as (_::_)),sep) = (loop(p);writeMain(sep);loopLst(more,sep))
  in
     if isPoly(p) then Basic.fail("Polymorphic input given to "^(N.smtSolveFun_name)^": "^(toString1 p))
     else (loop(p);writeAllDomains())
  end
          
fun makeTSTPPropFast(P) = 
 let val A = CharArray.array(10000000,#"a")
     fun write(str,i) = Basic.writeStringToCharArray(str,A,i)
     val (lp,rp,blank) = (Basic.lparen,Basic.rparen,Basic.blank)
     val fvars = freeVars(P)
     fun f(atom({term,...}),i) = 
        if AthTerm.isGeneralConstant(term) then AthTerm.makeTSTPTermFast(term,fvars,true,A,i) 
        else AthTerm.makeTSTPTermFast(term,fvars,false,A,i)
       | f(neg({arg,...}),i) = let val i1 = write("( ~ (",i) 
                                   val i2 = f(arg,i1)
                               in
                                  write("))",i2)
                               end
       | f(conj({args=[],...}),i) = i
       | f(conj({args as [P],...}),i) = f(P,i)
       | f(conj({args as (P1::P2::rest),...}),i) = fLst(args," & ",i)
       | f(disj({args=[],...}),i) = i
       | f(disj({args as [P],...}),i) = f(P,i)
       | f(disj({args as (P1::P2::rest),...}),i) = fLst(args," | ",i)
       | f(cond({ant=P1,con=P2,...}),i) =  let val i1 = write(lp,i)
                                               val i2 = f(P1,i1)
                                               val i3 = write(" => ",i2)
                                               val i4 = f(P2,i3)
                                           in
                                              write(rp,i4)
                                           end
       | f(biCond({left=P1,right=P2,...}),i) = let val i1 = write(lp,i)
                                                   val i2 = f(P1,i1)
                                                   val i3 = write(" <=> ",i2)
                                                   val i4 = f(P2,i3)
                                               in
                                                  write(rp,i4)
                                               end
       | f(uGen({qvar,body,...}),i) = i 
       | f(eGen({qvar,body,...}),i) = i
       | f(eGenUnique({qvar,body,...}),i) = i 
       and fLst([],_,i) = i
         | fLst([P],_,i) = f(P,i)
         | fLst(P1::(more as (P2::rest)),sep,i) = 
               let val i1 = write(lp,i)
                   val i2 = f(P1,i1)
                   val i3 = write(sep,i2)
                   val i4 = fLst(more,sep,i3)
               in
                  write(rp,i4)
               end                                      
     in
       (let val i = f(P,0) in (A,i) end)
     end

fun makeSpassProp(P,variableRenamer,fsymRenamer) = 
 let val P' = alphaRename(P)
     val fvars = freeVars(P')
     val psym_ht: (string,string) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (99,Basic.Never)
     val fsym_ht: (string,string) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (99,Basic.Never)
     fun addFS(key,str) = HashTable.insert fsym_ht (key,str)
     fun addPS(key,str) = HashTable.insert psym_ht (key,str)
     fun f(P_in as atom({term=t,...})) = 
            let val bc = isBooleanConstant(P_in)
		val is_bc = not(bc = "") 
		val tstr = if is_bc then "" else AT.makeSpassTerm(t,fvars,variableRenamer,fsymRenamer,fsym_ht)
            in
	       if is_bc then bc else
	       (case AthTerm.isApp(t) of
                  SOME(f,[]) => let val psym = "c"^(fsymRenamer(MS.name(f)))
                                    val str = "("^psym^",0)"
                                    val _ = addPS(psym,str)
			        in
                                   tstr
		                end
                | SOME(f,args) => let val is_eq = msymEq(f,N.mequal_logical_symbol)
                                      val psym = "f"^(fsymRenamer(MS.name(f)))
				      val str = "("^psym^","^(Int.toString(length(args)))^")"
			              val _ = if is_eq then () else addPS(psym,str)			
			          in
                                    tstr
		                  end
                | _ => (case AT.isVarOpt(t) of
                           SOME(v) => if Basic.isMemberEq(v,fvars,ATV.athTermVarEq) then
                                         let val psym = "c"^(variableRenamer(ATV.name(v)))
                                             val str = "("^psym^",0)"
                                             val _ = addPS(psym,str)
                                         in
					    tstr
				         end
                                       else
                                       raise SpassTranslation("quantified Boolean variables are not "^
						              "allowed in Spass formulas.")
                        | _ => raise Basic.Never))
             end
       | f(neg({arg=Q,...})) = let val qstr = f(Q)
                               in
                                 "not("^qstr^")"
			       end
       | f(conj({args,...})) = fLst(args,"and")
       | f(disj({args,...})) = fLst(args,"or")
       | f(cond({ant=P1,con=P2,...})) = 
			    let val Pstr1 = f(P1)
                                val Pstr2 = f(P2)
		            in
			       "implies("^Pstr1^","^Pstr2^")"
			    end
       | f(biCond({left=P1,right=P2,...})) = 
			    let val Pstr1 = f(P1)
                                val Pstr2 = f(P2)
		            in
			       "equiv("^Pstr1^","^Pstr2^")"
			    end
       | f(uGen({qvar=x,body=P,...})) = 
			  let val Pstr = f(P)
                          in
			     "forall([X"^ATV.name(x)^"],"^Pstr^")"
                          end
       | f(eGen({qvar=x,body=P,...})) = 
		          let val Pstr = f(P)
                          in
			     "exists([X"^ATV.name(x)^"],"^Pstr^")"
                          end
      | f(eGenUnique(_)) = Basic.failLst ["Translation to SPASS failed on exists-unique sentence."]
     and fLst([],_) = ""
       | fLst([P],_) = f(P)
       | fLst(P1::(L as _::_),op_str) = 
		let val Pstr1 = f(P1)
                    val Pstr2 = fLst(L,op_str)
                in
		  op_str^Basic.lparen^Pstr1^Basic.comma^Pstr2^Basic.rparen
		end
     val prop_str = f(P')
     val psym_and_psym_values = HashTable.listItemsi psym_ht 
     val psyms = map #1 psym_and_psym_values
     val _ = List.app (fn psym => (HashTable.remove fsym_ht psym;())) psyms
     val fsyms = HashTable.listItems(fsym_ht)
     in
        (prop_str,fsyms,psyms)
    end

fun makeSpassUgen(L,p,format) = 
      let fun f([],p) = p
            | f(v::rest,p) = let val p' = f(rest,p)
                             in
                                if format = "spass" then 
                                   "forall(["^v^"],"^p'^")"
                                else " ! [ "^v^" ] : ( "^p'^")"
                             end
      in 
        f(L,p)
      end    

fun makePolySpassProp(P,variableRenamer,fsymRenamer) = 
 let val P' = alphaRename(P)
     val fvars = freeVars(P')
     val _ = print("\nTranslating prop: " ^ (toString1(P')) ^ " with free vars: " ^ (Basic.printListStr(fvars,ATV.toStringDefault,",")))
     val (lp,rp,comma) = ("(",")",",")
     val printer = F.makePolyVarSortPrinter()     
     fun f(P_in as atom({term=t,...})) = 
            let val bc = isBooleanConstant(P_in)
		val is_bc = not(bc = "") 
            in
	       if is_bc then (bc,[],[],[],[],[]) else
	       (case AthTerm.isApp(t) of
                  SOME(f,[]) => let val psym = "(c"^(fsymRenamer(MS.name(f)))^",0)" 
                                    val str = "c"^(fsymRenamer(MS.name(f)))
      		                    val (tstr,{vars=sort_vars,fsyms=fsyms,fsymbols=fsymbols,osorts=os,...}) = 
                                              if is_bc then ("",{vars=[],fsymbols=[],fsyms=[],osorts=[]}) else 
 				              AT.makePolySpassTerm(t,fvars,variableRenamer,fsymRenamer,printer)
			        in
                                   (str,Basic.remove(psym,fsyms),fsymbols,[psym],sort_vars,os)
		                end
                | SOME(f,args) => let val (arg_strings,{vars=sort_vars,fsymbols=fsymbols,fsyms=fsyms,osorts=os}) = 
                                           AT.makePolySpassTermLst(args,fvars,variableRenamer,fsymRenamer,printer)
                                      val is_eq = msymEq(f,N.mequal_logical_symbol)
				      val fname = if is_eq then "equal" else "f"^(fsymRenamer(MS.name(f)))
				      val psym = "(f"^(fsymRenamer(MS.name(f)))^","^
						(Int.toString(length(args)))^")"
				      val fsyms' = if is_eq then fsyms else 
 						    Basic.remove(psym,fsyms)
				      val psyms' = if is_eq then [] else [psym]
                                      val str = fname^lp^(Basic.printListStr(arg_strings,fn x => x,comma))^rp 
			          in
                                    (str,fsyms',fsymbols,psyms',sort_vars,os)
		                  end
                | _ => (case AT.isVarOpt(t) of
                           SOME(v) => if Basic.isMemberEq(v,fvars,ATV.athTermVarEq) then
                                         let val name = "c"^(variableRenamer(ATV.name(v)))
                                             val psym = "(c"^(variableRenamer(ATV.name(v)))^",0)"
         		                     val (tstr,{vars=sort_vars,fsyms=fsyms,fsymbols=fsymbols,osorts=os}) = 
                                                     if is_bc then ("",{vars=[],fsyms=[],fsymbols=[],osorts=[]}) else 
 				                        AT.makePolySpassTerm(t,fvars,variableRenamer,fsymRenamer,printer)
                                         in
					    (name,Basic.remove(psym,(fsyms)),fsymbols,[psym],sort_vars,os)
				         end
                                       else 
                                       (
                                       raise SpassTranslation("quantified Boolean variables are not "^
						              "allowed in Spass formulas.")
                                         )
                        | _ => raise Basic.Never))
             end
       | f(neg({arg=Q,...})) = let val (qstr,fsyms,fsymbols,psyms,sort_vars,os) = f(Q)
                               in
                                 ("not("^qstr^")",fsyms,fsymbols,psyms,sort_vars,os)
			       end
       | f(conj({args,...})) = fLst(args,"and")
       | f(disj({args,...})) = fLst(args,"or")
       | f(cond({ant=P1,con=P2,...})) = 
			    let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                                val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = f(P2)
		            in
			       ("implies("^Pstr1^","^Pstr2^")",fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
			    end
       | f(biCond({left=P1,right=P2,...})) = 
			    let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                                val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = f(P2)
		            in
			       ("equiv("^Pstr1^","^Pstr2^")",fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
			    end
       | f(uGen({qvar=x,body=P,...})) = 
			  let val (Pstr,fsyms,fsymbols,psyms,sort_vars,os) = f(P)
                          in
			     ("forall([X"^(variableRenamer(ATV.name(x)))^"],"^Pstr^")",fsyms,fsymbols,psyms,sort_vars,os)
                          end
       | f(eGen({qvar=x,body=P,...})) = 
		          let val (Pstr,fsyms,fsymbols,psyms,sort_vars,os) = f(P)
                          in
			     ("exists([X"^(variableRenamer(ATV.name(x)))^"],"^Pstr^")",fsyms,fsymbols,psyms,sort_vars,os)
                          end
      | f(eGenUnique(_)) = Basic.failLst ["Translation to SPASS failed on exists-unique sentence."]
     and fLst([],_) = ("",[],[],[],[],[])
       | fLst([P],_) = f P
       | fLst(P1::(L as _::_),op_str) = 
		let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                    val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = fLst(L,op_str)
                in
		  (op_str^Basic.lparen^Pstr1^Basic.comma^Pstr2^Basic.rparen,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
		end
     in
         let val (Pstr,fsyms,fsymbols,psyms,sort_vars,os) = f(P')
             val sort_vars' = Basic.removeDuplicatesEq(sort_vars,op=)
             val pstr' = makeSpassUgen(sort_vars',Pstr,"spass")
             val psyms' = ("(psubsort,2)")::("(phas_sort,2)")::psyms
         in
           (pstr',fsyms,fsymbols,psyms',sort_vars,os)
         end 
  end

fun makePolySpassPropList(plst) = 
     let val id = fn x => x
	 val variableRenamer = Basic.varRenamer;
	 val fsymRenamer = Basic.fsymRenamer;
	 fun f([],fsyms,fsymbols,psyms,prop_strings,osorts) = let val (fsyms',psyms') = (Basic.printListStrCommas(fsyms,id),
                                                                                         Basic.printListStrCommas(psyms,id))
                                                                  val osorts' = Basic.removeDuplicatesEq(osorts,msymEq) 							
                                                                  val fsymbols' = Basic.removeDuplicatesEq(fsymbols,msymEq)

                                                              in
                                                                 ((fsyms',fsyms,fsymbols'),(psyms',psyms),rev(prop_strings),osorts')
			                 	              end
           | f(P::rest,fsyms,fsymbols,psyms,prop_strings,osorts) = let val (pstr,fsyms',fsymbols',psyms',sort_vars,osorts') = 
    				  			               makePolySpassProp(P,variableRenamer,fsymRenamer)
                      	                                           in
                            	                                      f(rest,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,pstr::prop_strings,osorts'@osorts)
						                   end
      in
         f(plst,[],[],[],[],[])
      end;

(* This is the function used to translate Athena into Vampire: *)

fun makePolyProp(P,variableRenamer,fsymRenamer,format) = 
 let val P' = alphaRename(P)
     val fvars = freeVars(P')
     val (lp,rp,comma) = ("(",")",",")
     val printer = F.makePolyVarSortPrinter()     
     val eq_symbol = if format = "spass" then "equal" else "="
     val neg_sign = if format = "spass" then "not" else " ~ "
     val and_sign = if format = "spass" then "and" else " & "     
     val or_sign = if format = "spass" then "or" else " | "
     val if_sign = if format = "spass" then "implies" else " => "
     val iff_sign = if format = "spass" then "equiv" else " <=> "
     val forall_sign = if format = "spass" then "forall" else "! "
     val exists_sign = if format = "spass" then "exists" else "? "
     fun isBooleanVar(v) = F.sortEq(ATV.getSort(v),F.boolean_sort)
     fun f(P_in as atom({term=t,...})) = 
            let val bc = isBooleanConstant(P_in)
		val is_bc = not(bc = "") 
                val bc' = if format = "spass" then bc else "$"^bc 
            in
	       if is_bc then (bc',[],[],[],[],[]) else
	       (case AthTerm.isApp(t) of
                  SOME(f,[]) => let val psym = "(c"^(fsymRenamer(MS.name(f)))^",0)" 
                                    val str = "c"^(fsymRenamer(MS.name(f)))
      		                    val (tstr,{vars=sort_vars,fsyms=fsyms,fsymbols=fsymbols,osorts=os,...}) = 
                                              if is_bc then ("",{vars=[],fsymbols=[],fsyms=[],osorts=[]}) else 
 				              AT.makePolySpassTerm(t,fvars,variableRenamer,fsymRenamer,printer)
			        in
                                   (str,Basic.remove(psym,fsyms),fsymbols,[psym],sort_vars,os)
		                end
                | SOME(f,args) => let val (arg_strings,{vars=sort_vars,fsymbols=fsymbols,fsyms=fsyms,osorts=os}) = 
                                           AT.makePolySpassTermLst(args,fvars,variableRenamer,fsymRenamer,printer)
                                      val is_eq = msymEq(f,N.mequal_logical_symbol)
				      val fname = if is_eq then eq_symbol else "f"^(fsymRenamer(MS.name(f)))
				      val psym = "(f"^(fsymRenamer(MS.name(f)))^","^
						(Int.toString(length(args)))^")"
				      val fsyms' = if is_eq then fsyms else 
 						    Basic.remove(psym,fsyms)
				      val psyms' = if is_eq then [] else [psym]
                                      val str = if (is_eq andalso not(format = "spass")) then 
                                                   (case arg_strings of 
                                                        [s1,s2] => lp^s1^blank^fname^blank^s2^rp)
                                                else fname^lp^(Basic.printListStr(arg_strings,fn x => x,comma))^rp 
			          in
                                    (str,fsyms',fsymbols,psyms',sort_vars,os)
		                  end
                | _ => (case AT.isVarOpt(t) of
                           SOME(v) => let val name = "c"^(variableRenamer(ATV.name(v)))
                                          val psym = "(c"^(variableRenamer(ATV.name(v)))^",0)"
       		                          val (tstr,{vars=sort_vars,fsyms=fsyms,fsymbols=fsymbols,osorts=os}) = 
                                                       if is_bc then ("",{vars=[],fsyms=[],fsymbols=[],osorts=[]}) else 
 				                          AT.makePolySpassTerm(t,fvars,variableRenamer,fsymRenamer,printer)
                                      in
				          if Basic.isMemberEq(v,fvars,ATV.athTermVarEq) then
  				              (name,Basic.remove(psym,(fsyms)),fsymbols,[psym],sort_vars,os)
                                          else
                                                f(makeEquality(t,AT.true_term))
                                      end
                        | _ => raise Basic.Never))
             end
       | f(neg({arg=Q,...})) = let val (qstr,fsyms,fsymbols,psyms,sort_vars,os) = f(Q)
                               in
                                 (neg_sign^"("^qstr^")",fsyms,fsymbols,psyms,sort_vars,os)
			       end
       | f(conj({args,...})) = if format = "spass" then fLst(args,and_sign) else gLst(args,and_sign)
       | f(disj({args,...})) = if format = "spass" then fLst(args,or_sign) else gLst(args,or_sign)
       | f(cond({ant=P1,con=P2,...})) = 
			    let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                                val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = f(P2)
                                val str = if format = "spass" then if_sign^lp^Pstr1^comma^Pstr2^rp 
                                          else lp^Pstr1^if_sign^Pstr2^rp
		            in
                              (str,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
			    end
       | f(biCond({left=P1,right=P2,...})) = 
			    let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                                val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = f(P2)
                                val str = if format = "spass" then iff_sign^lp^Pstr1^comma^Pstr2^rp 
                                          else lp^Pstr1^iff_sign^Pstr2^rp
		            in
			       (str,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
			    end
       | f(uGen({qvar=x,body=P,...})) = 
 	            let val (Pstr,fsyms,fsymbols,psyms,sort_vars,os) = f(P)
                        val vname = variableRenamer(ATV.name(x))
                        val str = if format = "spass" then forall_sign^lp^"[X"^vname^"],"^Pstr^rp
                                  else forall_sign^"[ X"^vname^" ] : ( "^Pstr^rp
                    in
                      (str,fsyms,fsymbols,psyms,sort_vars,os)
                    end
       | f(eGen({qvar=x,body=P,...})) = 
                  let val (Pstr,fsyms,fsymbols,psyms,sort_vars,os) = f(P)
                      val vname = variableRenamer(ATV.name(x))
                      val str = if format = "spass" then exists_sign^lp^"[X"^vname^"],"^Pstr^rp
                                else exists_sign^"[ X"^vname^" ] : ( "^Pstr^rp
                  in
   	             (str,fsyms,fsymbols,psyms,sort_vars,os)
                  end
      | f(eGenUnique(_)) = Basic.failLst ["Translation to SPASS failed on exists-unique sentence."]
     and fLst([],_) = ("",[],[],[],[],[])
       | fLst([P],_) = f P
       | fLst(P1::(L as _::_),op_str) = 
		let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                    val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = fLst(L,op_str)
                in
		  (op_str^Basic.lparen^Pstr1^Basic.comma^Pstr2^Basic.rparen,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
		end
      and gLst([],_) = ("",[],[],[],[],[])
        | gLst([P],_) = f P 
        | gLst(P1::(L as _::_),op_str) = 
		let val (Pstr1,fsyms,fsymbols,psyms,sort_vars,os) = f(P1)
                    val (Pstr2,fsyms',fsymbols',psyms',sort_vars',os') = gLst(L,op_str) 
                    val str = lp^Pstr1^op_str^Pstr2^rp
                in
                   (str,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,sort_vars'@sort_vars,os'@os)
                end
     in
         let val (Pstr,fsyms,fsymbols,psyms,sort_vars,os) = f(P')
             val sort_vars' = Basic.removeDuplicatesEq(sort_vars,op=)
             val pstr' = makeSpassUgen(sort_vars',Pstr,format)
             val psyms' = ("(psubsort,2)")::("(phas_sort,2)")::psyms
         in
           (pstr',fsyms,fsymbols,psyms',sort_vars',os)
         end 
  end
  
fun makePolyPropList(plst,format,fsymRenamer) = 
     let val id = fn x => x
	 val variableRenamer = Basic.varRenamer;
	 fun f([],fsyms,fsymbols,psyms,prop_strings,osorts) = let val (fsyms',psyms') = (Basic.printListStrCommas(fsyms,id),
                                                                                         Basic.printListStrCommas(psyms,id))
                                                                  val osorts' = Basic.removeDuplicatesEq(osorts,msymEq) 							
                                                                  val fsymbols' = Basic.removeDuplicatesEq(fsymbols,msymEq)

                                                              in
                                                                 ((fsyms',fsyms,fsymbols'),(psyms',psyms),rev(prop_strings),osorts')
			                 	              end
           | f(P::rest,fsyms,fsymbols,psyms,prop_strings,osorts) = let val (pstr,fsyms',fsymbols',psyms',sort_vars,osorts') = 
    				  			               makePolyProp(P,variableRenamer,fsymRenamer,format)
                      	                                           in
                            	                                      f(rest,fsyms'@fsyms,fsymbols'@fsymbols,psyms'@psyms,pstr::prop_strings,osorts'@osorts)
						                   end
      in
         f(plst,[],[],[],[],[])
      end

fun makeSpassPropList(plst,fsymRenamer) = 
     let val id = fn x => x
	 val variableRenamer = Basic.varRenamer;
	 fun f([],fsyms,psyms,prop_strings) = let val (fsyms',psyms') = 
						       (Basic.printListStrCommas(fsyms,id),
							Basic.printListStrCommas(psyms,id))
                                              in
                                                 (fsyms',psyms',rev(prop_strings))
				              end
           | f(P::rest,fsyms,psyms,prop_strings) = let val (pstr,fsyms',psyms') = 
							    makeSpassProp(P,variableRenamer,fsymRenamer)
                      	                           in
                            	                      f(rest,fsyms'@fsyms,psyms'@psyms,pstr::prop_strings)
						   end
      in
         f(plst,[],[],[])
      end
	
val applySub = 
     (fn (sub,P) =>
	let
            fun f(atom({term,flags,...})) = 
			let val term' = AT.applySub(sub,term)
			    val flags' = makeFlagsFromWord(makeWord({poly=AT.isPoly(term'),
                                                           involves_pred_based_sorts=AT.involvesPredBasedSorts(term'),
						           bvars=false,fvars=AT.hasVars(term')}))
                            val hc = AT.fastHash(term')
		  	in
				atom({term=term',hash_code=hc,flags=flags'})
			end
	      | f(neg({arg,fvars,flags,...})) = let val arg' = f arg
                                                    val hc = B.hashTwoWords(neg_code,fastHash(arg'))
						in
					          neg({arg=arg',fvars=freeVars(arg'),hash_code=hc,poly_constants=getPolyConstants(arg'),flags=inheritWordFromProp(arg')})
						end
	      | f(conj({args,flags,fvars,...})) = 
			let val args' = map f args
			in
			   makeConjunction(args')
			end
	      | f(disj({args,flags,fvars,...})) = 
			let val args' = map f args
			in
			   makeDisjunction(args')
			end
	      | f(cond({ant,con,flags,fvars,...})) = 
			let val (ant',con') = (f ant,f con)
			in 
				makeConditional(ant',con')
			end
	      | f(biCond({left,right,flags,fvars,...})) = 
			let val (left',right') = (f left,f right)
			in 
			 	makeBiConditional(left',right')
			end		
	      | f(p as uGen({qvar,body,flags,fvars})) = 
                        if AT.nameInSupp(qvar,sub) then p else makeUGen([qvar],f body)
	      | f(p as eGen({qvar,body,flags,fvars})) = 
                        if AT.nameInSupp(qvar,sub) then p else makeEGen([qvar],f body)
	      | f(p as eGenUnique({qvar,body,flags,fvars})) = 
                        if AT.nameInSupp(qvar,sub) then p else makeEGenUnique([qvar],f body)
	in
	   f  (alphaRename P)
	end)
	
fun replaceVarByTermOfSomeSubSort(v,t,P,sort_sub) = 
	if not(hasFreeVars(P)) then P else 
	let val unit_sub = AT.makeSub([(v,t)])
	in
	   applySub(unit_sub,P)
	end

val (matchRWraw,matchLstRWraw) = 
     let fun debugPrint(str) = ()
         fun f(p1 as atom({term=term1,...}),p2 as atom({term=term2,...}),sub,sort_sub,uvars,banned) = 
                 let val _ = debugPrint("\nDoing atoms...\n")
		     val res = AT.matchRWrawWithBanned(term1,term2,sub,sort_sub,uvars,banned)
		     val _ = let val _ = debugPrint("\nGot a result from the atom matching, namely: ")
                             in
			        (case res of
                                    SOME(sub,sort_sub) => debugPrint("\nHere's the sub: " ^ AT.subToString(sub) ^ "\nand the sort sub: " ^ (FTerm.subToString(sort_sub)))
                                 | _ => ())
                             end
                 in
                   res
                 end 
           | f(p1 as neg({arg=arg1,...}),p2 as neg({arg=arg2,...}),sub,sort_sub,uvars,banned)  =
                                   let val _ = debugPrint("\nDoing negations...\n")
                                   in
                                       f(arg1,arg2,sub,sort_sub,uvars,banned)
                                   end
           | f(p1 as cond({ant=ant1,con=con1,...}),p2 as cond({ant=ant2,con=con2,...}),sub,sort_sub,uvars,banned) = 
                                   let val _ = debugPrint("\nDoing conditionals...\n")
                                   in
                                       fLst([ant1,con1],[ant2,con2],sub,sort_sub,uvars,banned)
                                   end
           | f(p1 as biCond({left=left1,right=right1,...}),p2 as biCond({left=left2,right=right2,...}),
	   sub,sort_sub,uvars,banned) = 
                    fLst([left1,right1],[left2,right2],sub,sort_sub,uvars,banned)

           | f(p1 as conj({args=args1,...}),p2 as conj({args=args2,...}),sub,sort_sub,uvars,banned) = 
                  let val _ = debugPrint("\nDoing conjunctions...\n")
                  in 
                     fLst(args1,args2,sub,sort_sub,uvars,banned)
                  end
           | f(p1 as disj({args=args1,...}),p2 as disj({args=args2,...}),sub,sort_sub,uvars,banned) = 
                  let val _ = debugPrint("\nDoing disjunctions...\n")
                  in 
                     fLst(args1,args2,sub,sort_sub,uvars,banned)
                  end
           | f(p1 as uGen({qvar=qvar1,body=body1,...}),p2 as uGen({qvar=qvar2,body=body2,...}),
	   sub,sort_sub,uvars,banned) = 
                 let val fresh_var_name = ATV.freshVarName()
		     val qvar_pat_sort = ATV.getSort(qvar2)
		     val qvar_obj_sort = ATV.getSort(qvar1)
		     val sort_sub' = F.matchModuloSub(qvar_obj_sort,qvar_pat_sort,sort_sub)
		     val sort_sub = FTerm.composeSubs(sort_sub',sort_sub)
                     val fresh_var_1 = ATV.applySortSub(sort_sub,ATV.athTermVarWithSort(fresh_var_name,qvar_obj_sort))
                     val fresh_var_2 = ATV.applySortSub(sort_sub,ATV.athTermVarWithSort(fresh_var_name,qvar_pat_sort))
                     val body1' = unsafeReplace(qvar1,AT.makeVar fresh_var_1,body1)
                     val body2' = unsafeReplace(qvar2,AT.makeVar fresh_var_2,body2)
		     val uvars' = uvars
                 in 
                     f(body1',body2',sub,sort_sub,uvars',fresh_var_2::banned)
                 end
           | f(p1 as eGen({qvar=qvar1,body=body1,...}),p2 as eGen({qvar=qvar2,body=body2,...}),
	   sub,sort_sub,uvars,banned) = 
                 let val fresh_var_name = ATV.freshVarName()
		     val qvar_pat_sort = ATV.getSort(qvar2)
		     val qvar_obj_sort = ATV.getSort(qvar1)
		     val sort_sub' = F.matchModuloSub(qvar_obj_sort,qvar_pat_sort,sort_sub)
		     val sort_sub = FTerm.composeSubs(sort_sub',sort_sub)
                     val fresh_var_1 = ATV.applySortSub(sort_sub,ATV.athTermVarWithSort(fresh_var_name,qvar_obj_sort))
                     val fresh_var_2 = ATV.applySortSub(sort_sub,ATV.athTermVarWithSort(fresh_var_name,qvar_pat_sort))
                     val body1' = unsafeReplace(qvar1,AT.makeVar fresh_var_1,body1)
                     val body2' = unsafeReplace(qvar2,AT.makeVar fresh_var_2,body2)
		     val uvars' = uvars
                 in 
                     f(body1',body2',sub,sort_sub,uvars,fresh_var_2::banned)
                 end
           | f(p1 as eGenUnique({qvar=qvar1,body=body1,...}),p2 as eGenUnique({qvar=qvar2,body=body2,...}),
	   sub,sort_sub,uvars,banned) = 
                 let val fresh_var_name = ATV.freshVarName()
                     val fresh_var_1 = ATV.athTermVarWithSort(fresh_var_name,ATV.getSort(qvar1))
                     val fresh_var_2 = ATV.athTermVarWithSort(fresh_var_name,ATV.getSort(qvar2))
                     val body1' = unsafeReplace(qvar1,AT.makeVar fresh_var_1,body1)
                     val body2' = unsafeReplace(qvar2,AT.makeVar fresh_var_2,body2)
                 in 
                     f(body1',body2',sub,sort_sub,uvars,fresh_var_2::banned)
                 end
           | f(_) = NONE
         and fLst([],[],sub,sort_sub,uvars,banned) = SOME(sub,sort_sub) 
           | fLst(p1::rest1,p2::rest2,sub,sort_sub,uvars,banned) = 
               (case f(p1,p2,sub,sort_sub,uvars,banned) of
                   SOME(sub',sort_sub') => let 
                                               val sub'' = AT.composeSubs(sub',sub)
                                               val sort_sub'' = FTerm.composeSubs(sort_sub',sort_sub)
                                           in
                                             fLst(rest1,rest2,sub'',sort_sub'',uvars,banned)
                                           end
                 | _ => NONE)
           | fLst(_) = NONE
     in
        ((fn (p1,p2,sub,sort_sub,uvars) => (f(p1,p2,sub,sort_sub,uvars,[]) handle _ => NONE)),
         (fn (p1_lst,p2_lst,sub,sort_sub,uvars) => ((fLst(p1_lst,p2_lst,sub,sort_sub,uvars,[])) handle _ => NONE)))
     end

fun matchRW(p,q,uvars) = (case matchRWraw(p,q,AT.empty_sub,FTerm.empty_sub,uvars) of 
                             SOME(sub,_) => SOME(sub)
                           | _ => NONE)

fun matchLstRW(L1,L2,uvars) = (case matchLstRWraw(L1,L2,AT.empty_sub,FTerm.empty_sub,uvars) of 
                                  SOME(sub,_) => SOME(sub)
                                 | _ => NONE)

fun match(p1,p2) = matchRW(p1,p2,freeVars p2)

fun matchLst(L1,L2) = matchLstRW(L1,L2,freeVarsLst L2)

fun unify(p1,p2) = NONE

val getDisjunctsWithoutDups = 
        let val count = ref 0 
            val hashFun = Basic.hashInt
            val equalityFun = op=
            val mtable: (int,prop list) HashTable.hash_table = HashTable.mkTable(hashFun, equalityFun) (157,PropHashConsEx)
            fun f(disj({args,...})) = args@(Basic.flatten(List.map f args))
              | f(p) = [p]
        in 
           (fn p =>  (case getCode(p) of
                         ref(SOME(i)) => (case (HashTable.find mtable i) of
                                            SOME(res) => res
                                          | _ => let val res = Basic.removeDuplicatesEq(f p,alEq)
                                                     val _ = HashTable.insert mtable (i,res)
                                                 in
                                                    res
                                                 end)
                       | _ => Basic.removeDuplicatesEq(f p,alEq)))
        end

fun makePolyTPTPProp(P) = 
  let val P' = alphaRename(P)
      val printer = F.makePolyVarSortPrinter()
      val fvars = freeVars(P')
      val (lp,rp,comma,blank) = ("(",")",","," ")
      val printer = F.makePolyVarSortPrinter()     
      fun f(P_in as atom({term=t,...}),sort_vars) = 
            let val bc = isBooleanConstant(P_in)
		val is_bc = not(bc = "") 
            in
	       if is_bc then ("$"^bc,[]) else
	       (case AthTerm.isApp(t) of
                  SOME(g,[]) => let val str = "c"^(Basic.fsymRenamer(MS.name(g)))
                                in (str,sort_vars) end
                | SOME(g,args) => let val (arg_strings,sort_vars') = AT.makePolyTPTPTermLst(args,fvars,printer,sort_vars)
                                      val is_eq = msymEq(g,N.mequal_logical_symbol)
				      val gname = if is_eq then "=" else "f"^(Basic.fsymRenamer(MS.name(g)))
                                      val str = if is_eq then 
                                                   (case arg_strings of 
                                                       [s1,s2] => lp^s1^blank^gname^blank^s2^rp)
                                                else gname^lp^(Basic.printListStr(arg_strings,fn x => x,comma))^rp 
			          in
                                    (str,sort_vars')
		                  end
                | _ => (case AT.isVarOpt(t) of
                           SOME(v) => if Basic.isMemberEq(v,fvars,ATV.athTermVarEq) then
                                         let val name = "c"^(Basic.varRenamer(ATV.name(v)))
                                         in
					    (name,sort_vars)
				         end
                                       else
                                       raise SpassTranslation("Quantified Boolean variables are not "^
						              "allowed in TPTP formulas.")
                        | _ => raise Basic.Never))
             end
        | f(neg({arg,...}),sort_vars) = let val (body_str,sort_vars') = f(arg,sort_vars)
                                        in (" ~ ("^body_str^rp,sort_vars') end
        | f(conj({args,...}),sort_vars) = fLst(args," & ",sort_vars)
        | f(disj({args,...}),sort_vars) = fLst(args," | ",sort_vars)
        | f(cond({ant=P1,con=P2,...}),sort_vars) =  let val (str1,sort_vars') = f(P1,sort_vars)
                                                        val (str2,sort_vars'') = f(P2,sort_vars')
                                                    in 
                                                      (lp^str1^" => "^str2^rp,sort_vars'')
                                                    end
        | f(biCond({left=P1,right=P2,...}),sort_vars) = let val (str1,sort_vars') = f(P1,sort_vars)
                                                            val (str2,sort_vars'') = f(P2,sort_vars')
                                                        in 
                                                            (lp^str1^" <=> "^str2^rp,sort_vars'')
                                                        end 
        | f(uGen({qvar,body,...}),sort_vars) = let val (body_str,sort_vars') = f(body,sort_vars)
                                               in
                                                  ("! [ X"^(AthTerm.makeConservativeName(ATV.name(qvar)))^" ] : ( "^body_str^rp,sort_vars')
                                               end
        | f(eGen({qvar,body,...}),sort_vars) = let val (body_str,sort_vars') = f(body,sort_vars)
                                               in
                                                  ("? [ X"^(AthTerm.makeConservativeName(ATV.name(qvar)))^" ] : ( "^body_str^")",sort_vars')
                                               end
        | f(eGenUnique({qvar,body,...}),_) = 
		Basic.failLst(["Translation to TPTP failed on exists-unique sentence."])
      and fLst([],_,sort_vars) = ("",sort_vars)
        | fLst([P],_,sort_vars) = f(P,sort_vars)
        | fLst(P1::(rest as _::_),sep,sort_vars) = let val (str1,sort_vars') = f(P1,sort_vars)
                                                       val (str2,sort_vars'') = fLst(rest,sep,sort_vars')
                                                   in
                                                     (lp^str1^sep^str2^rp,sort_vars'')
                                                   end
      and makeugen([],p) = p
        | makeugen(v::rest,p) = let val p' = makeugen(rest,p)
                                in 
                                    lp^"! [ "^v^" ] : ( "^p'^rp^rp 
                                end
    val (pstr,sort_vars) = f(P',[])     
    val sort_vars' = Basic.removeDuplicatesEq(sort_vars,op=)
    val pstr' = makeugen(sort_vars',pstr)
  in
    pstr' 
  end

fun makeSubsortAxioms(fsymbols,osorts,free_vars,format) = 
  let val (lp,rp,comma) = ("(",")",",")
      val fsymbols' = Basic.removeDuplicatesEq(fsymbols,msymEq)
      fun sortConArity(s) = (case MS.lookUp(!(Data.structure_and_domain_arities),s) of
                                SOME(i) => i 
                              | _ => 0)
      val makeSubSortProp = (fn (s1:ModSymbol.mod_symbol,s2:ModSymbol.mod_symbol) => 
                                           let val pname = "psubsort"
                                               val arity = sortConArity(s1)
                                               val range = Basic.fromI2N(1,arity)
                                               val variable_terms1 = map (fn i => "X"^(Int.toString i)) range
                                               val variable_terms2 = map (fn i => "Y"^(Int.toString i)) range 
                                               val variable_terms = variable_terms1@variable_terms2 
                                               val var_term_pairs = Basic.zip(variable_terms1,variable_terms2)
                                               val sort1 = (F.atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(MS.name(s1))))
                                               val sort2 = (F.atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(MS.name(s2))))
                                               val term1 = if arity < 1 then sort1 else
                                                              sort1^lp^(Basic.printListStr(variable_terms1,fn x => x,comma))^rp
                                               val term2 = if arity < 1 then sort2 else
                                                              sort2^lp^(Basic.printListStr(variable_terms2,fn x => x,comma))^rp
                                               fun makeAntecedent([(x,y)]) = pname^lp^x^comma^y^rp
                                                 | makeAntecedent((x,y)::more) = "and"^lp^pname^lp^x^comma^y^rp^comma^(makeAntecedent more)^rp
                                               fun makeConsequent() = pname^"("^term1^","^term2^")"
                                               val if_sign = if format = "spass" then "implies" else " => " 
                                               fun makeConditional() = if format = "spass" then 
                                                                          if_sign^lp^(makeAntecedent var_term_pairs)^comma^(makeConsequent())^rp
                                                                       else lp^(makeAntecedent var_term_pairs)^if_sign^(makeConsequent())^rp
                                           in 
                                             if arity < 1 then makeConsequent() else makeSpassUgen(variable_terms,makeConditional(),format)
                                           end)
      val osort_props = let val facts = SortOrder.organize(osorts)
                        in 
                           List.map makeSubSortProp facts
                        end 
      val positive_sorts = List.filter (fn s => sortConArity(s) > 0) osorts
      val osort_props' = List.map makeSubSortProp (Basic.zip(positive_sorts,positive_sorts))
      val ref_axiom = if format = "spass" then "forall([X],psubsort(X,X))"
                      else " ! [ X ] : (psubsort(X,X)) "
      val subsort_axiom_1 = if format = "spass" then "forall([X1],forall([X2],phas_sort(st(X1,X2),X1)))"
                            else "! [X1] : ( ! [X2] : (phas_sort(st(X1,X2),X1)))"
      fun makeHasSortAxiomForFVar(fvar) = 
           let val var_name = "c"^(Basic.varRenamer(ATV.name(fvar)))
               val sort = ATV.getSort(fvar)
           in
             (if not(F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(sort) orelse ATV.isPoly(fvar)) then ""
              else let val printer = F.makePolyVarSortPrinter()     
                       val (sort_str,{vars=sort_vars,fsyms,...}) = F.toPolyString(sort,printer)
                       val blank_term = var_name
                       val term = "st"^lp^sort_str^comma^blank_term^rp
                       val body = "phas_sort"^lp^term^comma^sort_str^rp
                       val prop = makeSpassUgen(sort_vars,body,format)
                   in
                      prop 
                   end) handle _ => ""
           end 
      fun makeHasSortAxiom(fsym:ModSymbol.mod_symbol) = 
                                   let val fsym_str = MS.name(fsym)
                                       val clist = explode fsym_str 
                                       val parseNum = A.parseNumberKind
                                       val fsym_str' = implode(tl(clist))
                                       val number_kind' = if null(clist) then 0 else parseNum(fsym_str')
                                       val number_kind = if not(null(clist)) andalso not(hd(clist) = #"c") then 0
                                                         else (if number_kind' > 0 then number_kind' else
                                                                  (case String.tokens (fn x => x = #"_") fsym_str' of
                                                                      [s1,s2] => if (parseNum(s1) = 1 andalso parseNum(s2) = 1) then 2 else 0
                                                                    | _ => 0))
                                       
                                       val printer = F.makePolyVarSortPrinter()     
                                       
                                   in
                                         (case number_kind of
                                             1 => let val sort_str = (F.atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(MS.name(Names.mint_sort_symbol))))
                                                      val term = "st"^lp^sort_str^comma^fsym_str^rp
                                                  in
                                                     "phas_sort"^lp^term^comma^sort_str^rp
                                                  end
                                           | 2 => let val sort_str = (F.atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(MS.name(Names.mreal_sort_symbol))))
                                                      val term = "st"^lp^sort_str^comma^fsym_str^rp
                                                  in
                                                     "phas_sort"^lp^term^comma^sort_str^rp
                                                  end
                                           | _ =>                                              
                                             let val (arg_sorts,result_sort,is_poly,has_pred_based_sorts) = Data.getSignature(fsym)
                                             in
                                              if Basic.exists(result_sort::arg_sorts,F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt) 
                                                 orelse is_poly 
                                                 then 
                                                 let val (sort_str,{vars=sort_vars,fsyms,...}) = F.toPolyString(result_sort,printer)
                                                      val arity = (case Data.isTermConstructor(fsym) of
                                                                      SOME(i) => i    
                                                                    | _ => 0)
                                                      val arg_vars = List.map (fn i => "X"^(Int.toString i)) (Basic.fromI2N(1,arity)) 
                                                      val arg_sort_strings = List.map (fn sort => #1(F.toPolyString(sort,printer))) arg_sorts
                                                      val arg_terms = List.map (fn (sort,arg_var) => "st"^lp^sort^comma^arg_var^rp) 
                                                                               (Basic.zip(arg_sort_strings,arg_vars))
                                                      val is_equality = msymEq(fsym,Names.mequal_logical_symbol)
                                                      val eq_sign = if format = "spass" then "equal" else " = "
                                                      val fname = if arity > 0 then 
                                                                     (if is_equality then 
                                                                         eq_sign else "f"^(Basic.fsymRenamer(fsym_str)))
                                                                  else "c"^(Basic.fsymRenamer(fsym_str))
                                                      val blank_term = if arity = 0 then fname
                                                                       else (if (is_equality andalso not(format="spass")) then
                                                                                (case arg_terms of 
                                                                                    [s1,s2] => lp^s1^blank^fname^blank^s2^rp)
                                                                             else fname^lp^(Basic.printListStr(arg_terms,fn x => x,comma))^rp)
                                                      val term = "st"^lp^sort_str^comma^blank_term^rp
                                                      val body = "phas_sort"^lp^term^comma^sort_str^rp
                                                      val prop = makeSpassUgen(sort_vars@arg_vars,body,format)
                                                  in
                                                     prop
                                                  end
                                              else ""
                                             end) 
                                   end handle _ => ""
      val has_sort_axioms_1 = (map makeHasSortAxiomForFVar free_vars)
      val has_sort_axioms_2 = (map makeHasSortAxiom fsymbols')
      val has_sort_axioms = has_sort_axioms_1@has_sort_axioms_2 
      val subsort_axiom_2 = if format = "spass" then
                               "forall([X1],forall([X2],forall([X3],implies(and(psubsort(X2,X3),phas_sort(st(X2,X1),X2)),"^
                                "equal(st(X2,X1),st(X3,X1))))))"
                            else " ! [X1] : ( ! [X2] : ( ! [X3]: ((psubsort(X2,X3) & phas_sort(st(X2,X1),X2)) => (st(X2,X1) = st(X3,X1)))))"
      val subsort_axioms = subsort_axiom_2::has_sort_axioms 
  in 
    ref_axiom::(subsort_axioms@osort_props'@osort_props)
  end

val fsym_def_table : {eval_proc_name:string, 
                      eval_proc_name_with_full_mod_path:string,
                      evaluator_being_defined: bool ref, 
		      guard_syms: msymbol list, 
		      code:string ref,
		      red_code:string ref,
		      dcode:string ref, 
                      obsolete_axioms: prop list,
                      needed_by:msymbol list,
		      occurring_syms: msymbol list, 
		      defining_equations_finished: bool ref,
		      defining_equations: prop list,
		      bicond_sources: (prop * prop) list} ModSymbol.htable = ModSymbol.makeHTableWithInitialSize(113)

exception HT

val proc_name_table: (string,msymbol) HashTable.hash_table = HashTable.mkTable(HashString.hashString, op=) (79,HT)

val module_ab_table: (string,((prop,string option) HashTable.hash_table)) HashTable.hash_table = 
   let val _ = ()
   in
      HashTable.mkTable(HashString.hashString, op=) (23,HT)
   end

fun addToModuleAb(mod_path,p,string_opt) = 
  let val module_name = Basic.printListStr(mod_path,Symbol.name,".")
  in
    (case (HashTable.find module_ab_table module_name) of 
        SOME(ht) => (HashTable.insert ht (p,string_opt))
      | _ => let val ht:(prop,string option) HashTable.hash_table = HashTable.mkTable(hash, alEq) (23,HT)
                 val _ = (HashTable.insert ht (p,string_opt))
             in
               (HashTable.insert module_ab_table (module_name,ht))
            end)
  end

fun removeFromModuleAb(mod_path,p) =  
  let val module_name = Basic.printListStr(mod_path,Symbol.name,".")
  in
    (case (HashTable.find module_ab_table module_name) of 
        SOME(ht:(prop,string option) HashTable.hash_table) => (HashTable.remove ht p;())
      | _ => ())
  end

fun removeFromAllModuleAbs(p) =  
    let val mod_names:string list = (map (fn (s,_) => s)  (HashTable.listItemsi module_ab_table))
    in
     List.app 
     (fn mod_name => 
         (case (HashTable.find module_ab_table mod_name) of 
            SOME(ht:(prop,string option) HashTable.hash_table) => ((HashTable.remove ht p;()) handle _ => ())
          | _ => ()))
     mod_names
    end

fun isEvalProcName(name_str) = 
     if (String.sub(name_str,String.size(name_str)-1) = Names.standardEvalProcNameTailCharacter) then
        (HashTable.find proc_name_table name_str)
     else NONE

val _ = MS.insert(fsym_def_table,N.maddition_symbol,{eval_proc_name="+'",eval_proc_name_with_full_mod_path="+'",
    guard_syms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],obsolete_axioms=[],
                  defining_equations=[],
		  defining_equations_finished = ref(false),
		  bicond_sources=[],evaluator_being_defined=ref(true)})


val _ = MS.insert(fsym_def_table,N.msubtraction_symbol,{eval_proc_name="-'",eval_proc_name_with_full_mod_path="-'",guard_syms=[],obsolete_axioms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[], 
    defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mmultiplication_symbol,{eval_proc_name="*'",eval_proc_name_with_full_mod_path="*'",guard_syms=[],obsolete_axioms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mdivision_symbol,{eval_proc_name="/'",eval_proc_name_with_full_mod_path="/'",guard_syms=[],obsolete_axioms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],
    defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mequal_logical_symbol,{eval_proc_name="='",eval_proc_name_with_full_mod_path="='",obsolete_axioms=[],guard_syms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],
    defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mformal_less_symbol,{eval_proc_name="<'",eval_proc_name_with_full_mod_path="<'",obsolete_axioms=[],guard_syms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mformal_greater_symbol,{eval_proc_name=">'",eval_proc_name_with_full_mod_path=">'",obsolete_axioms=[],guard_syms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mformal_leq_symbol,{eval_proc_name="<='",eval_proc_name_with_full_mod_path="<='",obsolete_axioms=[],guard_syms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val _ = MS.insert(fsym_def_table,N.mformal_geq_symbol,{eval_proc_name=">='",eval_proc_name_with_full_mod_path=">='",obsolete_axioms=[],guard_syms=[],occurring_syms=[],code=ref(""),red_code=ref(""),dcode=ref(""),needed_by=[],defining_equations=[],defining_equations_finished = ref(false),
    bicond_sources=[],evaluator_being_defined=ref(true)})

val structure_equality_table: (term * term -> prop) ModSymbol.htable = ModSymbol.makeHTableWithInitialSize(23)

fun tc(f) = 
  let fun loop(f,A) = 
              (case MS.find(fsym_def_table,f) of
                  SOME({guard_syms,occurring_syms,...}) => 
                       let val syms = occurring_syms@guard_syms
                           val A' = MS.union(A,MS.addLst(syms,MS.empty_set))
                       in 
                          if MS.equal(A,A') then A else loopLst(syms,A')
                       end
                | _ => A)
       and loopLst([],A) = A
         | loopLst(f::more,A) = loopLst(more,loop(f,A))
  in 
     loop(f,MS.empty_set)
  end

fun tc'(f) =               
     (case MS.find(fsym_def_table,f) of
        SOME({occurring_syms,...}) => let fun pred(g) = MS.isMember(f,tc(g))
                                      in  
                                         MS.addLst(List.filter pred (MS.listModSymbols(tc(f))),MS.empty_set)
                                      end 
      | _ => MS.empty_set)

val sort_predicate_table: (MS.mod_symbol, MS.mod_symbol * (AT.term list -> prop)) HashTable.hash_table =
      HashTable.mkTable(fn msym => Basic.hashInt(MS.code(msym)),
                       (fn (msym,msym') => MS.modSymEq(msym,msym')))
                       (29,Basic.Never)   

fun evalCanonical(t,p) = false

(*********************************************************************************************************************
					PROPOSITIONAL SATISFIABILITY 
*********************************************************************************************************************)

datatype cnf_array_entry = 

   atomic_entry of {p:prop} | 

   complex_entry of {definition_clauses: clauses,      (** e.g. x_37 <==> x_32 \/ x_10, but as a list of clauses **)
                     sentential_constructor: int,      (** 0 for not, 1 for and, 2 for or, 3 for if, 4 for iff   **)
                     arguments: int list,              (** the array indices of the subsentences                 **)
		     is_flat_disjunction: bool}		    

fun makeAssignment(asgn_line,
                   inverse_hash_table:(int,prop) HashTable.hash_table,
		   out_hash_table,
		   transformProp,
		   transformBool) = 

              let val minus_sign = #"-"
                  fun processStingVal(str) = 
                         let val (var_index_str,value) = 
                                     if String.sub(str,0) = minus_sign then (str,false) else (str,true)
                             val var_index = (case Int.fromString(var_index_str) of
                                                 SOME(i) => (if i < 0 then ~i else i) | _ => 0)
                         in
                            (case (HashTable.find inverse_hash_table var_index) of 
                                SOME(p) => (HashTable.insert out_hash_table (transformProp(p),transformBool(value)))
                              | _ => ())
                         end
                 fun pred(c) = c = #" " orelse c = #"\n"
                 val strings = String.tokens pred asgn_line
                 val _ = List.app processStingVal strings
              in
                 out_hash_table
              end

fun getMiniSatResult(minisat_file_stream,
                     inverse_hash_table:(int,prop) HashTable.hash_table,
		     out_hash_table,
		     transformProp,
		     transformBool) = 

  let val first_line = TextIO.inputLine(minisat_file_stream)
  in
     (case (String.tokens (fn c => c = #" " orelse c = #"\n") first_line) of 
        ("UNSAT"::_) => NONE
       | _ => let val asgn_line = TextIO.inputLine(minisat_file_stream)
              in 
                 SOME(makeAssignment(asgn_line,
		                     inverse_hash_table,
				     out_hash_table,
				     transformProp,
				     transformBool))
              end)
  end

fun nnf(p) = 
  let fun f(neg({arg,...}),negated) = f(arg,not negated)
        | f(conj({args,flags,fvars,poly_constants,hash_code,...}),negated) =	
	     if negated then 
	        let val args' = map (fn q => f(q,negated)) args
                in
 		   disj({args=args',
                         flags=flags,
                	 fvars=fvars,
			 poly_constants=poly_constants,
			 hash_code=Basic.hashTwoWords(or_code,Basic.hashWordList(args',fastHash))})
	        end
	     else 	        
	         let val args' = map (fn q => f(q,negated)) args
		 in
                    conj({args=args',
		          flags=flags,
			  fvars=fvars,
			  poly_constants=poly_constants,
			  hash_code=Basic.hashTwoWords(and_code,Basic.hashWordList(args',fastHash))})
                 end
        | f(disj({args,flags,fvars,poly_constants,hash_code,...}),negated) =	
	     if negated then 
	        let val args' = map (fn q => f(q,negated)) args
                in
 		   conj({args=args',
                         flags=flags,
                	 fvars=fvars,
			 poly_constants=poly_constants,
			 hash_code=Basic.hashTwoWords(and_code,Basic.hashWordList(args',fastHash))})
	        end
	     else 	        
	         let val args' = map (fn q => f(q,negated)) args
		 in
                    disj({args=args',
		          flags=flags,
			  fvars=fvars,
			  poly_constants=poly_constants,
			  hash_code=Basic.hashTwoWords(or_code,Basic.hashWordList(args',fastHash))})
                 end
        | f(cond({ant,con,flags,fvars,poly_constants,hash_code}),negated) =  
	     let val neg_ant = neg({arg=ant,
			            flags=getFlags(ant),
				    fvars=freeVars(ant),
			  	    poly_constants=getPolyConstants(ant),
			  	    hash_code=Basic.hashTwoWords(neg_code,Basic.hashWordList([ant],fastHash))})
                  val args' = [neg_ant,con] 				     
             in
	       f(disj({args=args',
	               flags=flags,
	               fvars=fvars,
		       poly_constants=poly_constants,
	               hash_code=Basic.hashTwoWords(or_code,Basic.hashWordList(args',fastHash))}),
		       negated)
             end
        | f(biCond({left,right,flags,fvars,poly_constants,hash_code}),negated) =  
	     let val conj1_args = [left,right]
                 val conj1 = conj({args=conj1_args,
	                           flags=flags,
				   fvars=fvars,
				   poly_constants=poly_constants,
				   hash_code=Basic.hashTwoWords(and_code,Basic.hashWordList(conj1_args,fastHash))})

                 val left_neg = neg({arg=left,
	                      	     flags=getFlags(left),	
				     fvars=freeVars(left),
				     poly_constants=getPolyConstants(left),
				     hash_code=Basic.hashTwoWords(neg_code,Basic.hashWordList([left],fastHash))})
                 val right_neg = neg({arg=right,
	                      	     flags=getFlags(right),	
				     fvars=freeVars(right),
				     poly_constants=getPolyConstants(right),
				     hash_code=Basic.hashTwoWords(neg_code,Basic.hashWordList([right],fastHash))})
                 val conj2_args = [left_neg,right_neg] 				     
                 val conj2 = conj({args=conj2_args,
		                   flags=flags,
				   fvars=fvars,
				   poly_constants=poly_constants,
				   hash_code=Basic.hashTwoWords(and_code,Basic.hashWordList(conj2_args,fastHash))})
                  val args' = [conj1,conj2]			   
            in
               f(disj({args=args',
	               flags=flags,
		       fvars=fvars,
		       poly_constants=poly_constants,
		       hash_code=Basic.hashTwoWords(and_code,Basic.hashWordList(args',fastHash))}),
		 negated)
            end				  
       | f(uGen({qvar,body,flags,fvars}),negated) = 
            uGen({qvar=qvar,body=f(body,negated),flags=flags,fvars=fvars})
       | f(eGen({qvar,body,flags,fvars}),negated) = 
            eGen({qvar=qvar,body=f(body,negated),flags=flags,fvars=fvars})
       | f(eGenUnique({qvar,body,flags,fvars}),negated) = 
            eGenUnique({qvar=qvar,body=f(body,negated),flags=flags,fvars=fvars})
       | f(p as atom({term,hash_code=atom_hash_code,flags}),negated) = 
              if negated then 
                   neg({arg=p,
                        flags=flags,
		        fvars=AT.getVars(term),
			hash_code=Basic.hashTwoWords(neg_code,atom_hash_code),
			poly_constants=AT.getPolyConstants(term)})
              else 
                  p
  in
    f(p,false)
  end 

fun nnfNoQuants(p) = 
  let fun f(neg({arg,...}),negated,n) = f(arg,not negated,n)
        | f(conj({args,flags,fvars,poly_constants,hash_code,...}),negated,n) =	
            let val args = getConjunctsLst(args)
                val (args',n') = fLst(args,negated,[],n)
            in
     	       if negated then 
 		   (disj({args=args',
                         flags=flags,
                	 fvars=fvars,
			 poly_constants=poly_constants,
			 hash_code=hash_code}),1+n')
  	       else 	        
                   (conj({args=args',
 	                  flags=flags,
		  	  fvars=fvars,
		 	  poly_constants=poly_constants,
			  hash_code=hash_code}),1+n')
            end
        | f(p as disj({args,flags,fvars,poly_constants,hash_code,...}),negated,n) =	
            let val args = getDisjuncts(p)
	        val (args',n') = fLst(args,negated,[],n)
	    in
	       if negated then
 		   (conj({args=args',
                          flags=flags,
                 	  fvars=fvars,
		 	  poly_constants=poly_constants,
			  hash_code=hash_code}),1+n')
  	        else 	        
                   (disj({args=args',
		          flags=flags,
			  fvars=fvars,
			  poly_constants=poly_constants,
			  hash_code=hash_code}),1+n')
            end
        | f(cond({ant,con,flags,fvars,poly_constants,hash_code}),negated,n) =  
	     let val neg_ant = neg({arg=ant,
			            flags=flags,
				    fvars=fvars,
			  	    poly_constants=poly_constants,
			  	    hash_code=hash_code})
                  val args' = [neg_ant,con] 				     
             in
	       f(disj({args=args',
	               flags=flags,
	               fvars=fvars,
		       poly_constants=poly_constants,
	               hash_code=hash_code}),
		       negated,n)
             end

        | f(biCond({left,right,flags,fvars,poly_constants,hash_code}),negated,n) =  
	     let val cond1 = cond({ant=left,con=right,flags=flags,fvars=fvars,poly_constants=poly_constants,hash_code=hash_code})
                 val cond2 = cond({ant=right,con=left,flags=flags,fvars=fvars,poly_constants=poly_constants,hash_code=hash_code})
                 val conjunction = conj({args=[cond1,cond2],flags=flags,fvars=fvars,poly_constants=poly_constants,hash_code=hash_code})
             in
                f(conjunction,negated,n)
             end
       | f(p as atom({term,hash_code,flags}),negated,n) = 
              if negated then 
                   (neg({arg=p,flags=flags,fvars=[],hash_code=hash_code,poly_constants=[]}),2+n)
              else 
                  (p,1+n)
       | f(p,negated,n) =
              if negated then 
                   (neg({arg=p,flags=defaultFlags(),fvars=[],hash_code=neg_code,poly_constants=[]}),2+n)
              else 
                  (p,1+n)
    and fLst([],_,results,n) = (rev(results),n)
      | fLst(p::more,negated,results,n) = 
                let val (p',n') = f(p,negated,n)
                in
                   fLst(more,negated,p'::results,n')
                end
   val final_res as (res,_) = f(p,false,0)
  in
    final_res
  end 

fun clausalConjunctiveDef(tseitin_var_index,arg_indices) = 

(** 
  Polarity is always positive (since we're assuming NNF), so we 
  produce CNF for something like x_4 ==> x_0 & x_1 & x_2.  
**)

let val negated_ant = ~ tseitin_var_index
in
   map (fn i => [negated_ant,i]) arg_indices
end

fun clausalDisjunctiveDef(tseitin_var_index,arg_indices) = 
(*** 
Polarity is always positive (since we're assuming NNF), so we 
produce CNF for something like x_4 ==> x_0 | x_1 | x_2.  
***)
  [(~tseitin_var_index)::arg_indices]
    
fun isAtomic(i,A) = 
  (i < 0) orelse (case Unsafe.Array.sub(A,i) of atomic_entry(_) => true | _ => false)

fun isFlatDisjunction(i,A) = 
 if (i < 0) then NONE
 else
  (case Unsafe.Array.sub(A,i) of 
     complex_entry({is_flat_disjunction,arguments,...}) => if is_flat_disjunction then SOME(arguments) else NONE
   | _ => NONE)

fun getDisjClauses(tseitin_var_index,arg_indices,A) = 
  let val already_seen: (int,bool) HashTable.hash_table = HashTable.mkTable(Basic.hashInt,op=) (100,Basic.Never) 
      fun loop([],results,good_indices,all_atoms) = ([(~tseitin_var_index)::results],good_indices,all_atoms)
        | loop(i::more,results,good_indices,all_atoms) = 
       (case (HashTable.find already_seen i) of
         NONE => 
           let val _ = HashTable.insert already_seen (i,true)
           in     
 	     (case isFlatDisjunction(i,A) of
                 SOME(atom_indices) => loop(more,atom_indices@results,good_indices,false)
               | _ => loop(more,i::results,i::good_indices,isAtomic(i,A) andalso all_atoms))
           end
      | _ => loop(more,results,good_indices,all_atoms))
  in
    loop(arg_indices,[],[],true)
  end

fun getDisjClausesFaster(tseitin_var_index,arg_indices,A) = 
  let 
      fun loop([],results,good_indices,all_atoms) = ([(~tseitin_var_index)::results],good_indices,all_atoms)
        | loop(i::more,results,good_indices,all_atoms) = 
 	     (case isFlatDisjunction(i,A) of
                 SOME(atom_indices) => loop(more,atom_indices@results,good_indices,false)
               | _ => loop(more,i::results,i::good_indices,isAtomic(i,A) andalso all_atoms))
  in
    loop(arg_indices,[],[],true)
  end

fun getConjClauses(tseitin_var_index,arg_indices,A) = 
  let val negated_tseitin = ~tseitin_var_index
      val already_seen: (int,bool) HashTable.hash_table = HashTable.mkTable(Basic.hashInt,op=) (100,Basic.Never)
      fun loop([],results,good_indices) = (results,good_indices)
        | loop(i::more,results,good_indices) = 
       (case (HashTable.find already_seen i) of
         NONE => 
           let val _ = HashTable.insert already_seen (i,true)
           in
	    (case isFlatDisjunction(i,A) of
                SOME(atom_indices) => 
		      let val new_clause = negated_tseitin::atom_indices
                      in
                         loop(more,new_clause::results,good_indices)
                      end
              | _ => let val new_clause = [negated_tseitin,i]
                     in
                       loop(more,new_clause::results,i::good_indices)
                     end)
           end
     | _ => loop(more,results,good_indices))
  in
    loop(arg_indices,[],[])
  end
                   
fun getConjClausesFaster(tseitin_var_index,arg_indices,A) = 
  let val negated_tseitin = ~tseitin_var_index
      fun loop([],results,good_indices) = (results,good_indices)
        | loop(i::more,results,good_indices) = 
	    (case isFlatDisjunction(i,A) of
                SOME(atom_indices) => 
		      let val new_clause = negated_tseitin::atom_indices
                      in
                         loop(more,new_clause::results,good_indices)
                      end
              | _ => let val new_clause = [negated_tseitin,i]
                     in
                       loop(more,new_clause::results,i::good_indices)
                     end)
  in
    loop(arg_indices,[],[])
  end

(*==========================================================================

The input sentence p must be in NNF. Use nnf to do the conversion. 

The input array A of cnf_entries will be updated as needed by the conversion
process. 

The table ht maps sentential-constructor codes and integer arguments
to integer (array) indices, memoizing previously seen subtrees.

The atom_table and inverse_atom_table are used to convert from
atomic sentences in the given sentence p to integer indices
and conversely. 

============================================================================*)

fun convertToCnf(p:prop,
                 A: cnf_array_entry Array.array,
		 ht: (int * int list,int) HashTable.hash_table,
		 atom_table: (prop,int) HashTable.hash_table,
		 inverse_atom_table: (int,prop) HashTable.hash_table,
		 index_counter: int ref) = 

let fun f(conj({args as first_arg::more_args,...}))  = 
            let val first_arg_index = f(first_arg)
                val (arg_indices,all_same) = fLst(more_args,[first_arg_index],first_arg_index,true)
            in
              if all_same then hd(arg_indices) else 
                      let val key = (1,ListMergeSort.sort Int.< arg_indices)
                      in
                        (case  (HashTable.find ht key) of
                            SOME(i) => i
                          | _ =>  let val res = Basic.returnAndInc(index_counter)
		                      val (def_clauses,good_indices) = getConjClauses(res,arg_indices,A)
                                      val new_entry = complex_entry{definition_clauses = def_clauses,
	  	  	  	     			            sentential_constructor = 1,
							            arguments = good_indices,
							            is_flat_disjunction=false};
                                      val _ = HashTable.insert ht (key,res)
			              val _ = Unsafe.Array.update(A,res,new_entry)
                                   in
		                      res
                                   end)        
                      end
            end
      | f(disj({args as first_arg::more_args,...}))  = 
            let val first_arg_index = f(first_arg)
                val (arg_indices,all_same) = fLst(more_args,[first_arg_index],first_arg_index,true)
            in
              if all_same then hd(arg_indices) else 
                 let val key = (2,ListMergeSort.sort Int.< arg_indices)
                 in
                    (case (HashTable.find ht key) of
                        SOME(i) => i
                      | _ =>  let val res = Basic.returnAndInc(index_counter)
		                  val (def_clauses,good_indices,is_flat_disj) = getDisjClauses(res,arg_indices,A)
                                  val new_entry = complex_entry{definition_clauses = def_clauses,
	  	  	    	       			        sentential_constructor = 2,
							        arguments = good_indices,
							        is_flat_disjunction=is_flat_disj };
                                  val _ = HashTable.insert ht (key,res)
			          val _ = Unsafe.Array.update(A,res,new_entry)
                              in
		                res
                              end)
                 end
            end
      | f(p as neg({arg,...})) = 
           (case (HashTable.find atom_table arg) of
               SOME(i) => ~i
             | _ => let val res = Basic.returnAndInc(index_counter)
                        val _ = HashTable.insert atom_table (arg,res)
                        val _ = HashTable.insert inverse_atom_table (res,arg)
                        val _ = Unsafe.Array.update(A,res,atomic_entry({p=arg}))
			val final_res = ~res
                    in
		       final_res 		       
                    end)
      | f(p as any_other_prop) = 
           (case (HashTable.find atom_table p) of
               SOME(i) => i
             | _ => let val res = Basic.returnAndInc(index_counter)
                        val _ = HashTable.insert atom_table (p,res)
                        val _ = HashTable.insert inverse_atom_table (res,p)
                        val _ = Unsafe.Array.update(A,res,atomic_entry({p=any_other_prop}))
                    in
		       res
                    end)
   and fLst([],results,_,all_same) = (rev results,all_same)
     | fLst(p::more,results,current,all_same) = 
         let val i = f(p)
         in
	    if (i = current) then
               fLst(more,results,i,all_same)
            else
               fLst(more,i::results,i,false)
         end
  val res = f(p)
in
  res
end

fun convertToCnfLst(props,
                    A: cnf_array_entry Array.array,
   		    ht: (int * int list,int) HashTable.hash_table,
		    atom_table: (prop,int) HashTable.hash_table,
		    inverse_atom_table: (int,prop) HashTable.hash_table,
		    index_counter: int ref) = 
  let fun loop([],results) = results
        | loop(p::more,results) = 
            let val res = convertToCnf(p,A,ht,atom_table,inverse_atom_table,index_counter)
            in 
               loop(more,res::results)
            end
   in
     loop(props,[])
   end

fun sentConToString(i) = if i = 0 then "not" else if i = 1 then "and" else "or"

fun printEntry(A,i) = 
  let val entry = Unsafe.Array.sub(A,i)
      val _ = print("\n====================== Array element #" ^ (Int.toString(i)) ^ ":\n")
  in 
     (case Unsafe.Array.sub(A,i) of 
        complex_entry({sentential_constructor,arguments,is_flat_disjunction,...}) =>
            (print("\nSentential constructor: " ^ sentConToString(sentential_constructor));
	     print("\nArgument indices: " ^ (Basic.printListStr(arguments,Int.toString,", ")));
	     print("\nIs flat disjunction: " ^ (Basic.boolToString(is_flat_disjunction))))
      | atomic_entry({p,...}) => print("\nATOM: " ^ (toStringDefault(p))))
  end

fun getAllCnfDefs(A,i,already_seen_array) = 
  let fun getDefs(i,all_clauses:clause list,var_count:int): (clause list * int) = 
	   if (i < 0 orelse Unsafe.Array.sub(already_seen_array,i))
	   then (all_clauses,var_count)
           else
           let val _ = Unsafe.Array.update(already_seen_array,i,true)
           in
              (case Unsafe.Array.sub(A,i) of
                  complex_entry({definition_clauses,is_flat_disjunction,arguments,...}) =>
  		     if is_flat_disjunction then
                       getDefsLst(arguments,definition_clauses@all_clauses,var_count)
                     else
		       getDefsLst(arguments,definition_clauses@all_clauses,1 + var_count)
                | atomic_entry(_) => (all_clauses,var_count))
           end
      and getDefsLst([],results:clause list,var_count:int) = (results,var_count)
        | getDefsLst(i::more,results,var_count:int) = 
                let val (results',var_count') = getDefs(i,results,var_count)
	        in
                   getDefsLst(more,results',var_count')
                end

      val ((clauses,var_count),is_atomic) = 
                 if isAtomic(i,A) then (([[i]],0),true)
                 else (getDefs(i,[],0),false)
   in
     (case isFlatDisjunction(i,A) of
        SOME(atom_indices) => ([atom_indices],var_count)
      | _ => if is_atomic then (clauses,var_count)
             else ([i]::clauses,var_count))
   end
  
fun getNNFs(props,start) = 
let fun loop([],res,n) = (res,n)
      | loop(p::more,res,n) = 
           let val (p',n') = nnfNoQuants(p)
           in
              loop(more,p'::res,n'+n)
           end
    in  
      loop(props,[],start)
    end

fun makeCNFFromNNFs(nnfs,n,t1) = 
  let 
      val bogus_entry = atomic_entry{p= true_prop}
      val A_size = 100+n
      val A = Unsafe.Array.create(A_size,bogus_entry)
      fun hash_fun(i,L) = Basic.hashTwoWords(Basic.hashInt(i),Basic.hashIntList(L))
      val ht: (int * int list,int) HashTable.hash_table = HashTable.mkTable(hash_fun,op=) (n,Basic.Never)
      val atom_table: (prop,int) HashTable.hash_table = HashTable.mkTable(hash,alEq) (n div 2,Basic.Never) 
      val inverse_atom_table: (int,prop) HashTable.hash_table = HashTable.mkTable(Basic.hashInt,op=) (n div 2,Basic.Never)
      val index_counter = ref(1)
      val indices = convertToCnfLst(nnfs,A,ht,atom_table,inverse_atom_table,index_counter)
      val already_seen_array = Unsafe.Array.create(1000+n,false)
      val top_level_already_seen: (int,bool) HashTable.hash_table = HashTable.mkTable(Basic.hashInt,op=) (length(indices),Basic.Never)
      fun loop([],results,tseitin_var_count) = (results,tseitin_var_count)
        | loop(i::more,results,tseitin_var_count) = 
            if (case (HashTable.find top_level_already_seen i) of NONE => false | _ => true)
            then loop(more,results,tseitin_var_count)
            else
            let val _ = HashTable.insert  top_level_already_seen (i,true)
                val (cl:clauses,var_count) = getAllCnfDefs(A,i,already_seen_array)
            in
	       loop(more,cl@results,tseitin_var_count+var_count)
            end
      val (clauses,tseitin_var_count) = loop(indices,[],0) 
      val t2 = Time.toReal(Time.now())		
      val result_record = {clauses=clauses,
                           table=inverse_atom_table,
                          total_var_num=tseitin_var_count+ HashTable.numItems(inverse_atom_table),			  
                          tseitin_var_num=tseitin_var_count,
			  clause_num=length(clauses),
			  array_n = A_size,
			  cnf_conversion_time=Real.-(t2,t1)
			  }
  in
     result_record
  end

fun cnf(p) = 
  let val t1 = Time.toReal(Time.now())
      val (nnf,n) = nnfNoQuants(p)
      val nnfs = getConjuncts(nnf)
  in
     makeCNFFromNNFs(nnfs,n,t1)
  end

fun cnfLst(props) = 
  let val t1 = Time.toReal(Time.now())
      val (nnfs,n) = getNNFs(props,0)
      val nnfs = getConjunctsLst(nnfs)
  in
     makeCNFFromNNFs(nnfs,n,t1)
  end

fun makeTPTPFormulas(props) = 
          let val index = ref 1
              val atom_count = ref 0
              val hash_table: (prop,string) HashTable.hash_table = HashTable.mkTable(hash, alEq) (2000,HT)
              val inverse_hash_table: (string,prop) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=) (2000,HT)
              fun makeBoolVar() = let val res = Sat.var_prefix^(Int.toString(!index))
                                      val _ = Basic.inc(index)
                                  in
                                     res
                                  end
              fun f(neg({arg,...}),slist) = let val (p_str,slist') = f(arg,slist)
                                            in
                                               (" ~ ("^p_str^")",slist')
                                            end
                | f(conj({args,...}),slist) = let val (p_strings,slist) = fLst(args,slist,[])
                                                  val p_str = Basic.printListStr(p_strings,fn x => x," & ")
                                              in
     	  	   	                         ("("^p_str^")",slist)
                                              end
                | f(disj({args,...}),slist) = let val (p_strings,slist) = fLst(args,slist,[])
                                                  val p_str = Basic.printListStr(p_strings,fn x => x," | ")
                                              in
     	  	   	                         ("("^p_str^")",slist)
                                              end
                | f(cond({ant,con,...}),slist) = let val (p_str1,slist1) = f(ant,slist)
                                                     val (p_str2,slist2) = f(con,slist1)
                                                  in
        	  	   	                     ("("^p_str1^" => "^p_str2^")",slist2)
                                                  end
                | f(biCond({left,right,...}),slist) = let val (p_str1,slist1) = f(left,slist)
                                                          val (p_str2,slist2) = f(right,slist1)
                                                       in
        	  	   	                         ("("^p_str1^" <=> "^p_str2^")",slist2)
                                                       end
                | f(p,slist) = (case (HashTable.find hash_table p) of 
                                           SOME(bvar) => 
                                                (bvar^"()",slist)
                                         | _ => let val _ = Basic.inc(atom_count)
           		      	  	     	    val bvar = makeBoolVar()
                                                    val _ = HashTable.insert hash_table (p,bvar)
                                                    val _ = HashTable.insert inverse_hash_table (bvar,p)
                                                in
                                                   (bvar^"()",bvar::slist)
                                                end)
             and  fLst([],slist,res) = (res,slist)
                | fLst(p::more,slist,res) = let val (p_str,slist') = f(p,slist)
                                            in
                                               fLst(more,slist',p_str::res)
                                            end
              val (res,slist) = fLst(props,[],[])
          in
             {p_strings=res,sym_list=slist,htable=hash_table,
              inverse_htable = inverse_hash_table,leaf_count=(!atom_count)}
          end

fun findAndSkipLine(in_stream,l) = let fun loop() = 
           	  		         let val line =  TextIO.inputLine(in_stream)
			                 in
                                            if line = "" orelse line = l then ()
	   			            else loop()
 				         end
			           in 
				      loop()
			           end

fun compare(atom({term=t1,...}),atom({term=t2,...})) = AT.compare(t1,t2)
  | compare(atom(_),_) = LESS
  | compare(p,atom(_)) = GREATER 
  | compare(p1,p2) = 
       let val r = Int.compare(getRootCode(p1),getRootCode(p2))
       in
          if r = EQUAL then Basic.lexOrder(getSubtrees(p1),getSubtrees(p2),compare) else r
       end               

fun isSkolemConstant(str)  = (if String.substring(str,0,2) = "Sk" then true else false) handle _ => false

fun firstElement(str) = String.substring(str,0,1)

fun printFile(stream) = 
   let val l =  TextIO.inputLine(stream)
   in 
      if l = "" then () else (print("\nLine: "^l); printFile(stream))
   end

fun makeCommand(in_file_name,out_file_name) = 
  let val (error_file,other_file) = ("minisat_error2.txt", "other_out_mini2.txt")
  in
     Names.minisat_binary ^ " -verbosity=0 "^in_file_name^" "^out_file_name^" 1> "^other_file^" 2> "^error_file
  end

fun makeDimacsFile(r:cnf_conversion_result as
                       {clauses,
		        table as inverse_atom_table,
			total_var_num,
			tseitin_var_num,
			clause_num,
			cnf_conversion_time,
			array_n,...},
		   dimacs_file_name) = 

let val A = Unsafe.Array.create(10+array_n,false)
    val total_var_count = ref(0)
    fun clauseToString(c:clause) =  Basic.printListStr(c,
                                                       fn i => let val (is_neg,abs_i) = if i < 0 then (true,~i) else (false,i)
                                                                   val _ = if Unsafe.Array.sub(A,abs_i) then () 
                                                                           else (Unsafe.Array.update(A,abs_i,true);Basic.inc(total_var_count))
 						                   val i_str = if is_neg then "-"^(Int.toString(abs_i)) else Int.toString(abs_i)
                                                               in
                                                                  i_str
                                                               end,
                                                       " ") ^ " 0\n"
    val clause_strings = map clauseToString clauses
    val dimacs_stream = TextIO.openOut(dimacs_file_name)
    val _ = ((TextIO.output(dimacs_stream,"p cnf "^(Int.toString(!total_var_count))^" "^(Int.toString(clause_num))^"\n");
              List.app (fn cl => TextIO.output(dimacs_stream,cl)) clause_strings)
             handle exn => (TextIO.closeOut dimacs_stream; raise exn)
             before TextIO.closeOut dimacs_stream)
in
  TextIO.closeOut(dimacs_stream)
end

fun runSatSolver(dimacs_file,out_file_name) = 
let val (error_file,other_file) = ("minisat_error2.txt", "other_out_mini2.txt")
    val sat_solver_cmd = Names.minisat_binary ^ " -verb=0 "^dimacs_file^" "^out_file_name^" 1> "^other_file^" 2> "^error_file

(***
    val _ = OS.Process.system(sat_solver_cmd)
***)
    val result = OS.Process.system(sat_solver_cmd)
(***
    val _ = if result = 10 orelse result = 20 
            then ()
            else Basic.fail("SAT solver did not complete successfully")
***)
(*** 
    val _ = (List.app OS.FileSys.remove [error_file,other_file]) handle _ => ()
***)
   (* Remove temporary files with a structured exception handler *)
    val _ =  (List.app (fn file => (OS.FileSys.remove file handle _ => ())) 
             [error_file, other_file])
in
    ()
end

val dimacs_counter = ref(0)

fun propSat(props,
            out_hash_table,
	    transformProp,
	    transformBool) = 

  let val r as {clauses,table=inverse_atom_table,total_var_num,tseitin_var_num,clause_num,cnf_conversion_time,array_n,...} = cnfLst(props) 
      val (dimacs_file,minisat_out_file_name) = ("dimacs_file_" ^ (Int.toString (Basic.incAndReturn(dimacs_counter))) ^ ".txt" ,"./minisat_out.txt")
      val t1 = Time.toReal(Time.now())
      val _ = makeDimacsFile(r,dimacs_file)
      val t2 = Time.toReal(Time.now())
      val _ = runSatSolver(dimacs_file,minisat_out_file_name)
      val t3 = Time.toReal(Time.now())
      val dimacs_prep_time = (Real.-(t2,t1))
      val sat_solving_time = (Real.-(t3,t2))
      val out_stream = TextIO.openIn(minisat_out_file_name)
      val res = getMiniSatResult(out_stream,inverse_atom_table,out_hash_table,transformProp,transformBool)
      val _ =  List.app (fn file => (OS.FileSys.remove file handle _ => ()))
                        [dimacs_file,minisat_out_file_name]
  in
     {assignment=res,
      clause_num=clause_num,
      total_var_num=total_var_num,	
      tseitin_var_num=tseitin_var_num,
      cnf_conversion_time=cnf_conversion_time,
      dimacs_file_prep_time=dimacs_prep_time,
      sat_solving_time=sat_solving_time}
  end

 fun dedup(props) = 
    let val mem: (prop,bool) HashTable.hash_table = HashTable.mkTable(hash,alEq) (100,Basic.Fail("Hashing Exception"))
        val props' = List.filter (fn p => (case (HashTable.find mem p) of 
                                              NONE => let val _ = (HashTable.insert mem (p,true))
                                                      in
                                                        true
                                                      end
                                            | _ => false)) props
    in
      props'
    end

val (renameSortVarsAux,renameSortVarsAuxLst) = 
  let fun f(atom({term,hash_code,flags,...}),sub) = 
              let val (term',sub') = AT.renameSortVarsAux(term,sub)
              in
                (atom({term=term',flags=flags,hash_code=hash_code}),sub')
              end
        | f(neg({arg,flags,fvars,poly_constants,hash_code}),sub) = 
              let val (arg',sub') = g(arg,sub)
	          val fvars' = map (fn v => ATV.applySortSub(sub',v)) fvars
                  val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                    (List.map (fn (c,sort) => (c,F.applySub(sub',sort))) 
						              poly_constants)		  
                  val p' = neg({arg=arg',
		               flags=flags,
			       fvars=fvars',
			       hash_code=hash_code,
			       poly_constants=poly_constants'})
              in
	         (p',sub')
              end
       | f(conj({args,flags,fvars,poly_constants,hash_code,...}),sub) = 
             let val (args',sub') = fLst(args,sub,[])
                 val fvars' = map (fn v => ATV.applySortSub(sub',v)) fvars
                 val poly_constants' = List.filter (fn (_,s) => not(F.isGround(s)))
                                                   (List.map (fn (c,sort) => (c,F.applySub(sub',sort))) 
						             poly_constants)
              in
                (conj({args=args',fvars=fvars',flags=flags,
		       poly_constants=poly_constants',hash_code=hash_code}),
		 sub')
              end
       | f(disj({args,flags,fvars,poly_constants,hash_code,...}),sub) = 
             let val (args',sub') = fLst(args,sub,[])
                 val fvars' = map (fn v => ATV.applySortSub(sub',v)) fvars
                 val poly_constants' = List.filter (fn (_,s) => not(F.isGround(s)))
                                                   (List.map (fn (c,sort) => (c,F.applySub(sub',sort))) 
						             poly_constants)
              in
                (disj({args=args',fvars=fvars',flags=flags,
		       poly_constants=poly_constants',hash_code=hash_code}),
		 sub')
              end
       | f(cond({ant,con,flags,fvars,poly_constants,hash_code,...}),sub) = 
           let val (ant',sub') = g(ant,sub)
               val (con',sub_final) = g(con,sub')
               val flags' = flags
               val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                 (List.map (fn (c,sort) => (c,F.applySub(sub_final,sort))) 
						           poly_constants)
   	       val fvars' = map (fn v => ATV.applySortSub(sub_final,v)) fvars	
           in
	     (cond({ant=ant',con=con',fvars=fvars',
	            poly_constants=poly_constants',flags=flags',hash_code=hash_code}),
	      sub_final)
           end
       | f(biCond({left,right,flags,fvars,poly_constants,hash_code,...}),sub) = 
           let val (left',sub') = g(left,sub)
               val (right',sub_final) = g(right,sub')
               val flags' = flags
               val poly_constants' = List.filter (fn (c,s) => not(F.isGround(s)))
                                                 (List.map (fn (c,sort) => (c,F.applySub(sub_final,sort))) 
						           poly_constants)
   	       val fvars' = map (fn v => ATV.applySortSub(sub_final,v)) fvars	
           in
	     (biCond({left=left',right=right',fvars=fvars',
	              poly_constants=poly_constants',flags=flags',hash_code=hash_code}),
	      sub_final)
           end
       | f(p as uGen({qvar,body,flags,fvars}),sub) = 
		let val (qvar',sub') = ATV.renameSortVars(qvar,sub)
		    val (body',sub_final) = g(body,sub')
		    val fvars' = map (fn v => ATV.applySortSub(sub_final,v)) fvars	
		    val w = makeWord({poly=isPoly(body') orelse ATV.isPoly(qvar'),
                                      involves_pred_based_sorts=involvesPredBasedSorts(body'), 
				      bvars=true,fvars=hasFreeVars(p)})
	            val flags' = flags
		in
		   (uGen({qvar=qvar',body=body',flags=flags',fvars=fvars'}),sub_final)
		end
       | f(p as eGen({qvar,body,flags,fvars}),sub) = 
		let val (qvar',sub') = ATV.renameSortVars(qvar,sub)
		    val (body',sub_final) = g(body,sub')
		    val fvars' = map (fn v => ATV.applySortSub(sub_final,v)) fvars	
		    val w = makeWord({poly=isPoly(body') orelse ATV.isPoly(qvar'),
                                      involves_pred_based_sorts=involvesPredBasedSorts(body'), 
				      bvars=true,fvars=hasFreeVars(p)})
	            val flags' = flags
		in
		   (eGen({qvar=qvar',body=body',flags=flags',fvars=fvars'}),sub_final)
		end
       | f(p as eGenUnique({qvar,body,flags,fvars}),sub) = 
		let val (qvar',sub') = ATV.renameSortVars(qvar,sub)
		    val (body',sub_final) = g(body,sub')
		    val fvars' = map (fn v => ATV.applySortSub(sub_final,v)) fvars	
		    val w = makeWord({poly=isPoly(body') orelse ATV.isPoly(qvar'),
                                      involves_pred_based_sorts=involvesPredBasedSorts(body'), 
				      bvars=true,fvars=hasFreeVars(p)})
	            val flags' = flags
		in
		   (eGenUnique({qvar=qvar',body=body',flags=flags',fvars=fvars'}),sub_final)
		end
      and g(p,sub) = if not(isPoly(p)) then (p,sub) else f(p,sub)
      and fLst([],sub,results) = (rev(results),sub)
        | fLst(p::more,sub,results) = 
              let val (p',sub') = g(p,sub)
              in
                 fLst(more,sub',p'::results)
              end
  in
    ((fn (p,sub) => g(p,sub)),(fn (props,sub) => fLst(props,sub,[])))
  end

fun renameSortVars(p) = 
     let val (p',_) = renameSortVarsAux(p,F.empty_sub)
     in
       p'
     end

fun renameSortVarsLst(props) = 
     let val (props',_) = renameSortVarsAuxLst(props,F.empty_sub)
     in
       props'
     end

fun isExMiddleInstance(p) = 
      (case isDisj(p) of
          SOME([p1,p2]) => alEq(p2,makeNegation(p1))
	| _ => false)

end  (**  of "abstype prop with..."  **)

end (** Of Prop structure **)

