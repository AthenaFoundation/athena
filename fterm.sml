(*======================================================================

Fast terms ("fterm's") are tree structures that represent Athena sorts.
Internal nodes of such terms are non-constant sort constructors and leaves
are either constant sort constructors or sort variables, which are represented
as infinite integers.

=======================================================================*)

structure FTerm = 

struct 

structure S = ModSymbol
structure MS = ModSymbol

type variable = InfNum.inf_num 

type fsymbol = ModSymbol.mod_symbol

structure SO = SortOrder

val failLst = Basic.failLst

val inf_counter = InfNum.makeInfNum()

val varEq = InfNum.eq

val fsymEq = ModSymbol.modSymEq

exception Subterm

val sorts_with_predicates:int MS.htable = MS.makeHTableWithInitialSize(31)

fun addSortWithPredicate(f,arity:int) = MS.insert(sorts_with_predicates,f,arity)

fun isSortWithPredicate(f) = (case MS.find(sorts_with_predicates,f) of NONE => false | _ => true)

abstype term = Var of variable | App of {root:fsymbol,args:term list,bits:Word8.word}

with

fun rootString(Var(v)) = "S" 
  | rootString(App({root,...})) = S.name(root)

fun termEq(App({root=f,args=terms1,...}),
	   App({root=g,args=terms2,...})) = fsymEq(f,g) andalso termEqLst(terms1,terms2)
  | termEq(Var(v),Var(v')) = varEq(v,v') 
  | termEq(_,_) = false
and
    termEqLst(t1::rest1,t2::rest2) = termEq(t1,t2) andalso termEqLst(rest1,rest2)
  | termEqLst([],[]) = true
  | termEqLst(_,_) = false

infix ==

fun t1 == t2 = termEq(t1,t2)

fun compare(App({root=f1,args=terms1,...}),App({root=f2,args=terms2,...})) = 
          let val r = ModSymbol.compare(f1,f2)
          in
             if r = EQUAL then compareLst(terms1,terms2) else r
          end
       | compare(Var(_),App(_)) = LESS
       | compare(Var(v1),Var(v2)) = InfNum.compare(v1,v2)
       | compare(App(_),Var(_)) = GREATER 
     and 
        compareLst(t1::rest1,t2::rest2) = 
	    let val r = compare(t1,t2) 
	    in
	       if r = EQUAL then compareLst(rest1,rest2) else r
            end 
      | compareLst([],[]) = EQUAL
      | compareLst(_::_,[]) = GREATER
      | compareLst([],_::_) = LESS


(************************************************************************************
                      Info on fterm bit fields:

The lowest bit is the "has-vars field". It indicates whether the
term has variables (whether it is not ground). 

The next highest bit is the "has-order-sorted symbols". It denotes
whether the sort contains any order-sorted domains in it, monomorphic
or polymorphic.

The next highest bit is the "has-polymorphic-order-sorted symbols",
denoting the obvious.

Finally, the highest bit indicates whether the term contains
sort constructors that have sort predicates associated with them. 
 
Hence, a word that ends in 0000 denotes a ground (monomorphic) sort 
without any order-sorted or predicate-based domains in it. 
One that ends in 001 denotes a polymorphic sort without any order-sorted 
or predicate-based domains in it. One that end in 010 denotes a monomorphic 
sort with monomorphic order-sorted domains in it but no predicate-based
domains. One that ends in 0100 denotes a monomorphic (ground) sort with 
polymorphic order-sorted domains in it but no predicate-based domains in it.
One that ends in 1000 denotes a monomorphic (ground) sort with 
some predicate-based domains in it but without any order-sorted 
polymorphic order-sorted domains in it but no predicate-based domains in it.

Note that since a predicate-based domain is automatically order-sorted
(it's a subsort of some other sort), it's impossible for a term to
have predicate-based domains in it but no order-sorted domains, i.e.,
the combination 100X is impossible.

************************************************************************************)

val orWords = Word8.orb
 
val zeroWord:Word8.word = 0w0

val polyWord:Word8.word = 0w1
val varsWord:Word8.word = 0w1

val OSDWord:Word8.word = 0w2

val POSDWord:Word8.word = 0w4

val sortsWithPredicatesWord:Word8.word = 0w8

fun hasVarsWord(w:Word8.word) = (Word8.andb(w,varsWord) = varsWord)

fun hasOrderSortedDomainsWord(w:Word8.word) = (Word8.andb(w,OSDWord) = OSDWord)

fun hasPolymorphicOrderSortedDomainsWord(w:Word8.word) = (Word8.andb(w,POSDWord) = POSDWord)

fun hasPredicateBasedDomainsWord(w:Word8.word) = (Word8.andb(w,sortsWithPredicatesWord) = sortsWithPredicatesWord)

fun isGroundWord(w:Word8.word) = not(hasVarsWord(w))

fun isGround(Var(v)) = false
  | isGround(App({bits,...})) = isGroundWord(bits)

fun hasVars(Var(_)) = true
  | hasVars(App({bits,...})) = hasVarsWord(bits)


fun areAllGround([]) = true
  | areAllGround(Var(_)::_) = false
  | areAllGround(App({bits,...})::rest) = if isGroundWord(bits) then areAllGround(rest) else false

fun hasPolymorphicOrderSortedDomains(Var(v)) = false
  | hasPolymorphicOrderSortedDomains(App({bits,...})) = hasPolymorphicOrderSortedDomainsWord(bits)

fun havePolymorphicOrderSortedDomains(terms) = Basic.exists(terms,hasPolymorphicOrderSortedDomains)

fun makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=false,hasVars=false}):Word8.word = 0w0  (* value of 0 *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=false,hasVars=true}):Word8.word = 0w1   (* value of 1 *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=false,hasOSD=false,hasVars=true}):Word8.word = 0w9
                (* value of 9, not that this case is impossible *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=true,hasVars=false}):Word8.word = 0w2   (* value of 2 *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=false,hasOSD=true,hasVars=false}):Word8.word = 0w10   (* value of 10 *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=true,hasVars=true}):Word8.word = 0w3    (* value of 3 *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=false,hasOSD=true,hasVars=true}):Word8.word = 0w11    (* value of 11 *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=true,hasOSD=false,hasVars=false}):Word8.word = 0w4  
      	        (* value of 4, note that this case cannot actually arise, as it indicates
                   that the term has polymorphic order-sorted domains but no order-sorted domains *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=true,hasOSD=false,hasVars=false}):Word8.word = 0w12  
 		(* value of 12, this case is also impossible *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=true,hasOSD=false,hasVars=true}):Word8.word = 0w5 
  	        (* value of 5, this case cannot arise either *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=true,hasOSD=false,hasVars=true}):Word8.word = 0w13
		(* value of 13, this case cannot arise either *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=true,hasOSD=true,hasVars=false}):Word8.word = 0w6    (* value of 6 *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=true,hasOSD=true,hasVars=false}):Word8.word = 0w14    (* value of 14 *)

  | makeWord({hasPredBasedSorts=false,hasPolyOSD=true,hasOSD=true,hasVars=true}):Word8.word = 0w7     (* value of 7 *)
  | makeWord({hasPredBasedSorts=true,hasPolyOSD=true,hasOSD=true,hasVars=true}):Word8.word = 0w15     (* value of 15 *)

fun orTermWords([],w) = w
  | orTermWords(App({bits,...})::more,w) = orTermWords(more,orWords(bits,w))
  | orTermWords(Var(v)::more,w) =  orTermWords(more,orWords(w,varsWord))

fun printWord(w) = print(Word8.toString(w))

fun printBits(App({root,bits,...})) = (print("\nHere are the bits: ");printWord(bits))
  | printBits(_) = ()

fun makeVar(v) = Var(v)

fun makeMConstant(c:ModSymbol.mod_symbol) = 
	let val b = SO.isOrderSorted(c) 
	in
	  if b = 0 then 
            App({root=c,args=[],bits=makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=false,hasVars=false})})
	  else
            let val is_pred_based = isSortWithPredicate(c)
            in
   	        if b = 1 then 
	           App({root=c,args=[],bits=makeWord({hasPredBasedSorts=is_pred_based,hasPolyOSD=false,hasOSD=true,hasVars=false})})
	        else App({root=c,args=[],bits=makeWord({hasPredBasedSorts=is_pred_based,hasPolyOSD=true,hasOSD=true,hasVars=false})})
            end
        end


fun makeApp(f,terms) = 
	let val b = SO.isOrderSorted(f) 
	in
	  if b = 0 then 
            App({root=f,args=terms,bits=orTermWords(terms,0w0)})
	  else
             let val is_pred_based = isSortWithPredicate(f) 
             in
               if b = 1 then 
	          (if is_pred_based then App({root=f,args=terms,bits=orTermWords(terms,orWords(sortsWithPredicatesWord,OSDWord))})
                      else App({root=f,args=terms,bits=orTermWords(terms,OSDWord)}))
               else (if is_pred_based then App({root=f,args=terms,bits=orTermWords(terms,orWords(sortsWithPredicatesWord,POSDWord))})
                     else App({root=f,args=terms,bits=orTermWords(terms,POSDWord)}))
             end
        end

fun findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(t) = 
       (case t of
           App({bits,...}) => hasOrderSortedDomainsWord(bits)
         | _ => false)

fun findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(t) = 
       (case t of
           App({bits,...}) => hasPredicateBasedDomainsWord(bits)
         | _ => false)

fun findOutDynamicallyIfAnySortsHavePredicateBasedSortSymbols(terms) = 
          (List.exists findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt terms)

fun findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(t) = 
       let fun f(App({root,args,...}),res) = 
		if SO.isOrderSorted(root) = 0 andalso null(args) then fLst(args,res) else fLst(args,root::res)
             | f(Var(_),res) = res
            and fLst(t::more,res) = fLst(more,(f(t,res))@res)
              | fLst([],res) = res
       in
          (case f(t,[]) of
              [] => NONE
            | res => SOME(res))
       end

val hasOrderSortedDomains = findOutDynamicallyIfASortHasOrderSortedSymbolsInIt

fun isVarOpt(Var(v)) = SOME(v) 
  | isVarOpt(_) = NONE

fun isVar(Var(_)) = true
  | isVar(_) = false

fun isTaggedVar(Var(v)) = InfNum.tagged(v) 
  | isTaggedVar(_) = false

fun isUnTaggedVar(Var(v)) = not(InfNum.tagged(v))
  | isUnTaggedVar(_) = false

fun allTaggedVars(App({root,args,...})) = List.all allTaggedVars args 
  | allTaggedVars(t as Var(_)) = isTaggedVar(t)

fun someTaggedVars(App({root,args,...})) = List.exists someTaggedVars args 
  | someTaggedVars(t as Var(_)) = isTaggedVar(t)

fun isConstant(App({root=f,args=[],...})) = SOME(f)
  | isConstant(_) = NONE

fun isApp(App({root=f,args=terms,...})) = SOME(f,terms)
  | isApp(_) = NONE

fun varOccursIn(v,Var(v')) = varEq(v,v')
  | varOccursIn(v,App({args=terms,...})) = Basic.exists(terms,fn t => varOccursIn(v,t))

fun fsymOccursIn(f,App({root=g,args,...})) = fsymEq(f,g) orelse Basic.exists(args,fn t => fsymOccursIn(f,t))
  | fsymOccursIn(f,_) = false

fun height(App({args as _::_,...})) = 1 + Basic.maxLst(map height args)
  | height(_) = 0

fun varToString(v) = Names.sort_variable_prefix^(Names.sort_variable_letter_prefix)^(InfNum.toString v)

fun makeVarSortPrinter() = 
	let val tl_index = ref(0)
	    exception HT 
	    val variable_prefix = Names.variable_prefix
	    val variable_prefix_length = String.size(variable_prefix)
	    fun getTLetter(0) = "S"
	      | getTLetter(1) = "T"
	      | getTLetter(2) = "U"
	      | getTLetter(3) = "V"
	      | getTLetter(4) = "W"
	      | getTLetter(_) = "Q"
	    fun nextTypeLetter() = let val letter = getTLetter(Int.mod(!tl_index,5))
	                                val quot = !tl_index div 5
	                                val index = if quot < 1 then "" else Int.toString(quot)
	                                val _ = tl_index := !tl_index + 1
	                            in
	                               letter^index
	                            end
	    val table:(variable,string) HashTable.hash_table = 
			HashTable.mkTable(fn n:InfNum.inf_num => Word.fromInt(InfNum.top(n)), op = ) (128,HT)
	 in
	   (fn (v:variable) =>
		 (case HashTable.find table v of 
		     SOME(str) => str
	           | _ => let val str = Names.sort_variable_prefix^nextTypeLetter()
			      val _ =  HashTable.insert table (v,str)
	                  in
			     str 
			   end))
         end

fun makePolyVarSortPrinter() = 
	let val tl_index = ref(0)
	    exception HT 
	    fun getTLetter() = "T"
	    fun nextTypeLetter() = let val letter = getTLetter()
	                                val quot = !tl_index 
	                                val index = Int.toString(quot)
	                                val _ = tl_index := !tl_index + 1
	                            in
	                               letter^index
	                            end
	    val table:(variable,string) HashTable.hash_table = 
			HashTable.mkTable(fn n:InfNum.inf_num => Word.fromInt(InfNum.top(n)), InfNum.eq) (128,HT)
	 in
	   (fn (v:variable) =>
		 (case HashTable.find table v of 
		     SOME(str) => str
	           | _ => let val str = nextTypeLetter()
			      val _ =  HashTable.insert table (v,str)
	                  in
			     str 
			   end))
         end

fun toString(Var v,printVarSort) = printVarSort v
  | toString(App({root=f,args=[],...}),_) = S.name(f)
  | toString(App({root=f,args,...}),printVarSort) = 
            "("^(S.name(f))^" "^(Basic.printSExpListStr(args,fn t => toString(t,printVarSort)))^")"

fun toOneString(Var v,printVarSort) = printVarSort v
  | toOneString(App({root=f,args=[],...}),_) = S.name(f)
  | toOneString(App({root=f,args,...}),printVarSort) = 
		(S.name(f))^Names.SMT_mono_sort_instantiation_of_poly_sort_char_separator_as_string^
                           (Basic.printListStr(args,fn t => toOneString(t,printVarSort),
                                               Names.SMT_mono_sort_instantiation_of_poly_sort_char_separator_as_string))

fun sortNameIntoCVCTypeName(name) = String.map (fn c => if c = #"-" then #"_" else c) name

fun toOneStringCVC(Var v,printVarSort) = printVarSort v
  | toOneStringCVC(App({root=f,args=[],...}),_) = sortNameIntoCVCTypeName(S.name f)
  | toOneStringCVC(App({root=f,args,...}),printVarSort) = 
            let val root_name = sortNameIntoCVCTypeName(S.name f)
            in
		root_name^Names.CVC_mono_sort_instantiation_of_poly_sort_char_separator_as_string^
                           (Basic.printListStr(args,fn t => toOneStringCVC(t,printVarSort),
                                               Names.CVC_mono_sort_instantiation_of_poly_sort_char_separator_as_string))
            end 

fun toStringDefault(t) = toString(t,varToString)

fun toOneStringDefault(t) = toOneString(t,varToString)
fun toOneStringDefaultCVC(t) = toOneStringCVC(t,varToString)
   
val atp_sort_prefix = "csort"

fun toPolyString(t,printVarSort) = 
           let val (lp,rp,comma) = ("(",")",",")
               fun f(Var v,{vars=vs,fsyms=fs}) = let val v_str = printVarSort v
                                                 in
                                                    (v_str,{vars=v_str::vs,fsyms=fs})
                                                 end
                 | f(App({root=f,args=[],...}),{vars,fsyms}) = 
                                 let val c_str = atp_sort_prefix^(Basic.fsymRenamer(Basic.toLower(S.name(f))))
                                 in 
                                    (c_str,{vars=vars,fsyms=(lp^c_str^comma^"0"^rp)::fsyms})
                                 end
                 | f(App({root=f,args,...}),res as {vars,fsyms}) = 
                      let val (str_lst,{vars=vars',fsyms=fsyms'}) = fLst(args,[],res)
                          val str_lst_str = Basic.printListStr(str_lst,fn x => x,comma)
                          val f_str = atp_sort_prefix^(Basic.fsymRenamer(Basic.toLower(S.name(f))))
                          val fsyms'' = (lp^f_str^comma^(Int.toString(length(args)))^rp)::fsyms'
                      in
      	  	        (f_str^lp^str_lst_str^rp,{vars=vars',fsyms=fsyms''})
                      end
               and fLst([],strings,res) = (rev strings,res)
                 | fLst(t::more,strings,res as {vars,fsyms}) = let val (str,res') = f(t,res)
                                                               in fLst(more,str::strings,res') end
           in
              f(t,{vars=[],fsyms=[]})
           end

fun toPrettyString(start,t,printVar) = 
       let fun pp(s,Var(v)) = printVar v
             | pp(s,App({root=f,args=[],...})) = S.name(f)
             | pp(s,App({root=f,args,...})) = 
		 	let val str = S.name(f)
                            val break_up = List.exists (fn t => height(t) > 0) args
                        in
                           "("^str^" "^ppArgs(s+String.size(str)+2,args,break_up)^")" 
                        end 
          and ppArgs(s,args,false) = Basic.printSExpListStr(args,fn t => toString(t,printVar))
            | ppArgs(s,args,true) = doArgs(s,args)
          and doArgs(s,[]) = ""
            | doArgs(s,[t]) = pp(s,t)
            | doArgs(s,t1::t2::more) = pp(s,t1)^Basic.new_line^Basic.spaces(s)^doArgs(s,t2::more)
       in
          pp(start,t)
       end

fun toPrettyStringDefault(start,t) = toPrettyString(0,t,varToString)

fun toStringDefaultLst(sorts) = Basic.printListStrCommas(sorts,fn s => toPrettyStringDefault(0,s))

fun printSorts(sorts) = print(toStringDefaultLst(sorts))
              
fun gleanVars(App({args,...}),lst) = gleanVarsLst(args,lst)
  | gleanVars(Var(v),lst) = v::lst
and
    gleanVarsLst(t::rest,lst) = gleanVarsLst(rest,gleanVars(t,lst))
  | gleanVarsLst([],lst) = lst

val (getVars,getVarsLst) = 
                (fn t => let val vars = gleanVars(t,[])
                         in
                           Basic.removeDuplicatesEq(vars,varEq)
                         end,
                 fn terms => let val vars = gleanVarsLst(terms,[])
                             in
                               Basic.removeDuplicatesEq(vars,varEq)
                             end)

(************************************************************************************
                           Substitutions for fterms
************************************************************************************)

type sub = term InfIntMapTable.table

val empty_sub = InfIntMapTable.empty

fun isEmptySub(theta:sub) = InfIntMapTable.isEmpty(theta)

fun incSub(tab,(v,t)) = InfIntMapTable.enter(tab,v,t)

fun supp(tab) = 
          let fun f(v,term,accum) = if term == Var(v) then accum else v::accum
          in
              InfIntMapTable.foldli f [] tab
          end      

infix ++

fun sub ++ (v,t) = incSub(sub,(v,t))

fun extendSub(sub,[]) = sub 
  | extendSub(sub,(v,t)::rest) = extendSub(sub++(v,t),rest)

fun makeSub(pairs) = extendSub(empty_sub,pairs)

fun applySub(sub,t as App({root,args,bits,...})) = 
	     if isGroundWord(bits) then t else makeApp(root,map (fn t => applySub(sub,t)) args)
  | applySub(sub,t as Var(v)) = 
           (case InfIntMapTable.look(sub,v) of
               SOME(termThunk) => termThunk
             | _ => t)

fun applySubLst(sub,lst) = map (fn t => applySub(sub,t)) lst

fun subToString(tab) = 
		let val support = supp(tab)
		in
		   Basic.printListStr(support,fn v => (varToString v)^" --> "^
				  	              (toStringDefault(applySub(tab,Var v))),"\n")
		end
		
fun inSupp(v,s) = not (applySub(s,Var(v)) == Var(v))

fun subEq(sub1,sub2) =
       let val supp1 = supp(sub1) 
       in
         Basic.listEq(supp1,supp(sub2),op=) andalso
         Basic.forall(supp1,(fn v => applySub(sub1,Var(v)) == applySub(sub2,Var(v))))
       end
 
fun composeSubs(sub2,sub1) = 
         let val sub1' = InfIntMapTable.map (fn termThunk => (applySub(sub2,termThunk))) sub1
             fun f(v,termThunk,sub_accum) = 
                   if inSupp(v,sub1') then sub_accum else InfIntMapTable.enter(sub_accum,v,termThunk)
         in
            InfIntMapTable.foldli f sub1' sub2
         end

fun replace(v,t1,t2) =
         let val unit_sub = makeSub([(v,t1)])
         in
           applySub(unit_sub,t2)
         end

fun unifyError(s,t) = 
  let val printSortVar = varToString
  in
     failLst ["Could not unify the sorts\n"^(toPrettyString(0,s,printSortVar))^
             "\nand\n"^(toPrettyString(0,t,printSortVar))^"."]
  end                 

val (unifyEx,unifyExLst) = 
            let fun U(t1 as App({root=f,args=terms1,...}),
		      t2 as App({root=g,args=terms2,...})) = 
			 if fsymEq(f,g) then ULst(terms1,terms2) else unifyError(t1,t2)
                  | U(s as Var(v),t) = if varOccursIn(v,t) then
                                           if t == s then empty_sub
                                           else
					     failLst ["Failed occurs check in attempting to unify the sorts\n"^
						     (toPrettyString(0,s,varToString))^"\nand\n"^
						     (toPrettyString(0,t,varToString))^"."]
                                        else
                                           makeSub([(v,t)])
                  | U(s,t as Var(_)) = U(t,s)
                  and
                     ULst(t1::rest1,t2::rest2) = 
                       let val sub = U(t1,t2)
                           val (new_rest1,new_rest2) = (applySubLst(sub,rest1),applySubLst(sub,rest2))
                           val sub' = ULst(new_rest1,new_rest2)
                           in
                             composeSubs(sub',sub)
                       end
                  | ULst([],[]) = empty_sub
                  | ULst(_,_) = (failLst ["Attempt to unify two lists of sorts of different lengths"])
                 in
                   (fn (s,t) => U(s,t),
                    fn (slist,tlist) => ULst(slist,tlist))
             end

val (subsortUnifyEx,subsortUnifyExLst) =
(***
     These are the two default unification procedures. subSortUnifyEx(sort1,sort2,subsort)
     works if sort2 is a subsort of sort1 that can be unified with it according to the subsort relation.
****)    
        let fun sortUnify(subSort,from_side:int) =
	
(*** If from_side < 0 then ignore whole tagged-var and from-side issue. ****)
            let fun debugPrint(str) = ()
                fun U(t1 as App({root=f,args=terms1,...}),
		      t2 as App({root=g,args=terms2,...})) = 
			 if subSort(f,g) then ULst(terms1,terms2) 
			 else failLst ["Failed to unify the sorts "^(toStringDefault t1)^
				       " and "^(toStringDefault t2)^"."]
                  | U(s as Var(v),t as Var(v')) = 
                         if t == s then empty_sub
                         else (if isTaggedVar(s) orelse from_side = 2 then 
                                  makeSub([(v',s)])
                               else  makeSub([(v,t)]))
                  | U(s as Var(v),t) = if varOccursIn(v,t) then
                                          failLst ["Failed occurs check in attempting to unify the sorts\n"^
						   (toPrettyString(0,s,varToString))^
					           "\nand\n"^(toPrettyString(0,t,varToString))^"."]
                                        else makeSub([(v,t)])
                  | U(s,t as Var(_)) = U(t,s)
                  and
  		    ULst(t1::rest1,t2::rest2) = 
                       let val sub = U(t1,t2)
                           val (new_rest1,new_rest2) = (applySubLst(sub,rest1),applySubLst(sub,rest2))
                           val sub' = ULst(new_rest1,new_rest2)
                           in
                             composeSubs(sub',sub)
                       end
                  | ULst([],[]) = empty_sub

                  | ULst(L1,L2) = (failLst ["Attempt to unify two lists of sorts of different lengths"])
                 in
                   (U,ULst)
              end
         in 
              (fn (s,t,subSort,from_side) =>  (let val (U,_) = sortUnify(subSort,from_side) in U(s,t) end),
               fn (slist,tlist,subSort,from_side) => 
			(let val (_,ULst) = sortUnify(subSort,from_side) in ULst(slist,tlist) end))
         end

fun unify(s,t) = SOME(unifyEx(s,t)) handle _ => NONE

fun unifiable(s,t) = (case unify(s,t) of SOME(_) => true | _ => false)

fun unifyLst(sl,tl) = SOME(unifyExLst(sl,tl)) handle _ => NONE

datatype superTerm = regTerm of term | lubTerm of superTerm * superTerm | glbTerm of superTerm * superTerm

fun superTermEq(regTerm(s),regTerm(t)) = termEq(s,t)
  | superTermEq(lubTerm(s1,s2),lubTerm(t1,t2)) = superTermEq(s1,t1) andalso superTermEq(s2,t2)
  | superTermEq(glbTerm(s1,s2),glbTerm(t1,t2)) = superTermEq(s1,t1) andalso superTermEq(s2,t2)
  | superTermEq(_) = false

fun findDeepLub(st as (lubTerm(regTerm(_),regTerm(_)))) = st
  | findDeepLub(lubTerm(regTerm(_),st' as lubTerm(_))) = findDeepLub(st')

fun findDeepGlb(st as (glbTerm(regTerm(_),regTerm(_)))) = st
  | findDeepGlb(glbTerm(regTerm(_),st' as glbTerm(_))) = findDeepGlb(st')

fun replaceSuperSubTerm(s,t,t') = 
             if superTermEq(s,t) then t' 
             else (case s of 
                     regTerm(_) => s
                   | lubTerm(l,r) => lubTerm(replaceSuperSubTerm(l,t,t'),replaceSuperSubTerm(r,t,t'))
                   | glbTerm(l,r) => glbTerm(replaceSuperSubTerm(l,t,t'),replaceSuperSubTerm(r,t,t')))

fun occursInSuperTerm(x,regTerm(t)) = varOccursIn(x,t)
  | occursInSuperTerm(x,lubTerm(S1,S2)) = occursInSuperTerm(x,S1) orelse occursInSuperTerm(x,S2)
  | occursInSuperTerm(x,glbTerm(S1,S2)) = occursInSuperTerm(x,S1) orelse occursInSuperTerm(x,S2)

fun printSuperTerm(regTerm(t)) = toString(t,varToString)
  | printSuperTerm(lubTerm(S1,S2)) = "("^(printSuperTerm S1)^" \\/ "^(printSuperTerm S2)^")"
  | printSuperTerm(glbTerm(S1,S2)) = "("^(printSuperTerm S1)^" /\\ "^(printSuperTerm S2)^")"

fun superTermEq(regTerm(s),regTerm(t)) = termEq(s,t)
  | superTermEq(lubTerm(s1,t1),lubTerm(s2,t2)) = superTermEq(s1,t1) andalso superTermEq(s2,t2)
  | superTermEq(glbTerm(s1,t1),glbTerm(s2,t2)) = superTermEq(s1,t1) andalso superTermEq(s2,t2)
  | superTermEq(_) = false 

datatype constraint = identity of superTerm * superTerm | inclusion of superTerm * superTerm 

fun occursInConstraint(x,identity(S1,S2)) = occursInSuperTerm(x,S1) orelse occursInSuperTerm(x,S2)
  | occursInConstraint(x,inclusion(S1,S2)) = occursInSuperTerm(x,S1) orelse occursInSuperTerm(x,S2)

fun printConstraint(identity(S1,S2)) = printSuperTerm(S1)^" = "^printSuperTerm(S2)
  | printConstraint(inclusion(S1,S2)) = printSuperTerm(S1)^" <= "^printSuperTerm(S2)

fun printConstraintSystem({complex_inclusions,flat_inclusions,identities}) = 
 		"\nComplex inclusions: "^(Basic.printListStr(complex_inclusions,printConstraint,",\n"))^
 		"\nFlattened inclusions: "^(Basic.printListStr(flat_inclusions,printConstraint,",\n"))^
 		"\nIdentities: "^(Basic.printListStr(identities,printConstraint,",\n"))

fun applySubToSuperTerm(sub,regTerm(t)) = regTerm(applySub(sub,t))
  | applySubToSuperTerm(sub,lubTerm(S1,S2)) = lubTerm(applySubToSuperTerm(sub,S1),applySubToSuperTerm(sub,S2))
  | applySubToSuperTerm(sub,glbTerm(S1,S2)) = glbTerm(applySubToSuperTerm(sub,S1),applySubToSuperTerm(sub,S2))

fun applySubToConstraint(sub,identity(S1,S2)) = identity(applySubToSuperTerm(sub,S1),
						        applySubToSuperTerm(sub,S2))
 | applySubToConstraint(sub,inclusion(S1,S2)) = inclusion(applySubToSuperTerm(sub,S1),
						          applySubToSuperTerm(sub,S2))

fun applySubToConstraints(sub,clist) = map (fn c => applySubToConstraint(sub,c)) clist

fun solvedForm({complex_inclusions=[],flat_inclusions=[],identities}) = 
        let fun check(T,L) = 
		Basic.forall(L,fn c => (case c of 
					    identity(regTerm(Var(T')),regTerm(S')) => 
                	                        not(varEq(T,T')) andalso not(varOccursIn(T,S'))
					  | _ => false)) 
	     fun solved([],_,res) = SOME(res)
	       | solved((c as identity(regTerm(Var(T)),regTerm(S)))::rest,prefix,res) = 
		   if not(varOccursIn(T,S)) andalso check(T,rest) andalso check(T,prefix) 
		   then solved(rest,c::prefix,(T,S)::res)
		   else NONE
	       | solved(_) = NONE
        in
	   solved(identities,[],[])
        end
      | solvedForm(_) = NONE

val inf_counter = ref(InfNum.makeInfNum())

fun makeFreshVarCounter() =
  let val res = !inf_counter
      val _ = inf_counter := InfNum.increment(!inf_counter)
  in
     res
  end
  
fun makeFreshVar() = Var(makeFreshVarCounter())

fun makeTaggedFreshVar() = let val long_num = !inf_counter
                               val _ = inf_counter := InfNum.increment(!inf_counter)
                           in 
                              Var(InfNum.tag(long_num))
		           end

fun tagSort(App({root,args,bits})) = App({root=root,args=map tagSort args,bits=bits})
  | tagSort(Var(v)) = Var(InfNum.tag(v))

fun lubSubterms(lubTerm(e1,e2)) = (lubSubterms e1)@(lubSubterms e2)
  | lubSubterms(e) = [e]

fun glbSubterms(glbTerm(e1,e2)) = (glbSubterms e1)@(glbSubterms e2)
  | glbSubterms(e) = [e]
				
fun isSuperVar(regTerm(Var(_))) = true
  | isSuperVar(_) = false

fun makeLub([e]) = e
  | makeLub(e::rest) = lubTerm(e,makeLub(rest))
  | makeLub(_) = failLst ["Empty list of arguments given to makeLub."]

fun makeGlb([e]) = e
  | makeGlb(e::rest) = glbTerm(e,makeGlb(rest))
  | makeGlb(_) = failLst ["Empty list of arguments given to makeGlb."]

fun normalize(e as regTerm(_)) = e
  | normalize(e as lubTerm(_)) = 
			    let val lub_parts = lubSubterms(e)
                            in
			      (case Basic.decomposeList(lub_parts,isSuperVar) of
				 SOME(terms1,x,terms2) => makeLub(x::(terms1@terms2))
                               | _ => makeLub(lub_parts))
			    end
  | normalize(e as glbTerm(_)) = 
			    let val glb_parts = glbSubterms(e)
                            in
			      (case Basic.decomposeList(glb_parts,isSuperVar) of
				 SOME(terms1,x,terms2) => makeGlb(x::(terms1@terms2))
                               | _ => makeGlb(glb_parts))
			    end
     
fun isComplexInclusion(inclusion(regTerm(App(_)),regTerm(App(_)))) = true
  | isComplexInclusion(_) = false

fun makeSystem(constraints) = 
  let fun loop([],res) = res
        | loop((c as (inclusion(_)))::rest,{complex_inclusions,flat_inclusions,identities}) = 
		if isComplexInclusion(c) then 
		   loop(rest,
			{complex_inclusions=c::complex_inclusions,
			flat_inclusions=flat_inclusions,
			identities=identities})
		else
		   loop(rest,
			{complex_inclusions=complex_inclusions,
			flat_inclusions=c::flat_inclusions,
			identities=identities})
	| loop((i as (identity(_)))::rest,{complex_inclusions,flat_inclusions,identities}) = 
		   loop(rest,
			{complex_inclusions=complex_inclusions,
			flat_inclusions=flat_inclusions,
			identities=i::identities})
  in
      loop(constraints,{complex_inclusions=[],flat_inclusions=[],identities=[]})
  end 

exception solverIncompleteness

fun constraintSolver(C,subsort,lub1,glb1,from_side) = 
 let fun freshVar() = regTerm((makeFreshVar()))
     fun debugPrint(x) = print(x) 
     fun mread() = Basic.continue()
     fun freshRegVar() = makeFreshVar()
     fun buildSub(L:(variable * term) list) = makeSub(L)
     fun lub(sym1,sym2) = lub1(sym1,sym2)
     fun glb(sym1,sym2) = glb1(sym1,sym2)
     fun makeId(x,y) = (case (InfNum.tagged(x),InfNum.tagged(y)) of
                           (_,false) => identity(regTerm(Var(y)),regTerm(Var(x)))
                         | (false,_) => identity(regTerm(Var(x)),regTerm(Var(y)))
                         | _ => identity(regTerm(Var(y)),regTerm(Var(x))))
     fun solve(C as {complex_inclusions,flat_inclusions,identities}) = 
       let fun process({complex_inclusions=(ic as (inclusion(S1 as regTerm(App({root=f,args=args1,...})), 
				    S2 as regTerm(App({root=g,args=args2,...})))))::rest_complex,
			flat_inclusions,identities}) = 

                (*********** Rule [R1] ***********)

                 if subsort(f,g) then 
			let fun getNewInclusions(S1::rest1,S2::rest2,(flat,complex)) = 
				  let val c = inclusion(regTerm(S1),regTerm(S2))
				  in
				    if isComplexInclusion(c) then 
				       getNewInclusions(rest1,rest2,(flat,c::complex))
				    else 
				       getNewInclusions(rest1,rest2,(c::flat,complex))
				  end
			      | getNewInclusions(_,_,res) = res
			    val (flat,complex) = getNewInclusions(args1,args2,([],[]))
			in
			   solve({flat_inclusions=flat@flat_inclusions,
				  complex_inclusions=complex@rest_complex,
				  identities=identities})
			end
		 else (failLst ["Could not satisfy the constraint "^(printConstraint ic)^
			       "\nbecause "^(S.name(f))^" is not a subsort of "^(S.name(g))^"."])
             | process({complex_inclusions,
			flat_inclusions=(inclusion(S1,v as regTerm(Var(x))))::rest,identities}) = 

                (*********** Rule [R2] combined with [R6] ***********)

                 let fun f(inclusion(S2,regTerm(Var(y)))) = varEq(x,y)
                       | f(_) = false
                 in
                     (case Basic.decomposeList(rest,f) of
                         SOME(L1,inclusion(S2,_),L2) => 
				if superTermEq(S1,S2) then 
				   solve({complex_inclusions=complex_inclusions,
					  flat_inclusions=rest,identities=identities})
				else solve({complex_inclusions=complex_inclusions,
					    flat_inclusions=L1@[inclusion(lubTerm(S1,S2),v)]@L2,
					    identities=identities})
                       | _ => solve({complex_inclusions=complex_inclusions,
				     flat_inclusions=rest,	
				     identities=(identity(v,normalize(S1)))::identities}))
	         end
             | process({complex_inclusions,
			flat_inclusions=inclusion(v as regTerm(Var(x)),S1)::rest,identities}) = 

                (*********** Rule [R2'] combined with [R7] ***********)

                 let fun f(inclusion(regTerm(Var(y)),_)) = varEq(x,y)
                       | f(_) = false
                 in
                     (case Basic.decomposeList(rest,f) of
                         SOME(L1,inclusion(_,S2),L2) => 
				if superTermEq(S1,S2) then 
				   solve({complex_inclusions=complex_inclusions,
					  flat_inclusions=rest,identities=identities})
				else solve({complex_inclusions=complex_inclusions,
					    flat_inclusions=L1@[inclusion(v,glbTerm(S1,S2))]@L2,
					    identities=identities})
                       | _ => solve({complex_inclusions=complex_inclusions,
				     flat_inclusions=rest,	
				     identities=(identity(v,normalize(S1)))::identities}))
	         end
             | process({complex_inclusions,flat_inclusions,
			identities=(identity(S1 as regTerm(t as App(_)),S2 as regTerm(Var(x))))::rest}) =

                (*********** Rule [R8] ***********) 

                      if InfNum.tagged(x) andalso from_side >= 0 
                      then (if (true orelse isGround(t)) (** !!! **) then 
 			       solve({complex_inclusions=complex_inclusions,flat_inclusions=flat_inclusions,identities=(identity(S2,S1))::rest})
                            else failLst ["Violated sort annotation."])
                      else 
			   solve({complex_inclusions=complex_inclusions,flat_inclusions=flat_inclusions,identities=(identity(S2,S1))::rest})
             | process({complex_inclusions,flat_inclusions,
			identities=(identity(S1 as lubTerm(_),S2 as regTerm(Var(_))))::rest}) =

                (*********** Another version of [R8] ***********) 

		solve({complex_inclusions=complex_inclusions,flat_inclusions=flat_inclusions,identities=(identity(S2,S1))::rest})
             | process({complex_inclusions,flat_inclusions,
		        identities=(identity(S1 as glbTerm(_),S2 as regTerm(Var(_))))::rest}) =

                (*********** Another version of [R8] ***********) 

		solve({complex_inclusions=complex_inclusions,flat_inclusions=flat_inclusions,identities=(identity(S2,S1))::rest})
             | process({complex_inclusions,flat_inclusions,
			identities=(c1 as identity(S1 as regTerm(Var(x)),S2 as regTerm(S)))::rest}) = 

                (*********** Rule [R9] ***********) 
               let
               in
		 if varOccursIn(x,S) then
		    failLst ["Failed occurs check in the constraint "^(printConstraint c1)^"."]
		 else 
		    (if (List.exists (fn c => occursInConstraint(x,c)) 
				     (flat_inclusions@complex_inclusions@rest))
   		     then 
                         if InfNum.tagged(x) andalso from_side >= 0 andalso isUnTaggedVar(S) then
                            solve({complex_inclusions=complex_inclusions,
				       flat_inclusions=flat_inclusions,
				       identities=(identity(S2,S1))::rest})
                         else 
   	            	    let val theta = makeSub([(x,S)]) 
                                val new_identities = applySubToConstraints(theta,rest)
			    in
				solve({complex_inclusions=applySubToConstraints(theta,complex_inclusions),
				       flat_inclusions=applySubToConstraints(theta,flat_inclusions),
				       identities=new_identities@[c1]})
			    end
  		    else let
                         in
                           solve({complex_inclusions=complex_inclusions,
  			          flat_inclusions=flat_inclusions,
			          identities=rest@[c1]})
                         end)
               end
             | process({complex_inclusions,flat_inclusions,
			identities=(c1 as identity(regTerm(Var(x1)),lubTerm(regTerm(Var(y)),S1)))::rest}) = 

                (*********** Rule [R11] (second case below) in combination with [R14] (first case below) ***********) 

                 let fun f(identity(regTerm(Var(x2)),lubTerm(regTerm(Var(y')),S2))) = 
                             varEq(y',y) andalso not(superTermEq(S1,S2))
                       | f(_) = false
                 in
                     (case Basic.decomposeList(rest,f) of
                         SOME(L1,identity(regTerm(Var(x2)),lubTerm(regTerm(Var(y')),S2)),L2) => 
			    let val first_id = identity(regTerm(Var(y)),normalize(lubTerm(S1,S2)))
				val second_id = if from_side < 0 then identity(regTerm(Var(x1)),regTerm(Var(y)))
                                                else makeId(x1,y)
				val third_id = if from_side < 0 then identity(regTerm(Var(x2)),regTerm(Var(y)))
                                               else makeId(x2,y)
                            in
		               solve({complex_inclusions=complex_inclusions,
				      flat_inclusions=flat_inclusions,
  				      identities=[first_id,second_id,third_id]@rest})
			    end
                      | _ => let val (safe,other) = if not(InfNum.tagged(x1)) then (x1,y) else 
                                                    if not(InfNum.tagged(y)) then (y,x1) 
						    else (x1,y)
                             in
                                solve({complex_inclusions=complex_inclusions,
  		  		      flat_inclusions=flat_inclusions,
				      identities=[identity(regTerm(Var(safe)),S1),
				      identity(regTerm(Var(safe)),regTerm(Var(other)))]@rest})
                             end)
		end
             | process({complex_inclusions,flat_inclusions,
			identities=(c1 as identity(regTerm(Var(x1)),glbTerm(regTerm(Var(y)),S1)))::rest}) = 

                (*********** Rule [R11'] (second case below) in combination with [R14'] (first case below) ***********) 

                 let fun f(identity(regTerm(Var(x2)),glbTerm(regTerm(Var(y')),S2))) = 
                             varEq(y',y) andalso not(superTermEq(S1,S2))
                       | f(_) = false andalso false 
                 in
                     (case Basic.decomposeList(rest,f) of
                         SOME(L1,inclusion(regTerm(Var(x2)),glbTerm(regTerm(Var(y')),S2)),L2) => 
			    let val first_id = identity(regTerm(Var(y)),normalize(glbTerm(S1,S2)))
				val second_id = if from_side < 0 then identity(regTerm(Var(x1)),regTerm(Var(y)))
                                                else makeId(x1,y)
				val third_id = if from_side < 0 then identity(regTerm(Var(x2)),regTerm(Var(y)))
                                               else makeId(x2,y)
                            in
		               solve({complex_inclusions=complex_inclusions,
				      flat_inclusions=flat_inclusions,
  				      identities=[first_id,second_id,third_id]@rest})
			    end
                      | _ => let val (safe,other) = if not(InfNum.tagged(x1)) then (x1,y) else 
                                                    if not(InfNum.tagged(y)) then (y,x1) 
						    else (x1,y)
                             in
                                solve({complex_inclusions=complex_inclusions,
  		  		      flat_inclusions=flat_inclusions,
				      identities=[identity(regTerm(Var(safe)),S1),
				      identity(regTerm(Var(safe)),regTerm(Var(other)))]@rest})
                             end)
		end
             | process({complex_inclusions,flat_inclusions,
			identities=(c1 as identity(l as regTerm(Var(x)),
						   r as lubTerm(S1,S2 as regTerm(Var(y)))))::rest}) = 

                (*********** Rule [R12] ***********) 

		  (case S1 of 
		      regTerm(Var(_)) => solve({complex_inclusions=complex_inclusions,
				      		flat_inclusions=flat_inclusions,identities=rest@[c1]})
                    | _ => solve({complex_inclusions=complex_inclusions,
				  flat_inclusions=flat_inclusions,
				  identities=(identity(l,lubTerm(S2,S1)))::rest}))
             | process({complex_inclusions,flat_inclusions,
			identities=(c1 as identity(l as regTerm(Var(x)),
						   r as glbTerm(S1,S2 as regTerm(Var(y)))))::rest}) = 
                (*********** Rule [R12'] ***********) 
		  (case S1 of 
		      regTerm(Var(_)) => solve({complex_inclusions=complex_inclusions,
	  				        flat_inclusions=flat_inclusions,
						identities=rest@[c1]})
                    | _ => solve({complex_inclusions=complex_inclusions,
				  flat_inclusions=flat_inclusions,
				  identities=(identity(l,glbTerm(S2,S1)))::rest}))
             | process({complex_inclusions,flat_inclusions,
		        identities=(c1 as identity(v as regTerm(Var(x)),
                                                   lt as lubTerm(regTerm(App(_)),_)))::rest}) =
               let val deep_lub as lubTerm(regTerm(App({root=f,args=args1,...})),regTerm(App({root=g,args=args2,...}))) = findDeepLub(lt)
               in
                (*********** Rule [R13] ***********) 
		 (case lub(f,g) of
		     SOME(h) => 
				let val fresh_vars = map (fn (_) => freshRegVar()) args1
				    val identities' = map (fn (z,(s,t)) => identity(regTerm(z),lubTerm(regTerm(s),
											     regTerm(t))))
							 (Basic.zip(fresh_vars,Basic.zip(args1,args2)))
                                    val new_term = regTerm(App({root=h,args=fresh_vars,bits=varsWord}))
                                    val lt' = replaceSuperSubTerm(lt,deep_lub,new_term)
				in 
				   solve({complex_inclusions=complex_inclusions,
					  flat_inclusions=flat_inclusions,
					  identities=(identity(v,lt'))::(identities'@rest)})
				end
		   | _ => let val msg = "Could not satisfy the constraint "^(printConstraint c1)^
  			                "\nbecause "^(S.name f)^" and "^(S.name g)^" do not have a l.u.b."
                          in
                            (failLst [msg])
                          end)
              end 
             | process({complex_inclusions,flat_inclusions,
		        identities=(c1 as identity(v as regTerm(Var(x)),
                                                   lt as glbTerm(regTerm(App(_)),_)))::rest}) =
               let val deep_glb as glbTerm(regTerm(App({root=f,args=args1,...})),regTerm(App({root=g,args=args2,...}))) = findDeepGlb(lt)
               in
                (*********** Rule [R13'] ***********) 
		 (case glb(f,g) of
		     SOME(h) => 
				let val fresh_vars = map (fn (_) => freshRegVar()) args1
				    val identities' = map (fn (z,(s,t)) => identity(regTerm(z),glbTerm(regTerm(s),
											     regTerm(t))))
							 (Basic.zip(fresh_vars,Basic.zip(args1,args2)))
                                    val new_term = regTerm(App({root=h,args=fresh_vars,bits=varsWord}))
                                    val lt' = replaceSuperSubTerm(lt,deep_glb,new_term)
				in 
				   solve({complex_inclusions=complex_inclusions,
					  flat_inclusions=flat_inclusions,
					  identities=(identity(v,lt'))::(identities'@rest)})
				end
		   | _ => let val msg = "Could not satisfy the constraint "^(printConstraint c1)^
  			                "\nbecause "^(S.name f)^" and "^(S.name g)^" do not have a g.l.b."
                          in
                            (failLst [msg])
                          end)
              end 
             | process({complex_inclusions,flat_inclusions,
			identities=(c1 as (identity(S1 as regTerm(App({root=f,args=args1,...})),
		    	 	                    S2 as regTerm(App({root=g,args=args2,...})))))::rest}) = 
                (*********** Rule [R15] ***********) 
			if S.modSymEq(f,g) then
			   let val identities' = map (fn (s,t) => identity(regTerm(s),regTerm(t))) 
					             (Basic.zip(args1,args2))
			   in
			      solve({complex_inclusions=complex_inclusions,
				     flat_inclusions=flat_inclusions,
				     identities=identities'@rest})
			   end
			else
			    (failLst ["Could not satisfy the constraint "^(printConstraint c1)])
             | process(C) = raise solverIncompleteness
      in
          (case solvedForm(C) of
	      SOME(identities') => buildSub(identities')
            | _ => (case (complex_inclusions,flat_inclusions,identities) of
		      ((inclusion(S1,S2))::rest,_,_) => 
				if superTermEq(S1,S2) then 
			           solve({complex_inclusions=rest,flat_inclusions=flat_inclusions,
					  identities=identities})
				else process(C)
	            | (_,(inclusion(S1,S2))::rest,_) => 
				if superTermEq(S1,S2) then 
			           solve({complex_inclusions=complex_inclusions,
					  flat_inclusions=rest,
					  identities=identities})
				else process(C)
	            | (_,_,(identity(S1,S2))::rest) => 
				        if superTermEq(S1,S2) then 
					   solve({complex_inclusions=complex_inclusions,
					  	  flat_inclusions=flat_inclusions,			
						  identities=rest})
					   else (case S2 of
						  lubTerm(S3,S4) =>
						     if superTermEq(S3,S4) then 
							solve({complex_inclusions=complex_inclusions,
	 					  	       flat_inclusions=flat_inclusions,
							       identities=(identity(S1,S3))::rest})
						     else process(C)
					        | glbTerm(S3,S4) =>
						     if superTermEq(S3,S4) then 
							solve({complex_inclusions=complex_inclusions,
	 					  	       flat_inclusions=flat_inclusions,
							       identities=(identity(S1,S3))::rest})
						     else process(C)
                                                | _ => process(C))
		   | _ => raise Basic.Never)) (* If there are no inclusions and no identities then the system *)
					      (* would have been recognized as being in solved form already.  *)
       end
 in
   solve(C)
 end

fun standardSolver(C,from_side) = 
      (constraintSolver(C,SortOrder.areSubsorts,SortOrder.lub,SortOrder.glb,from_side))

fun subsortUnifyExWithConstraintSolving(S1,S2,from_side) = 
	let val system = makeSystem [inclusion(regTerm(S1),regTerm(S2))]
        in
  	   standardSolver(system,from_side)
	end

fun subsortUnifyExLstWithConstraintSolving(sorts1,sorts2,from_side) = 
       (let val system = makeSystem(map (fn (S1,S2) => inclusion(regTerm(S1),regTerm(S2)))
	                                (Basic.strictZip(sorts1,sorts2)))
         in
	    standardSolver(system,from_side)
        end) handle _ => failLst ["Wrong number of arguments supplied to term constructor."]

fun isSubSort(S1,S2) = SOME(subsortUnifyExWithConstraintSolving(S1,S2,1)) handle _ => NONE

fun isSubSortBool(S1,S2) = (case isSubSort(S1,S2) of SOME(_) => true | _ => false)

fun areSubSorts(sort_lst1,sort_lst2) = 
	SOME(subsortUnifyExLstWithConstraintSolving(sort_lst1,sort_lst2,1)) handle _ => NONE

fun haveOrderSortedDomains(terms) = Basic.exists(terms,findOutDynamicallyIfASortHasOrderSortedSymbolsInIt)

fun subsortUnifyExDefault(sort1,sort2,from_side) = subsortUnifyEx(sort1,sort2,SortOrder.areSubsorts,from_side)

fun  subsortUnifyExLstDefault(sorts1,sorts2,from_side) = 
     	  subsortUnifyExLst(sorts1,sorts2,SortOrder.areSubsorts,from_side)

fun chooseUnificationProcedureForSorts(param_sort,arg_sort) = 
       let val os = findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(arg_sort) orelse 
                    findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(arg_sort) 
       in 
          if os andalso not(isGround(param_sort) andalso isGround(arg_sort))  
          then subsortUnifyExLstWithConstraintSolving
	  else subsortUnifyExLstDefault
       end

fun chooseUnificationProcedureForSortLists(param_sorts,arg_sorts) = 
       let val (os,poly) = (ref false,ref false)
	   fun loop([],[]) = ()
             | loop(psort::more_psorts,asort::more_asorts) = 
		 if findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(asort)
		    orelse findOutDynamicallyIfASortHasOrderSortedSymbolsInIt(psort) then
		    (os := true;
		     if !poly then failLst[] else 
			(poly := not(isGround(psort) andalso isGround(asort));
			 if !poly then (failLst []) else 
			    loop(more_psorts,more_asorts)))
		 else 
		     (if isGround(psort) andalso isGround(asort) 
		      then loop(more_psorts,more_asorts)
		      else (poly := true;
			    if !os then failLst([]) else loop(more_psorts,more_asorts)))
	     | loop(_) = failLst([])
           val _ = loop(param_sorts,arg_sorts) handle _ => ()
       in 
          if (!os andalso !poly) then subsortUnifyExLstWithConstraintSolving
	  else subsortUnifyExLstDefault 
       end

fun U_d(sorts1,sorts2,i) = SOME(subsortUnifyExLstDefault(sorts1,sorts2,i)) handle _ => NONE
fun U_s(sorts1,sorts2,i) = SOME(subsortUnifyExLstWithConstraintSolving(sorts1,sorts2,i)) handle _ => NONE

val (match,matchModuloSub,matchLst,matchLstModuloSub) = 
          let fun m(App({root=fsym1,args=args1,...}),
		    App({root=fsym2,args=args2,...}),sub) = 
			if SortOrder.areSubsorts(fsym1,fsym2) then mLst(args1,args2,sub) 
			else failLst([])
                | m(s,t as Var(v),sub) = 
                     if inSupp(v,sub) then
                        if termEq(s,applySub(sub,t)) then sub else 
			   failLst([])
                     else
                        sub++(v,s)  
                | m(_,_,_) = failLst([])
              and mLst(s::more1,t::more2,sub) = mLst(more1,more2,m(s,t,sub))
                | mLst([],[],sub) = sub
                | mLst(_,_,_) = failLst([])
          in
            ((fn (s,t) => let val sub_opt = SOME(m(s,t,empty_sub)) handle _ => NONE 
                          in
                             sub_opt
                          end),
             (fn (s,t,sort_sub) => let 
                                   in m(s,t,sort_sub)
                                   end),
             (fn (slst,tlst) => let val sub_opt = SOME(mLst(slst,tlst,empty_sub)) handle _ => NONE 
                                in
                                   sub_opt
                                end),
             (fn (slst,tlst,sort_sub) => mLst(slst,tlst,sort_sub)))
  
          end          

(** The following returns true if s matches the pattern t, and false otherwise **)

fun matches(s,t) = case match(s,t) of NONE => false | _ => true
       
val isInstanceOf = matches

fun variants(s,t) = matches(s,t) andalso matches(t,s)

val (variants1,variants1Lst) =
     
(*** NOTE: variants1 and variants1Lst work correctly only under the assumption that  ****)
(*** the input terms have no variables in common. This is true for sort terms, since ****)
(*** sort variables are freshly generated.                                           ****)

let fun appSubs(sub1,sub2,x) = if inSupp(x,sub1) then applySub(sub1,Var x) 
			       else if inSupp(x,sub2) then applySub(sub2,Var x) else Var(x)
    fun defined(x,sub1,sub2) = inSupp(x,sub1) orelse inSupp(x,sub2)
    fun f(t1 as Var(x),t2 as Var(y),sub1,sub2) = 
	           if defined(x,sub1,sub2) orelse defined(y,sub1,sub2) then 
		      (if termEq(appSubs(sub1,sub2,x),Var(y)) andalso termEq(appSubs(sub1,sub2,y),Var(x))
		       then SOME(sub1,sub2) else NONE)
		   else SOME(sub1++(x,t2),sub2++(y,t1))
      | f(App({root=g,args=args1,...}),App({root=h,args=args2,...}),sub1,sub2) = 
	           if fsymEq(g,h) then fLst(args1,args2,sub1,sub2) else NONE
      | f(_) = NONE
and
        fLst([],[],sub1,sub2) = SOME(sub1,sub2)
      | fLst(s1::rest1,s2::rest2,sub1,sub2) = 
                   (case f(s1,s2,sub1,sub2) of
		       SOME(sub1',sub2') => fLst(rest1,rest2,sub1',sub2')
		     | _ => NONE)
      | fLst(_) = NONE  
in
  (fn (s,t) => 	   
      (case f(s,t,empty_sub,empty_sub) of
          SOME(_) => true
        | _ => false),
   fn (terms1,terms2) =>
      (case fLst(terms1,terms2,empty_sub,empty_sub) of
          SOME(_) => true
        | _ => false))
end

fun sortEq(t1,t2) = if isGround(t1) andalso isGround(t2) then termEq(t1,t2) 
	            else (if not(isGround(t1)) andalso not(isGround(t2)) then variants(t1,t2)
  		          else false)

fun getGlb(sort1,sort2) =  
       let val new_var = regTerm((makeFreshVar()))
           val identity_constraint = identity(new_var,glbTerm(regTerm(sort1),regTerm(sort2)))
	   val system = makeSystem [identity_constraint]
           val res_sub = standardSolver(system,1)
       in
          res_sub
       end

fun getGlbModuloVarSort(var_sort,sort1,sort2) = 
       let val disagreements = ref(false)
           val _ = if sortEq(sort1,sort2) then () else disagreements := true
	   val identity_constraint = identity(regTerm var_sort,glbTerm(regTerm(sort1),regTerm(sort2)))
	   val system = makeSystem [identity_constraint]
           val res_sub = standardSolver(system,1)
       in
          (res_sub,!disagreements)
       end

fun getGlbWithGroundInfo(var_sort,sort1,sort2,sort1_ground,sort2_ground,both_ground) = 
       let val disagreements = ref(false)
           fun eqSorts() = if both_ground then termEq(sort1,sort2) else 
                           (if  not(sort1_ground) andalso not(sort2_ground) then variants(sort1,sort2) else false)
           val _ = if eqSorts() then () else disagreements := true
	   val identity_constraint = identity(regTerm var_sort,glbTerm(regTerm(sort1),regTerm(sort2)))
	   val system = makeSystem [identity_constraint]
           val res_sub = standardSolver(system,1)
       in
          (res_sub,!disagreements)
       end

fun getLub(var_sort,sort1,sort2,sort1_ground,sort2_ground,both_ground) = 
       let val disagreements = ref(false)
           fun eqSorts() = if both_ground then termEq(sort1,sort2) else 
                           (if  not(sort1_ground) andalso not(sort2_ground) then variants(sort1,sort2) else false)
           val _ = if eqSorts() then () else disagreements := true
	   val identity_constraint = identity(regTerm var_sort,lubTerm(regTerm(sort1),regTerm(sort2)))
	   val system = makeSystem [identity_constraint]
           val res_sub = standardSolver(system,1)
       in
          (res_sub,!disagreements)
       end
       
fun coerceSubsorts(S1,S2) = 
 let fun f(S1 as App({root=root1,args=args1,bits=bits1,...}),
	   S2 as App({root=root2,args=args2,bits=bits2,...})) = 
		if (Word8.andb(bits1,0w1)) = (Word8.andb(bits2,0w1)) then
		   (if SO.areSubsorts(root1,root2) then
			let val (args1',args2') = Basic.unZip(map  f (Basic.zip(args1,args2)))
			in
			  (App({root=root1,args=args1',bits=bits1}),App({root=root1,args=args2',bits=bits2}))
			end
  		    else
		         (failLst []))
		else (failLst [])
       | f(S1 as Var(_),S2 as Var(_)) = (S1,S2)
       | f(_) = (failLst [])
 in
   {coerced_sorts=SOME(f(S1,S2)),reversed=false} 
	handle _ => ({coerced_sorts=SOME(f(S2,S1)),reversed=true} 
			handle _ => {coerced_sorts=NONE,reversed=false})
 end

val (renameAux,renameLstAux) = 
  let fun f(App({root,args,bits}),m) = let val (args',m') = fLst(args,m,[])
				       in 
				         (App({root=root,args=args',bits=bits}),m')
				        end
         | f(Var(v),m) = (case InfIntMapTable.look(m,v) of
			    SOME(v') => (v',m)
			  | _ => let val v' = makeFreshVar()
				 in
				    (v',InfIntMapTable.enter(m,v,v'))
				 end)
     and fLst([],m,res) = (rev res,m)
       | fLst(t::rest,m,res) = let val (t',m') = g(t,m)
			       in
			         fLst(rest,m',t'::res)
			       end
     and g(t,m) =  if hasVars(t) then f(t,m) else (t,m) 
  in
     (fn (t,m) => g(t,m),fn (terms,m) => fLst(terms,m,[]))
  end

val (rename,renameLst) = (fn t => #1(renameAux(t,InfIntMapTable.empty)),
                          fn terms => #1(renameLstAux(terms,InfIntMapTable.empty)))

val boolean_sort = App({root=Names.mboolean_sort_symbol,args=[],bits=zeroWord})

val int_sort = App({root=Names.mint_sort_symbol,args=[],
		    bits=makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=true,hasVars=false})})

val real_sort = App({root=Names.mreal_sort_symbol,args=[],
		    bits=makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=true,hasVars=false})})

val ide_sort = App({root=Names.mide_sort_symbol,args=[],
		    bits=makeWord({hasPredBasedSorts=false,hasPolyOSD=false,hasOSD=false,hasVars=false})})

fun makeMonoSortSub(vars) = makeSub (map (fn v => (v,int_sort)) vars)

fun resolveSorts(S1:term,S2:term) = getGlb(S1,S2)

fun unifySorts(S1:term,S2:term) = unifyEx(S1,S2)

(** Here the sort S1 must be a subsort of S2: **)
fun unifySubSorts(S1:term,S2:term) = subsortUnifyExWithConstraintSolving(S1,S2,1)

val translateFromSymTermWithSortVarMapAux = 
      let fun f(sort_as_symterm,sort_var_map) = 
   		(case SymTerm.isVar(sort_as_symterm) of 
		    SOME(v) => (case Symbol.lookUp(sort_var_map,v) of 
				   SOME(v') => (v',sort_var_map)
				 | _ => (let val v' = makeFreshVar() 
					 in
					    (v',Symbol.enter(sort_var_map,v,v'))
					 end))
    	          | _ => (case SymTerm.isApp(sort_as_symterm) of
		             SOME(fsym,sorts) => let val (sorts',sort_var_map') = fLst(sorts,sort_var_map,[])
			        	         in
					           (makeApp(fsym,sorts'),sort_var_map')
				                 end
   		           | _ => raise Basic.Never))
        and fLst(s::rest,m,res) = let val (s',m') = f(s,m) 
				  in
				      fLst(rest,m',s'::res)
				  end
          | fLst([],m,res) = (rev res,m)
      in
        f
      end

fun translateFromSymTerm(sort_as_symterm) =        
          #1(translateFromSymTermWithSortVarMapAux(sort_as_symterm,Symbol.empty_mapping))

fun translateFromSymTermWithSortVarMap(sort_as_symterm,mapping) =        
          #1(translateFromSymTermWithSortVarMapAux(sort_as_symterm,mapping))

end (**  of "abstype term with..."  **)

end (** of FTerm struct **)
