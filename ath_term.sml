(*======================================================================

Implementation of Athena terms (satisfying the ATHENA_TERM signature).

=======================================================================*)

structure AthTerm: ATHENA_TERM = 

struct 

structure S = ModSymbol

structure A = AbstractSyntax

structure F = FTerm

structure D = Data

structure N = Names

structure MS = ModSymbol

structure ATV = AthTermVar
 
type variable = ATV.ath_term_var

type sort = FTerm.term

type fsymbol = MS.mod_symbol

val varEq = ATV.athTermVarEq

val fsymEq = MS.modSymEq

val failLst = Basic.failLst

fun msym(s) = ModSymbol.makeModSymbol([],s,s)

abstype term = Var of variable  
             | App of {root: fsymbol,
	       	       args: term list,
		       sort: sort,
		       bits: Word8.word,
		       hash_code:Word.word, 
		       vars: variable list,
		       poly_constants: (fsymbol * sort) list }  
             | numTerm of A.ath_number  
             | ideTerm of MetaId.meta_id

with 

(************************************************************************************
                      Info on term bit fields

Every tree-structured Athena term has a word attached to its root. The bits
of that word provide fast access to a host of information about the term,
which in turn speeds up many operations. (For instance, suppose we need
to apply a substitution to a very large term t. If we can tell that t is
ground in O(1) time then we avoid traversing t, thereby saving a lot of time.)

The lowest bit is the "poly field". It denotes whether or not the term has 
*any* subterms with polymorphic sorts, i.e., any subterm t such that 
FTerm.not(isGround(getSort(t))).

The next highest bit is the "has-vars field". This denotes whether the
term has variables, i.e. whether it's not ground. This seems roundabout --
why not keep a "ground" bit? The reason is that with the two lowest bits
set like this, we can very quickly compute the word of a new term
when we apply a function symbol f to terms t1,...,tn: we compute
the "or" of the words of t1,...,tn. 

The next highest bit is the "is-non-canonical" field.
This denotes whether the term is non-canonical, where a canonical
term is one that only contains constructors and possibly numerals. 
This is again represented in a roundabout way to enable 
quick "or"-ing. 

Finally, the highest bit indicates whether or not the term
contains any sorts that are predicate-based. More precisely: 
whether or not the term contains any subterm (f ...) where
the signature of f involves a domain that has a sort predicate. 

Hence, a word is interpreted according to the following
scheme, on the basis of its last three bits:

0000 --> canonical, ground, monomorphic, no predicate-based sorts
1000 --> canonical, ground, monomorphic, with predicate-based sorts

0001 --> canonical, ground, polymorphic, no predicate-based sorts
1001 --> canonical, ground, polymorphic, with predicate-based sorts

0010 --> cannot arise, as all canonical terms are ground 
1010 --> cannot arise, as all canonical terms are ground 

0100 --> non-canonical, ground, monomorphic, no predicate-based sorts
1100 --> non-canonical, ground, monomorphic, with predicate-based sorts

0011 --> cannot arise, same reason as above
1011 --> cannot arise, same reason as above

0101 --> non-canonical, ground, polymorphic, no predicate-based sorts
1101 --> non-canonical, ground, polymorphic, with predicate-based sorts

0110 --> non-canonical, non-ground, monomorphic, no predicate-based sorts
1110 --> non-canonical, non-ground, monomorphic, with predicate-based sorts

0111 --> non-canonical, non-ground, polymorphic, no predicate-based sorts
1111 --> non-canonical, non-ground, polymorphic, with predicate-based sorts

************************************************************************************)

val orWords = Word8.orb
 
fun isPolyWord(w:Word8.word) = (Word8.andb(w,0w1) = 0w1)

fun isPoly(Var(v)) = ATV.isPoly(v)
  | isPoly(App({bits,...})) = isPolyWord(bits)
  | isPoly(_) = false 

fun hasVarsWord(w:Word8.word) = (Word8.andb(w,0w2) = 0w2)

fun isNonCanonicalWord(w:Word8.word) = (Word8.andb(w,0w4) = 0w4)

fun hasVars(Var(_)) = true
  | hasVars(App{bits,...}) = hasVarsWord(bits)
  | hasVars(_) = false

fun hasTaggedSortVars(Var(v)) = ATV.isTagged(v) 
  | hasTaggedSortVars(App({sort,args,...})) = F.someTaggedVars(sort) orelse (List.exists hasTaggedSortVars args)
  | hasTaggedSortVars(_) = false

fun makeWord({involves_pred_based_sorts=false,non_canonical=false,hasVars=false,poly=false}):Word8.word = 0w0  (* value of 0 *)
  | makeWord({involves_pred_based_sorts=true,non_canonical=false,hasVars=false,poly=false}):Word8.word = 0w8   (* value of 8 *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=false,hasVars=false,poly=true}):Word8.word = 0w1   (* value of 1 *)
  | makeWord({involves_pred_based_sorts=true,non_canonical=false,hasVars=false,poly=true}):Word8.word = 0w9    (* value of 9 *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=false,hasVars=true,poly=false}):Word8.word = 0w2    (* value of 2; cannot arise *)
  | makeWord({involves_pred_based_sorts=true, non_canonical=false,hasVars=true,poly=false}):Word8.word = 0w10    (* value of 10; cannot arise *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=false,hasVars=true,poly=true}):Word8.word = 0w3     (* value of 3; cannot arise *)
  | makeWord({involves_pred_based_sorts=true, non_canonical=false,hasVars=true,poly=true}):Word8.word = 0w11    (* value of 11; cannot arise *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=true,hasVars=false,poly=false}):Word8.word = 0w4    (* value of 4 *)
  | makeWord({involves_pred_based_sorts=true, non_canonical=true,hasVars=false,poly=false}):Word8.word = 0w12   (* value of 12 *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=true,hasVars=false,poly=true}):Word8.word = 0w5     (* value of 5 *)
  | makeWord({involves_pred_based_sorts=true, non_canonical=true,hasVars=false,poly=true}):Word8.word = 0w13    (* value of 13 *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=true,hasVars=true,poly=false}):Word8.word = 0w6     (* value of 6 *)
  | makeWord({involves_pred_based_sorts=true, non_canonical=true,hasVars=true,poly=false}):Word8.word = 0w14    (* value of 14 *)

  | makeWord({involves_pred_based_sorts=false,non_canonical=true,hasVars=true,poly=true}):Word8.word = 0w7      (* value of 7 *)
  | makeWord({involves_pred_based_sorts=true, non_canonical=true,hasVars=true,poly=true}):Word8.word = 0w15     (* value of 15 *)

val zeroWord:Word8.word = 0w0
val polyWord:Word8.word = 0w1

val varsWord:Word8.word = 0w6  (* If it has vars it's non-canonical, so 6 instead of 2 is now the right value for this mask. *)
val hasPredBasedSortsWord:Word8.word = 0w8 
    
val nonCanonicalWord:Word8.word = 0w4

fun isCanonical(App({bits,...})) = not(isNonCanonicalWord(bits))
  | isCanonical(numTerm(_)) = true
  | isCanonical(_) = false

fun involvesPredBasedSortsWord(w:Word8.word) = (Word8.andb(w,0w8) = 0w8)

fun getBits(App({bits,...})) = bits

fun involvesPredBasedSorts(Var(v)) = F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(ATV.getSort(v))
  | involvesPredBasedSorts(App({bits,...})) = involvesPredBasedSortsWord(bits)
  | involvesPredBasedSorts(_) = false

fun involvePredBasedSorts(terms) = List.exists involvesPredBasedSorts terms

fun compareNums(A.int_num(i,_),A.int_num(j,_)) = Int.compare(i,j)
  | compareNums(A.int_num(i,_),A.real_num(_)) = LESS
  | compareNums(A.real_num(i,_),A.real_num(j,_)) = Real.compare(i,j)
  | compareNums(A.real_num(i,_),A.int_num(_)) = GREATER

fun compare(ideTerm(x),ideTerm(y)) = MetaId.compare(x,y)
  | compare(ideTerm(x),_) = LESS
  | compare(Var(x),Var(y)) = ATV.compare(x,y)
  | compare(Var(x),ideTerm(_)) = GREATER
  | compare(Var(x),_) = LESS
  | compare(numTerm(s),numTerm(t)) = compareNums(s,t) 
  | compare(numTerm(s),App(_)) = LESS
  | compare(numTerm(s),_) = GREATER
  | compare(App({root=root1,args=args1,...}),App({root=root2,args=args2,...})) = 
       let val c = Int.compare(MS.code(root1),MS.code(root2))
       in
          if c = EQUAL then Basic.lexOrder(args1,args2,compare) else c
       end
  | compare(App(_),_) = GREATER

fun fastHash(Var(v)) = ATV.hash(v)
  | fastHash(App({hash_code,...})) = hash_code
  | fastHash(numTerm(A.int_num(i,_))) = Basic.hashInt(i)
  | fastHash(numTerm(A.real_num(r,_))) = Basic.hashString(Real.toString(r))
  | fastHash(ideTerm(x)) = MetaId.hash(x)


fun isTrueTerm(App({root,...})) = MS.modSymEq(root,N.mtrue_logical_symbol)
  | isTrueTerm(_) = false

fun isFalseTerm(App({root,...})) = MS.modSymEq(root,N.mfalse_logical_symbol)
  | isFalseTerm(_) = false

fun sizeCumulative(App({args,...}),n) = sizeLst1(args,n+1) 
  | sizeCumulative(_,n) = n + 1
and sizeLst1([],n) = n
  | sizeLst1(t::more,n) = sizeLst1(more,sizeCumulative(t,n))

fun size(t) = sizeCumulative(t,0)

fun sizeLst(terms) = sizeLst1(terms,0)

fun getSort(App({sort,...})) = sort
  | getSort(Var(v)) = ATV.getSort(v)
  | getSort(numTerm(A.int_num(_))) = D.int_sort
  | getSort(numTerm(A.real_num(_))) = D.real_sort
  | getSort(ideTerm(_)) = D.ide_sort 



val global_tccs:(term * sort) list ref = ref([])

val (termSymbols,termSymbolsLst) = 
       let fun f(App({root,args,...})) = fLst(args,[root])
             | f(_) = []
           and fLst([],res) = res
             | fLst(t::more,res) = fLst(more,(f t)@res)
       in
          (fn t => f(t),fn L => fLst(L,[]))
       end

fun termSymbolsFastAux(t:term,ht:MS.mod_symbol MS.htable) = 
         let fun loop(App({root,args,...})) = (MS.insert(ht,root,root);List.app loop args)
               | loop(_) = ()  
          in
             loop(t)
          end
fun termSymbolsFast(t) = 
       let val ht: MS.mod_symbol MS.htable = MS.makeHTable() 
           val _ = termSymbolsFastAux(t,ht)
       in
         MS.listItems(ht)
       end
fun termSymbolsLstFast(terms) = 
       let val ht: MS.mod_symbol MS.htable = MS.makeHTable() 
           val _ = List.app (fn t => termSymbolsFastAux(t,ht)) terms
       in
         MS.listItems(ht)
       end

fun tagTerm(App({root,args,sort,bits,vars,hash_code,poly_constants,...})) = 
            App({root=root,args = map tagTerm args,sort=F.tagSort(sort),bits=bits,vars=map ATV.tagVar vars,hash_code=hash_code,
                 poly_constants=map (fn (c,sort) => (c,F.tagSort(sort))) poly_constants})
       | tagTerm(Var(v)) = Var(ATV.tagVar(v))
                                                           
     datatype term_root = NUM of A.ath_number | META_ID of string | FSYM of fsymbol | TERM_VAR of variable

fun termRootToString(tr) = 
        let val (lparen,rparen,comma) = (Basic.lparen,Basic.rparen,Basic.comma)
            fun f(TERM_VAR(v)) = "TERM_VAR"^lparen^(ATV.toStringDefault v)^rparen
             | f(FSYM(f)) = "FSYM"^lparen^(S.name(f))^rparen
             | f(META_ID(str)) = "META_ID"^lparen^str^rparen
             | f(NUM(a)) = "NUM"^lparen^(A.athNumberToString(a))^rparen
        in
           f tr
        end

fun termRoot(App({root,...})) = FSYM(root)
  | termRoot(Var(v)) = TERM_VAR(v)
  | termRoot(numTerm(a)) = NUM(a)
  | termRoot(ideTerm(x)) = META_ID(MetaId.name(x))


fun termChildren(App({args,...})) = (List.map termRoot args)
  | termChildren(_) = []
 
fun sortOfVarInTerm(v,Var(v')) = if ATV.nameEq(v,v) then SOME(ATV.getSort(v')) else NONE
   | sortOfVarInTerm(v,App({vars,...})) =  
        (case Basic.findInList(vars,fn v' => ATV.nameEq(v,v')) of
            SOME(v') => SOME(ATV.getSort(v'))
          | _ => NONE)
   | sortOfVarInTerm(_) = NONE

fun getVars(App({vars,...})) = vars
  | getVars(Var(v)) = [v]
  | getVars(_) = []

fun getVarsIO(Var(v)) = [v]
  | getVarsIO(App({args,...})) = getVarsIOLst(args,[])
  | getVarsIO(_) = []
and getVarsIOLst([],res) = List.foldl op@ [] res 
  | getVarsIOLst(t::more,res) = getVarsIOLst(more,(getVarsIO t)::res)

fun weedOutDups(vars) = 
  let val T = ATV.makeHTableWithVarEq(ATV.nameEq)
      fun loop([],res) = rev(res)
        | loop(v::more,res) = 
              (case ATV.find(T,v) of
                  SOME(_) => loop(more,res)
                | _ => (ATV.insert(T,v,v);loop(more,v::res)))
  in
     loop(vars,[])
  end

fun getVarsInOrder(t) = weedOutDups(getVarsIO(t))
     
fun getVarsInOrderLst(terms) = weedOutDups(getVarsIOLst(terms,[]))

fun getVarsLst(terms) = 
		let fun f(t::more,res) = f(more,(getVars t)@res)
                      | f([],res) = Basic.removeDuplicatesEq(res,varEq)
                in
		   f(terms,[])
		end

fun height(App({args as _::_,...})) = 1 + Basic.maxLst(map height args)
  | height(_) = 0

val mlprint = fn x => ()

fun getNumVal(t) = 
      let fun f(numTerm(a),negative) = SOME(a,negative)
            | f(App({root,args=[t],...}),negative) = 
		if MS.modSymEq(root,Names.msubtraction_symbol) then f(t,not negative) else 
		if MS.modSymEq(root,Names.maddition_symbol) then f(t,negative) else NONE
           | f(_) = NONE
      in
	f(t,false)
      end

fun constantSymToString(fsym,sort,printSortVar) = 
	  let val (_,res_sort,is_poly,has_pred_based_sorts) = Data.getSignature(fsym)
	      val str = S.name fsym
	      val tagged_str = str^":"^(F.toString(sort,printSortVar))
	  in
	     if not(!Options.print_var_sorts) then str
	     else (if is_poly then tagged_str
	          else (if not(F.sortEq(sort,res_sort)) then tagged_str else str))
	  end

fun makeInternalAppTerm(f,args,hc,sort,bits,pc,vs) =
  App({root=f,args=args,hash_code=hc,sort=sort,bits=bits,poly_constants=pc,vars=vs})
                                                          
fun constantSymToPrettyString(start,fsym,sort,printSortVar) = 
	  let val (_,res_sort,is_poly,_) = Data.getSignature(fsym)
	      val str = S.name fsym
	      val len = String.size str 
	      val tagged_str = str^":"^(F.toPrettyString(start+len+1,sort,printSortVar))
	  in
	     if not(!Options.print_var_sorts) then str
	     else (if is_poly then tagged_str
 	           else (if not(F.sortEq(sort,res_sort)) then tagged_str else str))
	  end

fun toString(t,printSortVar) = 
       let fun f(Var(v)) = ATV.toString(v,printSortVar)
             | f(numTerm(n)) = A.athNumberToString(n)
             | f(ideTerm(x)) = Names.metaIdPrefix^(MetaId.name(x))
             | f(App({root,args as [],sort,...})) = constantSymToString(root,sort,printSortVar)
             | f(App({root,args,...})) = "("^MS.name(root)^(Basic.blank)^Basic.printSExpListStr(args,f)^")"
             					 
       in
         f t
       end

fun toStringDefault(t) = toString(t,F.varToString)

fun tccToString((t,sort)) = (toStringDefault(t))^" :: "^(F.toStringDefault(sort))

fun tccsToString(tccs) = Basic.printListStr(tccs,tccToString,"\n")

fun jsonLeaf(t,subtype) = JSON.OBJECT([("type", JSON.STRING("term")),
	   	 		       ("subtype", JSON.STRING(subtype)),
	  	 		       ("root", JSON.STRING(toStringDefault(t))),
	  	 		       ("children", JSON.ARRAY([]))])

fun toJson(t as numTerm(_)) = jsonLeaf(t,"number")
  | toJson(t as ideTerm(_)) = jsonLeaf(t,"ide")
  | toJson(t as Var(v)) = ATV.toJson(v)
  | toJson(t as App({root,args,sort,...})) = 
     let val root_str:string = MS.name(root)
     in
	 JSON.OBJECT([("type", JSON.STRING("term")),
	   	      ("subtype", JSON.STRING("application")),
	  	      ("root", JSON.STRING(root_str)),
	  	      ("children", JSON.ARRAY((map toJson args)))])
     end

fun toPrettyString(start,t,printSortVar) = 
       let fun pp(s,Var(v)) = ATV.toPrettyString(s,v,printSortVar)         
             | pp(s,App({root,args as [],sort,...})) = constantSymToPrettyString(s,root,sort,printSortVar)
             | pp(s,App({root,args,...})) = 
			let val str = MS.name(root)
                            val break_up = List.exists (fn t => (height(t) > 0 
								 orelse F.height(getSort(t)) > 0)) args
			in
                            (Basic.lparen)^str^(Basic.blank)^
			     ppArgs(s+String.size(str)+2,args,break_up)^(Basic.rparen)
                        end
             | pp(s,t) = toString(t,printSortVar)
          and ppArgs(s,args,false) = Basic.printSExpListStr(args,fn t => toString(t,printSortVar))
            | ppArgs(s,args,true) = doArgs(s,args)
          and doArgs(s,[]) = ""
            | doArgs(s,[t]) = pp(s,t)
            | doArgs(s,t1::t2::more) = pp(s,t1)^Basic.new_line^Basic.spaces(s)^doArgs(s,t2::more)
       in
          pp(start,t)
       end

fun toPrettyStringDefault(s,t) = toPrettyString(s,t,F.varToString)

fun showTerms(terms) = Basic.printLnList(terms,fn t => toPrettyString(0,t,F.varToString))

fun showVars([]) = ()
  | showVars(vars::rest) = (List.app (fn v => (print(ATV.toPrettyString(0,v,F.varToString));print("\n"))) vars;
			    if null(rest) then print("\n") else print("\nand\n");
			    showVars(rest))

fun fauxTermToPrettyString(start,f,args) = 
  let val sortVarPrinter = F.makeVarSortPrinter()
      val str = MS.name(f)
      val break_up = List.exists (fn t =>  height(t) > 0) args
      fun doArgs(s,[]) = ""
        | doArgs(s,[t]) = toPrettyString(s,t,sortVarPrinter)
        | doArgs(s,t1::t2::more) = (toPrettyString(s,t1,sortVarPrinter))^
				   Basic.new_line^Basic.spaces(s)^(doArgs(s,t2::more))
     and ppArgs(s,args,false) = Basic.printSExpListStr(args,fn t => toString(t,sortVarPrinter))
       | ppArgs(s,args,true) = doArgs(s,args)
  in
    "("^str^" "^ppArgs(start+String.size(str)+2,args,break_up)^")"
  end

fun bitsToString(w:Word8.word) = 
  (case w of

      0w0 => "Pred-Based-sorts: no, canonical:yes, poly: no, vars: no"
    | 0w1 => "Pred-Based-sorts: no, canonical:yes, poly: yes, vars: no"
    | 0w2 => "(Should not arise!) Pred-Based-sorts: no, canonical:yes, poly: no, vars: yes"
    | 0w3 => "(Should not arise!) Pred-Based-sorts: no, canonical:yes, poly: yes, vars: yes"
    | 0w4 => "Pred-Based-sorts: no, canonical: no, poly: no, vars: no"
    | 0w5 => "Pred-Based-sorts: no, canonical: no, poly: yes, vars: no"
    | 0w6 => "Pred-Based-sorts: no, canonical: no, poly: no, vars: yes"
    | 0w7 => "Pred-Based-sorts: no, canonical: no, poly: yes, vars: yes"
    | 0w8 => "Pred-Based-sorts: no, canonical: yes, poly: no, vars: no"
    | 0w9 => "Pred-Based-sorts: yes, canonical: yes, poly: yes, vars: no"
    | 0w10 => "Pred-Based-sorts: yes, canonical: yes, poly: no, vars: yes"
    | 0w11 => "(Should not arise!): Pred-Based-sorts: yes, canonical: yes, poly: yes, vars: yes"
    | 0w12 => "Pred-Based-sorts: yes, canonical: yes, poly: no, vars: no"
    | 0w13 => "Pred-Based-sorts: yes, canonical: yes, poly: yes, vars: no"
    | 0w14 => "Pred-Based-sorts: yes, canonical: yes, poly: no, vars: yes"
    | 0w15 => "Pred-Based-sorts: yes, canonical: yes, poly: yes, vars: yes"
    | _ =>   "Invalid word (greater than 15)")	

fun showBits(Var(_)) = ""
  | showBits(App({bits,...})) = bitsToString(bits)
  | showBits(_) = ""

fun displayTerm(t) = (print("\nTerm: "^(toPrettyString(7,t,F.varToString)));
		      print("\nIts sort: "^(F.toString(getSort(t),F.varToString)));
		      (case t of
                          App({bits,...}) => print("\nIts bits are given by the word: " ^ (Word8.toString(bits)) ^ ", which is interpreted as: "^(showBits t))
                        | _ => print("\nNo bits...\n"));
		      print("\nIts variables: ");showVars([getVars(t)]);print("\n"))

val display = displayTerm

fun displayLst(terms) = List.app display terms

fun makeConservativeName(str) = 
     let fun normalChar c =  Char.isAlphaNum(c) orelse Char.ord(c) = 95 
	 fun f(c) = if normalChar(c) then Char.toString(c) else 
  		    "b_"^(Int.toString(Char.ord(c)))^"_b"
         val cl = String.explode str
     in
	List.foldr (op^) "" (map f cl)
     end

fun makeTPTPTerm(t,fvars) =
     let fun f(Var(v)) = let val vname = ATV.name(v)
                             val cvn =  makeConservativeName(vname)
			 in
                            if Basic.isMemberEq(v,fvars,ATV.nameEq) then 
			       "a"^cvn else "X"^cvn
                         end
           | f(numTerm(an as A.int_num(_))) = 
                              let val cname = A.athNumberToString(an)
			      in 
                                 cname 
                              end
           | f(numTerm(an as A.real_num(r,str))) = 
                     let val cname = let val (floor,ceil) = (Int.toString(Real.floor(Real.realFloor(r))),Int.toString(Real.ceil(Real.realCeil(r))))
                                     in "r"^floor^ceil  end
		     in 
                        cname 
                     end
           | f(ideTerm(x)) = "ident"^(makeConservativeName(MetaId.name(x)))
           | f(App({root,args as [],...})) = "a"^( makeConservativeName(MS.name(root)))
           | f(App({root,args,...})) =  let val is_eq = MS.modSymEq(root,Names.mequal_logical_symbol)
                                            val fname = if is_eq then "equal" else 
						  makeConservativeName("f"^(MS.name(root)))
				  in                                                       
				     fname^"("^fLst(args)^")"
				  end
         and
             fLst([]) = ""
           | fLst([t]) = f(t)
           | fLst(t1::(rest as _::_)) = f(t1)^","^fLst(rest) 
    in
       f(t)
    end

fun makeTSTPTerm(t,fvars,boolean_term) =
     let fun f(Var(v)) = let val vname = ATV.name(v)
                             val cvn =  makeConservativeName(vname)
			 in
                            if Basic.isMemberEq(v,fvars,ATV.nameEq) then 
			       "a"^cvn else "X"^cvn
                         end
           | f(numTerm(an)) = A.athNumberToString(an)
           | f(ideTerm(x)) = "ide_$nti_$fier_$_"^(makeConservativeName(MetaId.name(x)))
           | f(App({root,args as [],...})) = if boolean_term then 
  	     		                        "("^"a"^(makeConservativeName(MS.name(root)))^"())"
                                             else "a"^( makeConservativeName(MS.name(root)))
           | f(App({root,args,...})) =  let val is_eq = MS.modSymEq(root,Names.mequal_logical_symbol)
                                            val fname = if is_eq then "equal" else 
						  makeConservativeName("f"^(MS.name(root)))
				  in
				     if is_eq then "("^(f (Basic.first args))^" = "^(f (Basic.second args))^")"
                                     else fname^"("^fLst(args)^")"
				  end
         and
             fLst([]) = ""
           | fLst([t]) = f(t)
           | fLst(t1::(rest as _::_)) = f(t1)^","^fLst(rest) 
    in
       f(t)
    end

fun makeTSTPTermFast(t,fvars,boolean_term,A,i) = 
     let fun write(str,i) = Basic.writeStringToCharArray(str,A,i)
         val (lp,rp,blank) = (Basic.lparen,Basic.rparen,Basic.blank)
         fun f(Var(v),i) = let val vname = ATV.name(v)
                               val cvn =  makeConservativeName(vname)
                                val cvn' = if Basic.isMemberEq(v,fvars,ATV.nameEq) then "a"^cvn else "X"^cvn
   			   in
			      write(cvn',i)
                           end
           | f(numTerm(an),i) = write(A.athNumberToString(an),i)
           | f(ideTerm(x),i) = write("ide_$nti_$fier_$_"^(makeConservativeName(MetaId.name(x))),i)
           | f(App({root,args,...}),i) =  let val is_eq = MS.modSymEq(root,Names.mequal_logical_symbol)
                                              val fname = if is_eq then "equal" else 
				  	  	    makeConservativeName("f"^(MS.name(root)))
				          in
				             if is_eq then 
                                                let val j1 = write(Basic.lparen,i)
                                                    val j2 = f(Basic.first(args),j1)
                                                    val j3 = write(" = ",j2)
                                                    val j4 = f(Basic.second(args),j3)
                                                in  write(rp,j4) end
                                             else let val j0 = write(fname,i)
                                                      val j1 = write(lp,j0)
                                                      val j2 = fLst(args,j1)
                                                  in write(rp,j2) 
                                                  end
                                          end
      and fLst([],i) = i
        | fLst(t::more,i) = (f(t,i);fLst(more,i));
    in
       f(t,i)
    end

fun leaves(App({args,...})) = Basic.flatten (List.map leaves args)
  | leaves(t) = [t]

val false_code = MS.code(Names.mfalse_logical_symbol)

val  evaluateString = ref (fn x:string => ())

fun isBuiltIn(f) = ModSymbol.compare(f,Names.mfalse_logical_symbol) = LESS

fun isBuiltInCVC(f) = (ModSymbol.compare(f,Names.mfalse_logical_symbol) = LESS andalso 
                      (not(MS.modSymEq(f,Names.mfalse_logical_symbol))) andalso (not(MS.modSymEq(f,Names.mtrue_logical_symbol))))

val smt_names = Unsafe.Array.create(Int.+(1,false_code),"")

val _ = let val update = Unsafe.Array.update
        in
           (update(smt_names,0,Names.addition_name);
	    update(smt_names,1,N.subtraction_name);
	    update(smt_names,2,N.multiplication_name);
	    update(smt_names,3,N.division_name);
	    update(smt_names,4,"mod");
	    update(smt_names,5,N.formal_less_name);
	    update(smt_names,6,N.formal_greater_name);
	    update(smt_names,7,N.formal_leq_name);
	    update(smt_names,8,N.formal_geq_name);
	    update(smt_names,9,N.equal_logical_name);
	    update(smt_names,10,N.ite_name);
	    update(smt_names,11,"and");
	    update(smt_names,12,"or");
	    update(smt_names,13,"not");
	    update(smt_names,14,"=>");
	    update(smt_names,15,"<=>");
	    update(smt_names,16,N.true_logical_name);
	    update(smt_names,17,N.false_logical_name))
        end
	
fun realToRat(x) = 
  let val x_str = A.athenaNumberToString(x,true)
      val [integral,decimal] = String.tokens (fn c => c = #".") x_str 
      val d = Basic.pow(10,String.size(decimal))
      val str = integral^decimal
      val n = (case IntInf.fromString(str) of
                 SOME(r) => r
               | _ => Basic.fail("\nError in converting a real number to SMT format.\n"))
      val n_str = if IntInf.<(n,IntInf.fromInt(0)) then "-"^(IntInf.toString(IntInf.abs n)) else IntInf.toString(n)
  in
      (n_str,Int.toString(d))
  end

val (symTermToFTermWithSub,symTermsToFTermsWithSub) = 
    let fun convert(terms) = 
          let  val vars = SymTerm.getVarsLst(terms)
	       val new_vars = map (fn (_) => FTerm.makeFreshVarCounter()) vars 
	       val empty_mapping = Symbol.empty_mapping
	       val mapping = Symbol.enterLst(empty_mapping,Basic.zip(vars,new_vars))
               fun doIt(t) = 
                   case SymTerm.isVar(t) of 
                      SOME(v) => (case Symbol.lookUp(mapping,v) of
			 	        SOME(v') => F.makeVar(v') 
                                      | _ => raise Basic.Never)
                    | NONE => (case SymTerm.isApp(t) of
                                  SOME(fsym,args) =>    
                                    let val arg_results = map doIt args
                                        in
                                          FTerm.makeApp(fsym,arg_results)
                                    end
                                | _ => raise Basic.Never)
               in
                  (map doIt terms,mapping)
          end
        in
          (fn (t) => convert([t]),fn (terms) => convert(terms))
    end

val fmap_module = Symbol.symbol("DMap")

val (fmap_sort_name,
     fmap_empty_map_name,
     fmap_update_name,
     fmap_apply_name) = ("DMap","empty-map","update","apply")
     
val (fmap_sort_symbol,
     fmap_empty_map_symbol,
     fmap_update_symbol,
     fmap_apply_symbol) = (Symbol.symbol fmap_sort_name,
     	                   Symbol.symbol fmap_empty_map_name,
		  	   Symbol.symbol  fmap_update_name,
			   Symbol.symbol fmap_apply_name)
	     
val (mfmap_sort_symbol,mfmap_empty_map_symbol,mfmap_update_symbol,mfmap_apply_symbol) = 
             (ModSymbol.makeModSymbol'([fmap_module],fmap_sort_symbol),
              ModSymbol.makeModSymbol'([fmap_module],fmap_empty_map_symbol),
              ModSymbol.makeModSymbol'([fmap_module],fmap_update_symbol),
              ModSymbol.makeModSymbol'([fmap_module],fmap_apply_symbol))

val (lp_define_blank,lp_define_type_blank,define,int_sort,cvc_int_sort,real_sort,cvc_real_sort,bool_sort,cvc_bool_sort,lp,rp,blank,double_rp_newline,colon,double_colon) = 
    ("\n(define ","\n(define-type ", "define","int","INT","real","REAL","bool","BOOLEAN","(",")"," ","))\n",":","::") 

val (var_prefix,fsym_prefix,poly_con_name_prefix) = (Names.smt_var_prefix,Names.smt_fsym_prefix,Names.smt_poly_con_name_prefix)

val (int_sort_code,real_sort_code,boolean_sort_code) = (MS.code(Names.mint_sort_symbol),MS.code(Names.mreal_sort_symbol),MS.code(Names.mboolean_sort_symbol))

fun sortNameSMT(sort) = 
       let val res = (case F.isApp(sort) of
                        SOME(msym,args) => 
                          let val scode = MS.code(msym) 
                              val main_name = if scode = int_sort_code then int_sort
                                              else if scode = boolean_sort_code then bool_sort
                                                   else if scode = real_sort_code then real_sort
                                                        else S.name(msym)
                          in
                             if null(args) then main_name 
                             else if MS.modSymEq(msym,mfmap_sort_symbol)
                                  then let val arg_string = Basic.printListStr(args,sortNameSMT," ")
                                  in
                                     "(-> "^arg_string^")"
                                  end
                                  else F.toOneStringDefault(sort) 
                          end
                      | _ => F.toStringDefault(sort))
       in
         res
       end

fun writeSMT(t,{domain_stream,
                dec_stream,
		main_stream,
		var_table,
		fsym_table,
		domain_table,
		sel_counter,
		poly_to_mono_sort_table}) = 
 let 
     fun debugPrint(s) = print(s)
     fun makePolyConName(name,range_type_str,arg_sorts) = 
            let val con_name = S.name name
	        val con_name = if (con_name = "::") then "CONS" else con_name
                val len_str = Int.toString(String.size(con_name))
		val arg_sort_string = Basic.printListStr(map F.toOneStringDefault arg_sorts,fn x => x,"_")
                val poly_con_name = poly_con_name_prefix^len_str^"_"^arg_sort_string^"_"^range_type_str^"_"^con_name
            in
              poly_con_name 
            end
     val domain_decs: (MS.mod_symbol * string) list ref = ref([])
     fun addDomain(pair as (sort_name:MS.mod_symbol,dec_string)) = domain_decs := pair::(!domain_decs)
     fun writeDec(str) = TextIO.output(dec_stream,str)
     fun writeMain(str) = TextIO.output(main_stream,str)
     fun fsymTableInsert(fsym) = S.insert(fsym_table,fsym,true)
     fun constructorString(c:Data.ath_struc_constructor as {name,arity,
                                                            selectors,argument_types,absyn_argument_types,range_type,sym_range_type,...},obtype_params,sort_args) = 
            (fsymTableInsert(name);
                   if null(obtype_params) then
                      if arity < 1 then fsym_prefix^(S.name name) 
                      else 
                      let fun getSelName(NONE:MS.mod_symbol option) = 
                                    let val str = fsym_prefix^(Names.smt_default_selector_fun_sym_prefix)^(Int.toString(Basic.incAndReturn(sel_counter)))
                                    in
                                       str
                                    end
                            | getSelName(SOME(ms)) = (fsymTableInsert(ms);fsym_prefix^MS.name(ms))
                          val arg_sorts_and_sels = Basic.zip(argument_types,selectors) 
                          fun makeSelString(arg_sort,sel) = 
                                     let val str = getSelName(sel)
                                         val _ = possiblyDeclareSort(arg_sort) 
                                     in
                                        str^double_colon^(sortNameSMT arg_sort)
                                     end
                          val sel_string = Basic.printListStr(arg_sorts_and_sels,makeSelString," ")
                      in 
                         lp^(fsym_prefix^(S.name name))^blank^sel_string^rp
                      end
                   else 
                     let val argument_types_as_SymTerms = map SymTerm.stripTags absyn_argument_types
                         val (types_as_FTerms,mapping) = 
                                symTermsToFTermsWithSub(sym_range_type::argument_types_as_SymTerms)
                         val range_type_as_fterm = hd types_as_FTerms
                         val arg_sorts_as_fterms  = tl types_as_FTerms
                         fun makeSub([],_,res) = res
                           | makeSub(obtype_param::more,sort_arg::rest,res) = 
                                 (case Symbol.lookUp(mapping,obtype_param) of
                                     SOME(fvar) => makeSub(more,rest,F.incSub(res,(fvar,sort_arg)))
                                   | _ => makeSub(more,rest,res))
                         val fsub = makeSub(obtype_params,sort_args,F.empty_sub)
                         val argument_types' = F.applySubLst(fsub,arg_sorts_as_fterms)
			 val range_type_as_fterm' = F.applySub(fsub,range_type_as_fterm)
                         val range_type_str = F.toOneStringDefault(range_type_as_fterm')
                         val argument_types = argument_types'
                         fun getSelName(NONE:MS.mod_symbol option,arg_sort) = fsym_prefix^(Names.smt_default_selector_fun_sym_prefix)^(Int.toString(Basic.incAndReturn(sel_counter)))
                           | getSelName(SOME(ms),arg_sort) = 
                                                    let val sel_str = makePolyConName(ms,F.toOneStringDefault(arg_sort),[range_type_as_fterm'])
						        val _ = HashTable.insert poly_to_mono_sort_table (sel_str,([range_type_as_fterm'],arg_sort))
                                                        val sel_ms' = msym(Symbol.symbol(sel_str))
                                                        val _ = fsymTableInsert(ms)
                                                    in
                                                        sel_str 
                                                    end
                         val arg_sorts_and_sels = Basic.zip(argument_types,selectors) 
                         fun makeSelString(arg_sort,sel) = 
                                    let val str = getSelName(sel,arg_sort)
                                        val _ = possiblyDeclareSort(arg_sort) 
                                    in
                                       str^double_colon^(sortNameSMT(arg_sort))
                                    end
                         val sel_string = Basic.printListStr(arg_sorts_and_sels,makeSelString," ")
                         val poly_con_name = makePolyConName(name,range_type_str,argument_types')
			 val _ = HashTable.insert poly_to_mono_sort_table (poly_con_name,(argument_types',range_type_as_fterm'))
                         val poly_con_msym = msym(Symbol.symbol(poly_con_name)) 
                         val _ = fsymTableInsert(poly_con_msym)
                     in 
                        if arity < 1 then poly_con_name else lp^poly_con_name^blank^sel_string^rp
                     end)
     and constructorsString([],_,_,res) = res
       | constructorsString(c::more,obtype_params,sort_args,res) = constructorsString(more,obtype_params,sort_args,
                                                                                      blank^(constructorString(c,obtype_params,sort_args))^res)
     and declareSort(whole_sort,sort_root,sort_args,large_sort_sym) = 
            (case Data.findStructure(sort_root) of
                SOME(struc as {constructors,arity,obtype_params,free,...}) => 
                 if (not free) then
                      let val poly_structure = (arity > 0)
                          val str = lp_define_type_blank^(S.name large_sort_sym)^rp
		          val _ = addDomain(large_sort_sym,str)
                      in
                        ()
                      end		      
                 else 
                  if MS.modSymEq(sort_root,mfmap_sort_symbol) then ()
                  else 
                  let val str = lp_define_type_blank^(MS.name large_sort_sym)^" (datatype "^
                                (constructorsString(constructors,obtype_params,sort_args,""))^double_rp_newline
                      val _ = addDomain(large_sort_sym,str)
                  in
                     ()
                  end
               | _ => if (!Options.ground_doms) then
                           let 
                               val whole_sort_name = F.toStringDefault(whole_sort)
                               val syms = (case (HashTable.find Data.domains_as_datatypes_table whole_sort_name) of
                                              SOME(fsym_list) => fsym_list
                                            | _ => let fun ev(s:string) = (!evaluateString)(s)
						       val str = "(make-fresh-constants \"" ^ whole_sort_name ^   "\" (get-flag \"dom-dt-default-size\"))"
                                                       val _ = ev(str)
                                                   in 
                                                      (case (HashTable.find Data.domains_as_datatypes_table whole_sort_name) of
                                                         SOME(fsym_list) => fsym_list)
                                                   end)
                               val sym_names = map (fn fsym => let val name = Data.fsymName(fsym)
                                                                   val _ = fsymTableInsert(name)
                                                               in name end) syms
                               val sym_names' = List.take(sym_names, (!Options.dt_for_dom_default_size))
			       val str = lp_define_type_blank^(MS.name large_sort_sym)^" (datatype "^
                                         (Basic.printListStr(sym_names',fn x => fsym_prefix^(MS.name x), " ")) ^ double_rp_newline
                           in
                             addDomain(large_sort_sym,str)
                           end
                     else
                      let val str = lp_define_type_blank^(S.name large_sort_sym)^rp
                      in
                        addDomain(large_sort_sym,str)
                      end)
    and possiblyDeclareSort(sort) = 
      let 
           val (sort_root,sort_args,large_sort_sym) = 
                        (case F.isApp(sort) of
                             SOME(root,[]) => (root,[],root)
                           | SOME(root,args) => (root,args,msym(Symbol.symbol(F.toOneStringDefault(sort))))
                           | _ => raise Basic.Fail("\npossiblyDeclareSort failed on this sort: "^(F.toStringDefault(sort))))
      in
        (case S.find(domain_table,large_sort_sym) of
            SOME(_) => ()
          | _ => (
                  S.insert(domain_table,large_sort_sym,true);
                  declareSort(sort,sort_root,sort_args,large_sort_sym)))
      end
     fun writeVarDec(name,sort) = (TextIO.output(dec_stream,lp_define_blank);
                                   TextIO.output(dec_stream,name);TextIO.output(dec_stream,"::");
                                   TextIO.output(dec_stream,sort);TextIO.output(dec_stream,rp))
     fun declareVar(v,vname) = 
             let val sort = ATV.getSort(v)
             in
               (writeVarDec(vname,sortNameSMT(sort));possiblyDeclareSort(sort))
             end
     fun inInstantiatedTable(str) = (case (HashTable.find poly_to_mono_sort_table str) of
                                       SOME(_) => true | _ => false)
     fun declareFSymAndItsSorts(fsym,fsym_name,arg_sorts,output_sort,is_poly) = 
                       let val _ = (List.app possiblyDeclareSort arg_sorts;
                                    possiblyDeclareSort(output_sort))
                           fun loop([]) = ()
                             | loop(sort::more) = (writeDec(sortNameSMT(sort));writeDec(blank);loop(more))
			   val isConstructorOrSelectorAndInTheTable = 
                                   (case S.find(fsym_table,fsym) of
                                       SOME(_) => Data.isStructureConstructorBool(fsym) orelse Data.isSelector(fsym) orelse inInstantiatedTable(fsym_name)
                                     | _ => false)
		           val _ = if is_poly andalso not(isConstructorOrSelectorAndInTheTable)
			           then HashTable.insert poly_to_mono_sort_table (fsym_name,(arg_sorts,output_sort))
                                   else ()
                       in
                          (* It's conceivable that fsym is a constructor that was just inserted into fsym_table 
                             during the above applications of possiblyDeclareSort; if so, don't redeclare: *)
		          if isConstructorOrSelectorAndInTheTable then ()
                          else 
                              let val _ = fsymTableInsert(fsym)
                              in
                                 if null(arg_sorts) then 
                                    (writeDec(lp_define_blank);writeDec(fsym_name);writeDec("::");
                                     writeDec(sortNameSMT(output_sort));writeDec(")\n"))
                                 else 
                                    (writeDec(lp_define_blank);writeDec(fsym_name);writeDec("::(-> ");
                                     loop(arg_sorts);writeDec(sortNameSMT(output_sort));writeDec("))\n"))
                              end
                       end
     fun loop(Var(v)) = 
             (case ATV.find(var_table,v) of 
                 NONE => let val vname = var_prefix^(ATV.name(v))
                             val _ = declareVar(v,vname)
                             val _ = ATV.insert(var_table,v,v)
                         in
                           TextIO.output(main_stream,vname)
                         end
               | _ => TextIO.output(main_stream,var_prefix^(ATV.name(v))))
       | loop(t as App({root,args,sort,...})) = 
           let val code = S.code(root)
               val is_built_in = code <= false_code
               val is_poly_symbol = Data.isPolySymbol(root)
               val name_str = if is_built_in then Unsafe.Array.sub(smt_names,code) 
                              else
                                   (case Data.isStructureConstructorOpt(root) of
                                       SOME(_) => if is_poly_symbol then 
                                                     makePolyConName(root,F.toOneStringDefault(sort),map getSort args)
                                                  else fsym_prefix^(S.name root)
                                     | _ => if is_poly_symbol then makePolyConName(root,F.toOneStringDefault(sort),map getSort args)
                                            else 
                                               fsym_prefix^(S.name root))
               val _ = if is_built_in then ()
                       else (case S.find(fsym_table,root) of
                                SOME(_) => let val arg_sorts = map getSort args
                                               val res = if is_poly_symbol then declareFSymAndItsSorts(root,name_str,arg_sorts,sort,is_poly_symbol) else ()
                                           in
                                              res  
                                           end
                              | _ => let val arg_sorts = map getSort args
                                         val res = declareFSymAndItsSorts(root,name_str,arg_sorts,sort,is_poly_symbol)
                                     in 
			                res
                                     end)
           in
               (case args of
                   [] => writeMain(name_str) 
                 | s::more => if null(more) andalso MS.modSymEq(root,Names.msubtraction_symbol) then 
		                 ( writeMain("(- 0 ");
                                  loop(s);
                                  writeMain(rp)
                                  )
                              else 
                                   if MS.modSymEq(mfmap_empty_map_symbol,root) then
                                      let val arg_sort = (case F.isApp(sort) of
                                                             SOME(_,[asort,_]) => asort)
                                      in
                                        (writeMain("(lambda (a::");
                                         writeMain(sortNameSMT(arg_sort));  
                                         writeMain(") ");loop(s);writeMain(")"))
                                      end
                                   else if MS.modSymEq(mfmap_update_symbol,root) then
                                            let val _ = ()
                                                val (key,value) = (case s of 
						                      App({args,...}) => (hd args, hd(tl(args))))
                                                val m = hd(more)
                                           in
                                             (writeMain("(update ");loop(m);writeMain(" (");
                                              loop(key);writeMain(") ");loop(value);writeMain(")"))
                                           end
                                        else if MS.modSymEq(mfmap_apply_symbol,root) then
                                                (writeMain(lp);loop(s);writeMain(blank);loop(hd more);writeMain(rp))
                                             else (writeGenericTerm(name_str,args)))
           end
       | loop(numTerm(n)) = (case n of 
                               A.int_num(_) => writeMain(A.athNumberToString(n))
                             | A.real_num(r,_) => let val (num,denum) = realToRat(n)
                                                  in
                                                    writeMain(num^"/"^denum)
                                                  end)
       | loop(ideTerm(x)) =   let val str' = (Names.metaIdPrefix)^(MetaId.name(x))
                                  val sym = msym (Symbol.symbol str') 
                              in 
                                 (case MS.find(fsym_table,sym) of
                                     SOME(_) => writeMain(str')
                                   | _ => let val _ = possiblyDeclareSort(D.ide_sort)
                                              val _ = fsymTableInsert(sym)
                                          in 
                                             (writeDec(lp_define_blank);
                                              writeDec(str');
                                              writeDec(double_colon^(Names.ide_sort_name)^")\n");
                                              writeMain(str'))
                                          end)
                              end
     and loopLst([]) = ()
       | loopLst([t]) = loop(t)
       | loopLst(t1::(rest as (_::_))) = (loop(t1);writeMain(blank);loopLst(rest))
     and writeGenericTerm(f_name,args) =  (writeMain(lp^f_name);writeMain(blank);loopLst(args);writeMain(rp))
 in
   (loop(t);!domain_decs)
 end

fun writeCVC(t,{domain_stream,dec_stream,main_stream,
                var_table,inverse_var_table,
                fsym_table:string ModSymbol.htable,
                inverse_fsym_table,
                domain_table, 
                inverse_domain_table,
                fsym_counter,dom_counter,sel_counter,var_counter}) = 
 let 
     fun debugPrint(s) = ()
     fun newFSymName(fsym_counter) = "f"^(Int.toString(Basic.incAndReturn(fsym_counter)))
     fun newDomName(dom_str) =  
                     (case (HashTable.find domain_table dom_str) of
                           SOME(str) => str
                         | _ => let val new_dom_name = "D"^(Int.toString(Basic.incAndReturn(dom_counter)))
                                    val _ = (HashTable.insert domain_table (dom_str,new_dom_name))
                                    val _ = (HashTable.insert inverse_domain_table (new_dom_name,dom_str))
                                in
                                   new_dom_name
                                end)
     val domain_decs: (string * string) list ref = ref([])
     fun addDomain(pair as (sort_name:string,dec_string)) = domain_decs := pair::(!domain_decs)
     fun constructorString(c:Data.ath_struc_constructor as {name,arity,
                                                            selectors,argument_types,absyn_argument_types,range_type,sym_range_type,...},obtype_params,sort_args) = 
                 (if null(obtype_params) then (* This is a monomorphic constructor, fairly easy to translate.
                                                 Selectors will be introduced by default if none were given in the Athena declaration. *)

                      if arity < 1 then makeMonoFSymName(name)
                      else 
                      let val _ = debugPrint("\nGetting the declaration of this non-nullary mono constructor: " ^ (MS.name(name)))
                          fun getSelName(NONE:MS.mod_symbol option) = fsym_prefix^(Names.smt_default_selector_fun_sym_prefix)^(Int.toString(Basic.incAndReturn(sel_counter)))
                            | getSelName(SOME(ms)) =  (case MS.find(fsym_table,ms) of
                                                          SOME(fname) => fname
                                                        | _ => let val sel_name = newFSymName(fsym_counter)
                                                                    val _ = (MS.insert(fsym_table,ms,sel_name);(HashTable.insert inverse_fsym_table (sel_name,ms)))
                                                               in
                                                                  sel_name
                                                               end)
                          val arg_sorts_and_sels = Basic.zip(argument_types,selectors) 
                          fun makeSelString(arg_sort,sel) = 
                                     let val str = getSelName(sel)
                                     in
                                        str^colon^blank^(translateSort arg_sort)
                                     end
                          val sel_string = Basic.printListStr(arg_sorts_and_sels,makeSelString,", ")
                          val cname = makeMonoFSymName(name)
                      in 
                         cname^lp^sel_string^rp
                      end
                   else  (* This is a polymorphic constructor, so we must look at sort_args to translate properly... *)
                     let 
                         val _ = debugPrint("\nGetting the declaration of this poly constructor: " ^ (MS.name(name)))
                         val argument_types_as_SymTerms = map SymTerm.stripTags absyn_argument_types
                         val (types_as_FTerms,mapping) = 
                                symTermsToFTermsWithSub(sym_range_type::argument_types_as_SymTerms)
                         val range_type_as_fterm = hd types_as_FTerms
                         val arg_sorts_as_fterms  = tl types_as_FTerms
                         fun makeSub([],_,res) = res
                           | makeSub(obtype_param::more,sort_arg::rest,res) = 
                                 (case Symbol.lookUp(mapping,obtype_param) of
                                     SOME(fvar) => makeSub(more,rest,F.incSub(res,(fvar,sort_arg)))
                                   | _ => makeSub(more,rest,res))
                         val fsub = makeSub(obtype_params,sort_args,F.empty_sub)
                         val argument_types' = F.applySubLst(fsub,arg_sorts_as_fterms)
			 val range_type = F.applySub(fsub,range_type_as_fterm)
                         val range_type_str = F.toOneStringDefaultCVC(range_type)
			 val cvc_range_type_str = newDomName(range_type_str)
                         val argument_types = argument_types'
                         val poly_con_name = makePolyFSymName(name,argument_types,range_type)
                         fun getSelName(NONE:MS.mod_symbol option,_) = 
                                 let val _ = debugPrint("\nNo selector for " ^ (MS.name name) ^ "\n")
                                 in
                                     fsym_prefix^(Names.smt_default_selector_fun_sym_prefix)^(Int.toString(Basic.incAndReturn(sel_counter)))
                                 end 
                           | getSelName(SOME(ms),arg_sort) = makePolyFSymName(ms,[arg_sort],arg_sort)
                         val arg_sorts_and_sels = Basic.zip(argument_types,selectors) 
                         fun makeSelString(arg_sort,sel) = 
                                    let val str = getSelName(sel,range_type)
                                    in
                                       str^colon^blank^(translateSort arg_sort)
                                    end
                         val sel_string = Basic.printListStr(arg_sorts_and_sels,makeSelString,", ")
                     in 
                        if arity < 1 then poly_con_name else poly_con_name^lp^sel_string^rp
                     end)
     and writeDec(str) = TextIO.output(dec_stream,str)
     and writeMain(str) = TextIO.output(main_stream,str)
     and constructorsString(constructors,obtype_params,sort_args) = Basic.printListStr(constructors,(fn c => constructorString(c,obtype_params,sort_args))," | ")
     and declareSort(sort_root,sort_args,whole_sort_name) = 
       let val _ = debugPrint("\nCalling declareSort on this sort_root: " ^ (MS.name(sort_root)))
       in
          (case (HashTable.find domain_table whole_sort_name) of
              SOME(str) => (debugPrint("\nTHis sort is already mapped to this string: " ^ str);str)
            | _ => let val sort_root_name = newDomName(MS.name(sort_root))                                                        
                       val res = if null(sort_args) then sort_root_name else sort_root_name ^ "_" ^ (Basic.printListStr(sort_args,translateSort,"_"))
                       val _ = HashTable.insert domain_table (whole_sort_name,res)
                       val _ = HashTable.insert inverse_domain_table (res,whole_sort_name)
                       val _ = debugPrint("\nDeclaring this sort: " ^ whole_sort_name)
                       val _ = (case Data.findStructure(sort_root) of
                          SOME(struc as {constructors,arity,obtype_params,...}) => 
                            if MS.modSymEq(sort_root,mfmap_sort_symbol) then ()
                            else 
                             let val str = "\nDATATYPE "^res^" = "^(constructorsString(constructors,obtype_params,sort_args))^" END;\n"
                                           
  	 	                 val _ = debugPrint("\nSort translation: " ^ str)
                             in
                               addDomain(whole_sort_name,str)
                             end
                       | _ => if (!Options.ground_doms)
                              then
                                   let val _ = debugPrint("\nwhole_sort_name: " ^ whole_sort_name)
                                       val syms = (case (HashTable.find Data.domains_as_datatypes_table whole_sort_name) of
                                                      SOME(fsym_list) => fsym_list
						    | _ => let fun ev(s:string) = (!evaluateString)(s)
 						               val str = "(make-fresh-constants \"" ^ whole_sort_name ^   "\" (get-flag \"dom-dt-default-size\"))"
                                                               val _ = ev(str)
							   in
							     (case (HashTable.find Data.domains_as_datatypes_table whole_sort_name) of
                                                                 SOME(fsym_list) => fsym_list)
							   end)
                                       val csyms = List.take(syms, (!Options.dt_for_dom_default_size))
                                       val str = "\nDATATYPE "^res^" = "^(Basic.printListStr(csyms,fn x => makeMonoFSymName(Data.fsymName(x)), " | ")) ^ " END;\n"
                                   in
                                      addDomain(whole_sort_name,str)
                                   end
                              else 
                              let val str = "\n"^res^colon^blank^"TYPE"^";\n"
                              in
                                 addDomain(whole_sort_name,str)
                              end)
                   in
                      res
                   end)
       end  
and translateSort(sort) = 
      let val _ = debugPrint("\nCalling translateSort on this sort: " ^ (F.toOneStringDefault(sort)))
          val whole_sort_name = F.toStringDefault(sort)
      in
          (case (HashTable.find domain_table whole_sort_name) of
              SOME(str) => str
            | _ => (case F.isApp(sort) of
                       SOME(sort_root,sort_args) => let val res = declareSort(sort_root,sort_args,whole_sort_name)
                                                    in 
                                                       res
                                                    end))
      end
and makeMonoFSymName(name) =
       (case MS.find(fsym_table,name) of
           SOME(fname) => fname
         | _ => let val new_name = newFSymName(fsym_counter)
                    val _ = (MS.insert(fsym_table,name,new_name);(HashTable.insert inverse_fsym_table (new_name,name)))
                in
                   new_name
                end)
and makePolyFSymName(msym,arg_sorts,range_sort) = 
      (case MS.find(fsym_table,msym) of
         SOME(fname) => fname^"_"^(if null(arg_sorts) then translateSort(range_sort) else Basic.printListStr(arg_sorts,translateSort,"_"))
      | _ => let val fname = newFSymName(fsym_counter)
                 val _ = MS.insert(fsym_table,msym,fname)
                 val _ = HashTable.insert inverse_fsym_table (fname,msym)
             in
                fname^"_"^(if null(arg_sorts) then  translateSort(range_sort) else Basic.printListStr(arg_sorts,translateSort,"_"))
             end)
and getFSymName(fsym,term_args,term_sort) = 
      (case MS.find(fsym_table,fsym) of
         SOME(fname) => 
           if not(Data.isPolySymbol(fsym)) then fname
           else let val arg_sorts = map getSort term_args
                    val arg_sort_string = Basic.printListStr(arg_sorts,translateSort,"_")
		    val translated_term_sort = translateSort(term_sort)
		    val _ = debugPrint("\nTranslated term sort: " ^ translated_term_sort ^ " for this fsym: " ^ (MS.name(fsym)) ^ " and this term sort: " ^ (F.toStringDefault term_sort))
    	            val name_str = fname^(if null(arg_sorts) then "_"^translated_term_sort else "_"^arg_sort_string)
		    val fsym' = msym(Symbol.symbol(name_str))
           in
                (case MS.find(fsym_table,fsym') of
                           SOME(str) => str  
                         | _ => let val translated_arg_sorts = Basic.printListStr(arg_sorts,translateSort,", ")
			            val translated_term_sort = translateSort(term_sort)
				    val _ = debugPrint("\nAbout to do a constructor check on this msym: " ^ (MS.name(fsym)))
                                    val _ = if Data.isStructureConstructorBool(fsym) orelse Data.isSelector(fsym) then  debugPrint("\nThis is a constructor: ")
                                            else (if null(arg_sorts) then 
                                                    (writeDec(name_str);writeDec(": ");writeDec(translated_term_sort);writeDec(";\n")) 
                                                  else 
                                                    (writeDec(name_str);writeDec(": (");writeDec(translated_arg_sorts);writeDec(") -> ");
                                                     writeDec(translated_term_sort);writeDec(";\n")))
                                    val _ = MS.insert(fsym_table,fsym',name_str)
                                    val _ = (HashTable.insert inverse_fsym_table (name_str,fsym'))                                    
                                in name_str end)
           end
       | _ => let val fname = newFSymName(fsym_counter)
                  val _ = MS.insert(fsym_table,fsym,fname)
                  val _ = (HashTable.insert inverse_fsym_table (fname,fsym))
                  val arg_sorts = map getSort term_args
                  val arg_sort_names = Basic.printListStr(arg_sorts,translateSort,", ")
                  val term_sort_translation = translateSort(term_sort)
		  val is_mono_sym = (not(Data.isPolySymbol(fsym))) handle _ => true 
                  val name_str = if is_mono_sym then fname else 
                                 (if null(arg_sorts) then fname^("_"^term_sort_translation) 
                                  else fname^"_"^(Basic.printListStr(arg_sorts,translateSort,"_")))
	          val _ = debugPrint("\nAbout to do a constructor check on this msym: " ^ (MS.name(fsym)))
                  val _ = if Data.isStructureConstructorBool(fsym) orelse Data.isSelector(fsym) then  debugPrint("\nThis is a constructor: ")
                          else 
                           if null(arg_sorts) then
                             (writeDec(name_str);writeDec(": ");writeDec(term_sort_translation);writeDec(";\n"))
                          else 
                              (writeDec(name_str);writeDec(": (");writeDec(arg_sort_names);writeDec(") -> ");
                               writeDec(term_sort_translation);writeDec(";\n"))
                  val _ = if is_mono_sym then ()
                          else let val fsym' = msym(Symbol.symbol(name_str))
                                   val _ = MS.insert(fsym_table,fsym',name_str)
                               in (HashTable.insert inverse_fsym_table (name_str,fsym')) end
              in name_str end)
and
    writeVarDec(name,sort) = (TextIO.output(dec_stream,"\n"^name^colon^blank);
                                   TextIO.output(dec_stream,sort);TextIO.output(dec_stream,";\n"))
and declareVar(v,vname) = 
             let val sort = ATV.getSort(v)
             in
               writeVarDec(vname,translateSort(sort))
             end  
     fun loop(Var(v)) = 
             (case ATV.find(var_table,v) of 
                 NONE => let val vname = var_prefix^(Int.toString (Basic.incAndReturn(var_counter)))
                             val _ = declareVar(v,vname)
                             val _ = ATV.insert(var_table,v,vname)
                             val _ = (HashTable.insert inverse_var_table (vname,v))
                         in
                           TextIO.output(main_stream,vname)
                         end
               | SOME(vname) => TextIO.output(main_stream,vname))
       | loop(t as App({root,args,sort,...})) = 
           let val code = S.code(root)
               val is_built_in = isBuiltInCVC(root)
               val is_poly_symbol = Data.isPolySymbol(root)
               val name_str = if is_built_in then Unsafe.Array.sub(smt_names,code) else getFSymName(root,args,sort)
           in
               if (code = N.ite_symbol_code) then
                    (writeMain("(IF "); loop(Basic.first(args)); writeMain(" THEN "); loop(Basic.second(args)); 
                     writeMain(" ELSE ");loop(Basic.third(args));writeMain(" ENDIF)"))
               else
               (case args of
                   [] => writeMain(name_str) 
                 | s::more => if null(more) andalso MS.modSymEq(root,Names.msubtraction_symbol) then 
		                 (writeMain("(- ");loop(s);writeMain(rp))
                              else 
                                   if MS.modSymEq(mfmap_empty_map_symbol,root) then
                                      let val arg_sort = (case F.isApp(sort) of
                                                             SOME(_,[asort,_]) => asort)
                                      in
                                        (writeMain("(lambda (a::");
                                         writeMain(translateSort(arg_sort));  
                                         writeMain(") ");loop(s);writeMain(")"))
                                      end
                                   else if MS.modSymEq(mfmap_update_symbol,root) then
                                           let val _ = ()
                                           in
                                             (writeMain("(update ");loop(s);writeMain(" (");
                                              loop(hd more);writeMain(") ");loop(hd(tl(more)));writeMain(")"))
                                           end
                                        else if MS.modSymEq(mfmap_apply_symbol,root) then
                                                (writeMain(lp);loop(s);writeMain(blank);loop(hd more);writeMain(rp))
                                             else writeGenericTerm(name_str,args)) 
           end
       | loop(numTerm(n)) = (case n of 
                               A.int_num(_) => writeMain(A.athNumberToString(n))
                             | A.real_num(r,_) => let val (num,denum) = realToRat(n)
                                                  in
                                                    writeMain(num^"/"^denum)
                                                  end)
       | loop(t as (ideTerm(x))) = 
                              let val str' = (Names.metaIdPrefix)^(MetaId.name(x))
                                  val sym = msym (Symbol.symbol str')
				  val _ = debugPrint("\nAbout to get a name for this meta-id sym: " ^ (MS.name sym))
                                  val sym_name = getFSymName(sym,[],getSort(t))
				  val _ = debugPrint("\nResult: " ^ sym_name)
                              in 
                                 writeMain(sym_name)
                               end
     and loopLst([]) = ()
       | loopLst([t]) = loop(t)
       | loopLst(t1::(rest as (_::_))) = (loop(t1);writeMain(Basic.comma);loopLst(rest))
     and isPrimBinary(f_name) = Basic.isMember(f_name,["=","+","-","*","/","<",">","<=",">="])
     and writeGenericTerm(f_name,args) =
          if isPrimBinary(f_name) then 
            (if (f_name = "+" andalso length(args) = 1) then (writeMain(lp);loopLst(args);writeMain(rp))
             else (writeMain("(");loop(hd args);writeMain(" " ^ f_name ^ " ");loop(hd(tl(args)));writeMain(")")))
          else (writeMain(f_name^lp);loopLst(args);writeMain(rp))
 in
    (loop(t);!domain_decs)
 end;

val (makePolyTPTPTerm,makePolyTPTPTermLst) = 
 let fun makeBoth(fvars,printer) = 
           let val st = "st" 
               val (lp,rp,comma) = ("(",")",",")
               fun f(Var(v),sort_vars) = let val vname = ATV.name(v)
                                             val cvn =  makeConservativeName(vname)
                                             val vname' = if Basic.isMemberEq(v,fvars,ATV.nameEq) then "a"^cvn else "X"^cvn
                                             val (sort_str,{vars=vs,...}) = F.toPolyString(ATV.getSort(v),printer)
                                             val v_str = st^lp^sort_str^comma^vname'^rp
  			                 in
                                            (v_str,vs@sort_vars)
                                         end
                 | f(numTerm(an as A.int_num(_)),sort_vars) = 
                              let val cname = A.athNumberToString(an)
                                  val sort_str = "c"^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.int_sort_symbol))))
                                  val term_str = st^lp^sort_str^comma^cname^rp 
			      in 
                                 (term_str,sort_vars)
                              end
                 | f(numTerm(an as A.real_num(r,_)),sort_vars) = 
                     let val cname = 
                                   let val (floor,ceil) = (Int.toString(Real.floor(Real.realFloor(r))),Int.toString(Real.ceil(Real.realCeil(r))))
                                   in "r"^floor^ceil  
                                   end
                         val sort_str = "c"^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.real_sort_symbol))))
                         val term_str = st^lp^sort_str^comma^cname^rp 
		     in 
                        (term_str,sort_vars)
                     end
                 | f(ideTerm(x),sort_vars) = 
                                           let val cname = "ident"^(MetaId.name(x))
                                               val sort_str = "c"^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.ide_sort_symbol))))
                                               val term_str = st^lp^sort_str^comma^cname^rp 
					   in
                               	             (term_str,sort_vars)
					   end
                 | f(App({root,sort,args as [],...}),sort_vars) = 
			  let val cname = "a"^(makeConservativeName(MS.name(root)))
                              val (sort_str,{vars=vs',...}) = F.toPolyString(sort,printer)
                              val c_str = st^lp^sort_str^comma^cname^rp
                              val sort_vars' = vs'@sort_vars
			      in
                               	(c_str,sort_vars')
	       	              end
                 | f(App({root,sort,args,...}),sort_vars) =  
		    let val is_eq = MS.modSymEq(root,Names.mequal_logical_symbol)
			val fname = if is_eq then "=" else "f"^(Basic.fsymRenamer(MS.name(root)))
                        val (sort_str,{vars=vs,...}) = F.toPolyString(sort,printer)				    
			val (term_strings,sort_vars') = fLst(args,[],vs@sort_vars)
                        val f_str = fname^lp^(Basic.printListStr(term_strings,fn x => x,comma))^rp 
                        val term_str = st^lp^sort_str^comma^f_str^rp
		     in
			(term_str,sort_vars')
		     end
              and fLst([],strings,sort_vars) = (rev strings,sort_vars)
                | fLst(t::rest,strings,sort_vars) = 
                    let val (str,sort_vars') = f(t,sort_vars)
                    in
		      fLst(rest,str::strings,sort_vars')
      	            end
           in 
             (f,fLst)
           end 
   in 
      (fn (t,fvars,printer,sort_vars) => let val (f,fLst) = makeBoth(fvars,printer) in f(t,sort_vars) end, 
       fn (terms,fvars,printer,sort_vars) => let val (f,fLst) = makeBoth(fvars,printer) in fLst(terms,[],sort_vars) end)
   end

fun makeSpassTerm(t,fvars,variableRenamer,fsymRenamer,ht) =
     let  fun insertFS(key,str) = HashTable.insert ht (key,str)
          fun f(Var(v)) = 
			 let val vname = variableRenamer(ATV.name(v))
                         in 
                            if Basic.isMemberEq(v,fvars,ATV.nameEq) then 
				    let val cname = "c"^vname  
                                        val _ = insertFS(cname,"("^cname^",0)")
				    in
			       	       cname
			    	    end
	   		    else "X"^vname
                         end
           | f(numTerm(an)) = let val cname = A.athNumberToString(an)
                                        val str = "("^cname^",0)"
                                        val _ = insertFS(cname,str)
			      in 
                                  cname
                              end
           | f(ideTerm(x)) =   
                               let val cname = "ide_nti_fier_"^(MetaId.name(x))
                                   val str = "("^cname^",0)" 
                                   val _ = insertFS(cname,str)
 		                in
                               	   cname
			        end
           | f(App({root=f,args as [],...})) = 
			  let val cname = "c"^(fsymRenamer(MS.name(f)))
                              val str = "("^cname^",0)"
                              val _ = insertFS(cname,str)
			      in
                               	cname
	       	              end
           | f(App({root=f,args=terms,...})) = 
		    let val is_eq = MS.modSymEq(f,Names.mequal_logical_symbol)
			val fname = if is_eq then "equal"
                                    else "f"^(fsymRenamer(MS.name(f)))
				    
			val arity = Int.toString(length(terms))
			val (term_strings,n) = fLst(terms,[],0)
			val str = if is_eq then () else insertFS(fname,"("^fname^","^n^")")
		     in
			fname^"("^Basic.printListStrCommas(term_strings,fn x => x)^")"
		     end
         and
             fLst([],strings,i) = (rev(strings),Int.toString(i))
           | fLst(t::rest,strings,i) = let val str = f(t)
				       in
				         fLst(rest,str::strings,i+1)
				       end
	val res = f(t)
    in
       res
    end

val atp_sort_prefix = F.atp_sort_prefix

fun findOutDynamicallyIfASortLstHasOrderSortedSymbolsInIt(sorts) = 
        let fun f([],res) = res
              | f(sort::more,res) = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                        SOME(sorts') => f(more,sorts'@res)
                                      | _ => f(more,res))
        in 
          (case f(sorts,[]) of
             [] => NONE
           | res => SOME(res))
        end  

fun toPolyString1Lst(sorts,printer) = 
           let fun f([],res) = res 
                 | f(s::more,res) = let val (_,{fsyms=fs,vars=vs}) = F.toPolyString(s,printer)
                                    in 
                                       f(more,fs@res)
                                    end
           in 
              f(sorts,[])
           end

val (makePolyTerm,makePolyTermLst) = 
   let fun makeBoth(fvars,variableRenamer,fsymRenamer,printer,format) = 
     let val st = "st" 
         val (lp,rp,comma) = ("(",")",",")
         fun f(Var(v),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
			 let val vname = variableRenamer(ATV.name(v))
                             val (vname',flag) = if Basic.isMemberEq(v,fvars,ATV.nameEq) 
                                                 then ("c"^vname,true) else ("X"^vname,false)
                             val sort = ATV.getSort(v)
                             val (sort_str,{vars=vs',fsyms=fs'}) = F.toPolyString(sort,printer)    
                             val v_str = st^lp^sort_str^comma^vname'^rp
                             val vs'' = vs'@vs 
                             val fs'' = if flag then ((lp^vname'^",0"^rp)::fs')@fs else fs'@fs 
                             val os' = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                           SOME(sorts) => sorts@os
                                         | _ => os)
                 
                         in
                             (v_str,{vars=vs'',fsyms=fs'',fsymbols=fsymbols,osorts=os'})
                         end
           | f(numTerm(an as A.int_num(_)),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                              let val cname = "c"^A.athNumberToString(an)
                                  val sort_str = (atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.int_sort_symbol))))
                                  val term_str = st^lp^sort_str^comma^cname^rp 
                                  val os' = Data.mint_sort_symbol::os
                                  val res = (term_str,{vars=vs,fsyms=("("^cname^",0)")::("("^sort_str^",0)")::fs,
                                             fsymbols=(msym(Symbol.symbol cname))::fsymbols,osorts=os'})
			      in 
                                 res                                
                              end
           | f(numTerm(an as A.real_num(r,_)),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                 let val cname = let val (floor,ceil) = (Int.toString(Real.floor(Real.realFloor(r))),Int.toString(Real.ceil(Real.realCeil(r))))
                                   in "c"^floor^"_"^ceil  end
                    val sort_str = (atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.real_sort_symbol))))
                    val term_str = st^lp^sort_str^comma^cname^rp
                    val os' = Data.mreal_sort_symbol::os 
                 in 
                   (term_str,{vars=vs,fsyms=("("^cname^",0)")::("("^sort_str^",0)")::fs,fsymbols=(msym (Symbol.symbol cname))::fsymbols,osorts=os'})
                 end
           | f(ideTerm(x),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                                           let val cname = "ide_nti_fier_"^(MetaId.name(x))
                                               val sort_str = (atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.ide_sort_symbol))))
                                               val term_str = st^lp^sort_str^comma^cname^rp 
					   in
                               	             (term_str,{vars=vs,fsyms=("("^cname^",0)")::fs,fsymbols=msym (Symbol.symbol cname)::fsymbols,osorts=os})
					   end
           | f(App({root=f,sort,args as [],...}),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os}) = 
			  let val cname = "c"^(fsymRenamer(MS.name(f)))
                              val (sort_str,{vars=vs',fsyms=fs'}) = F.toPolyString(sort,printer)
                              val c_str = st^lp^sort_str^comma^cname^rp
                              val fs'' = ((lp^cname^",0"^rp)::fs')@fs
                              val vs'' = vs'@vs 
                              val os' = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                            SOME(sorts) => sorts@os
                                           | _ => os)
			      in
                               	(c_str,{vars=vs'',fsyms=fs'',fsymbols=f::fsymbols,osorts=os'})
	       	              end
           | f(App({root=f,sort,args=terms,...}),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
		    let val is_eq = MS.modSymEq(f,Names.mequal_logical_symbol)
                        val equality_symbol = if format = "spass" then "equal" else "="
			val fname = if is_eq then equality_symbol else "f"^(fsymRenamer(MS.name(f)))
                        val (sort_str,{vars=vs',fsyms=fs'}) = F.toPolyString(sort,printer)				    
                        val os' = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                      SOME(sorts) => sorts@os
                                    | _ => os)
			val arity = Int.toString(length(terms))
                        val (arg_sorts,_,_,has_pred_based_sorts) = Data.getSignature(f)
                        val fs_new = toPolyString1Lst(arg_sorts,printer) 
                        val os'' = (case findOutDynamicallyIfASortLstHasOrderSortedSymbolsInIt(arg_sorts) of
                                      SOME(sorts) => sorts@os'
                                    | _ => os')
			val (term_strings,{vars=vs'',fsyms=fs'',fsymbols=fsymbols',osorts=os'''},n) = 
                                  fLst(terms,[],{vars=vs'@vs,fsyms=fs'@fs,fsymbols=fsymbols,osorts=os''},0)
                        val f_str = fname^lp^(Basic.printListStr(term_strings,fn x => x,comma))^rp 
                        val term_str = st^lp^sort_str^comma^f_str^rp
			val fs''' = if is_eq then fs'' 
				      else ("("^fname^","^n^")")::fs''
		     in
			(term_str,{vars=vs'',fsyms=fs_new@fs''',fsymbols=f::fsymbols',osorts=os'''})
		     end
         and
             fLst([],strings,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os},i) = 
                        (rev(strings),{vars=vs,fsyms=fs,osorts=os,fsymbols=fsymbols},Int.toString(i))
           | fLst(t::rest,strings,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os},i) =  
                    let val (str,{vars=vs',fsyms=fs',fsymbols=fsymbols',osorts=os'}) = f(t,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os})
                    in
		      fLst(rest,str::strings,{fsyms=fs',vars=vs',fsymbols=fsymbols',osorts=os'},i+1)
      	            end
     in
        (f,fLst)
     end
    in
       (fn (t,fvars,variableRenamer,fsymRenamer,printer,format) =>
              let val (f,_) = makeBoth(fvars,variableRenamer,fsymRenamer,printer,format) 
                  val (str,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os}) = f(t,{vars=[],fsyms=[],fsymbols=[],osorts=[]})
                  val st_str = "(st,2)"
              in  
                 (str,{vars=vs,fsyms=st_str::fs,fsymbols=fsymbols,osorts=os}) 
              end,
       fn (terms:term list,fvars,variableRenamer,fsymRenamer,printer,format) => 
              let val (_,f) = makeBoth(fvars,variableRenamer,fsymRenamer,printer,format) 
                  val (strings,res as {vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os},_) = f(terms,[],{vars=[],fsyms=[],fsymbols=[],osorts=[]},0)
                  val st_str = "(st,2)"
              in  
                  (strings,{vars=vs,fsyms=st_str::fs,fsymbols=fsymbols,osorts=os}) 
              end)
    end

fun hash(t,seed,n,max,map) = 
         let fun f(App({root=r,args,...}),seed,n) = 
			let val res as (hash_code,char_count) = 
					Basic.hashAccum(MS.name(r),seed,n)
			in
			   if char_count > max then res 
                           else fLst(args,hash_code,char_count) 
			end
               | f(Var(v),seed,n) = 
		  let val top_sort_name = F.rootString(ATV.getSort(v))
                      val str = (case ATV.lookUp(map,v) of
			            SOME(str) => str
			           | _ => ATV.name(v))
                      val (w1,n') = Basic.hashAccum(str,seed,n)
	  	  in
		     Basic.hashAccum(top_sort_name,w1,n')
   	          end
               | f(numTerm(num),seed,n) = Basic.hashAccum(A.athNumberToString(num),seed,n)
               | f(ideTerm(x),seed,n) = Basic.hashAccum(MetaId.name(x),seed,n)
             and
                 fLst(t::more,seed,count) = let val (code,count') = f(t,seed,count)
                                            in
                                               if count' > max then (code,count')
                                               else
                                                 fLst(more,code,count')
                                            end
               | fLst([],seed,count) = (seed,count)

         in    
            if n > max then (seed,n) else f(t,seed,n)
         end

fun hashTerm(t) = #1(hash(t,0w0,0,55,ATV.empty_mapping))

val hashTerm = fastHash

fun subterms(t,ht) = 
  let fun f(t) = (case (HashTable.find ht t) of
                     NONE => ((HashTable.insert ht (t,true));g(t))
                   | _ => g(t))
     and g(App({args,...})) = List.app f args 
       | g(_) = ()
  in
     f(t)
  end

fun termEq(s,t) = if ATV.varListsMatch(getVars(s),getVars(t)) then f(s,t) else false
  and termEqLst(terms1,terms2) = fLst(terms1,terms2)
  and     f(Var(v),Var(v')) = ATV.nameEq(v,v')
        | f(App({root=root1,args=[],sort=sort1,bits=bits1,...}),
	    App({root=root2,args=[],sort=sort2,bits=bits2,...})) = 
            MS.modSymEq(root1,root2) andalso bits1=bits2 andalso F.sortEq(sort1,sort2) 
        
        | f(App({root=f,args=terms1,...}),App({root=g,args=terms2,...})) = 
		MS.modSymEq(f,g) andalso fLst(terms1,terms2)
        | f(numTerm(n1),numTerm(n2)) = A.athNumEquality(n1,n2) 
        | f(ideTerm(x1),ideTerm(x2)) = MetaId.eq(x1,x2)
        | f (_) = false
    and fLst([],[]) = true
      | fLst(t1::rest1,t2::rest2) = termEq(t1,t2) andalso termEqLst(rest1,rest2)
      | fLst(_) = false

fun termEq(s,t) =
	let fun f(Var(x),Var(y),sorts1,sorts2) = 
			if ATV.nameEq(x,y) then
			   ((ATV.getSort x)::sorts1,(ATV.getSort y)::sorts2)
			else (failLst [])
	      | f(t1 as App({root=f,args=[],sort=sort1,bits=bits1,...}),
		  t2 as App({root=g,args=[],sort=sort2,bits=bits2,...}),sorts1,sorts2) = 
			if fsymEq(f,g) andalso bits1=bits2 then 
			   (case F.coerceSubsorts(sort1,sort2) of
				{coerced_sorts=SOME(sort1',sort2'),reversed} =>
				  let val res = if reversed then
						      (sort2'::sorts1,sort1'::sorts2)
	 				        else
						      (sort1'::sorts1,sort2'::sorts2)
				  in
				    res
				  end
			      | _ => (failLst []))
			else (failLst [])
	     | f(App({root=f,args=args1,sort=sort1,bits=bits1,...}),
		 App({root=g,args=args2,sort=sort2,bits=bits2,...}),sorts1,sorts2) = 
			if fsymEq(f,g) andalso (bits1=bits2) then
			   fLst(args1,args2,(sorts1,sorts2))
			else (failLst [])
             | f(numTerm(n1),numTerm(n2),sorts1,sorts2) = 
			if A.athNumEquality(n1,n2) then
			   (sorts1,sorts2)
			else (failLst [])
             | f(ideTerm(x1),ideTerm(x2),sorts1,sorts2) = 
			if MetaId.eq(x1,x2) then
			   (sorts1,sorts2)
			else (failLst [])
	     | f(_) = (failLst [])
 	   and fLst(t1::rest1,t2::rest2,(sorts1,sorts2)) = fLst(rest1,rest2,f(t1,t2,sorts1,sorts2))
             | fLst([],[],res) = res
	     | fLst(_) = (failLst [])
	   val res = SOME(f(s,t,[],[])) handle _ => NONE
        in
	  (case res of
	      SOME(sorts1,sorts2) => 
		(case (F.matchLst(sorts1,sorts2),F.matchLst(sorts2,sorts1)) of
		    (SOME(_),SOME(_)) => true
                  | _ => false)
            | _ => false)
        end

fun subtermsDefault(t) = 
    let val ht : (term,bool) HashTable.hash_table = HashTable.mkTable(hashTerm,termEq) (100,Basic.Fail("Hash Table Creation"))  
        val _ = subterms(t,ht)
    in 
      List.map #1 (HashTable.listItemsi ht)
    end

fun termEqWithPolyConstants(s,t) =
	let fun f(Var(x),Var(y),sorts1,sorts2) = 
			if ATV.nameEq(x,y) then
			   ((ATV.getSort x)::sorts1,(ATV.getSort y)::sorts2)
			else (failLst [])
	      | f(t1 as App({root=f,args=[],sort=sort1,bits=bits1,...}),
		  t2 as App({root=g,args=[],sort=sort2,bits=bits2,...}),sorts1,sorts2) = 
			if fsymEq(f,g) andalso bits1=bits2 then 
                          (if isPoly(t1) orelse isPoly(t2) then
                             (if F.termEq(sort1,sort2) then (sorts1,sorts2)
                                 else (failLst []))
                          else 
			   (case F.coerceSubsorts(sort1,sort2) of
				{coerced_sorts=SOME(sort1',sort2'),reversed} =>
				  let val res = if reversed then
						      (sort2'::sorts1,sort1'::sorts2)
	 				        else
						      (sort1'::sorts1,sort2'::sorts2)
				  in
				    res
				  end
			      | _ => (failLst [])))
			else (failLst [])
	     | f(App({root=f,args=args1,sort=sort1,bits=bits1,...}),
		 App({root=g,args=args2,sort=sort2,bits=bits2,...}),sorts1,sorts2) = 
			if fsymEq(f,g) andalso (bits1=bits2) then
			   fLst(args1,args2,(sorts1,sorts2))
			else (failLst [])
             | f(numTerm(n1),numTerm(n2),sorts1,sorts2) = 
			if A.athNumEquality(n1,n2) then
			   (sorts1,sorts2)
			else (failLst [])
             | f(ideTerm(s1),ideTerm(s2),sorts1,sorts2) = 
			if MetaId.eq(s1,s2) then
			   (sorts1,sorts2)
			else (failLst [])
	     | f(_) = (failLst [])
 	   and fLst([],[],res) = res
	     | fLst(t1::rest1,t2::rest2,(sorts1,sorts2)) = fLst(rest1,rest2,f(t1,t2,sorts1,sorts2))
	     | fLst(_) = (failLst [])
	   val res = SOME(f(s,t,[],[])) handle _ => NONE
        in
	  (case res of
	      SOME(sorts1,sorts2) => 
		(case (F.matchLst(sorts1,sorts2),F.matchLst(sorts2,sorts1)) of
		    (SOME(_),SOME(_)) => true
                  | _ => false)
            | _ => false)
        end

infix ==

fun t1 == t2 = termEq(t1,t2)

fun makeNumTerm(n) = numTerm(n)

fun makeNumConstant(n) = numTerm(n)
  
fun makeIdeConstant(s) = ideTerm(MetaId.makeMetaId(s))

val (isSortInstance,isSortInstanceAux) =
	let fun f(Var(x),Var(y),(sorts1,sorts2)) = 
			if ATV.nameEq(x,y) then
			   ((ATV.getSort x)::sorts1,(ATV.getSort y)::sorts2)
			else (failLst [])
	      | f(t1 as App({root=f,args=[],sort=sort1,bits=bits1,...}),
		  t2 as App({root=g,args=[],sort=sort2,bits=bits2,...}),(sorts1,sorts2)) = 
			if fsymEq(f,g) then (sort1::sorts1,sort2::sorts2)
                        else (failLst [])
	      | f(t1 as App({root=f,args=args1 as _::_,...}),
		  t2 as App({root=g,args=args2 as _::_,...}),sorts) = 
			if fsymEq(f,g) then fLst(args1,args2,sorts)
			else (failLst [])
             | f(numTerm(n1),numTerm(n2),sorts) = 
			if A.athNumEquality(n1,n2) then sorts
			else (failLst [])
             | f(ideTerm(s1),ideTerm(s2),sorts) = 
			if MetaId.eq(s1,s2) then sorts
			else (failLst [])
	     | f(_) = (failLst [])
 	      	   and fLst([],[],res) = res
	     | fLst(t1::rest1,t2::rest2,sorts) = fLst(rest1,rest2,f(t1,t2,sorts))
	     | fLst(_) = (failLst [])
        in
           (fn (s,t) => 
              let val res = SOME(f(s,t,([],[]))) handle _ => NONE
              in
                 (case res of
                      SOME(sorts1,sorts2) => F.matchLst(sorts1,sorts2)
                   | _ => NONE)
              end,f)
        end

fun orTermWords(App({bits,...})::more,w) = orTermWords(more,orWords(bits,w))
  | orTermWords(Var(v)::more,w) =
      let val sort = ATV.getSort(v)
      in 
        if F.isGround(sort) then 
           (if F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(sort)
            then orTermWords(more,orWords(w,orWords(varsWord,hasPredBasedSortsWord)))
	    else orTermWords(more,orWords(w,varsWord)))
        else
           (if F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(sort)
            then makeWord({involves_pred_based_sorts=true,non_canonical=true,poly=true,hasVars=true})
            else makeWord({involves_pred_based_sorts=false,non_canonical=true,poly=true,hasVars=true}))
      end
| orTermWords(_::more,w') = orTermWords(more,w')
| orTermWords([],w) = w

val (renameSortVarsAux,renameSortVarsAuxLst) = 
      let fun f(t as Var(v),sub) = 
      	      	    let val (v',sub') = ATV.renameSortVars(v,sub)
                    in
		       (Var(v'),sub')
                    end
            | f(App({root,args,sort,bits,vars,hash_code,poly_constants,...}),sub) = 
 	        let val (args',sub') = fLst(args,sub,[])
		    val sort' = F.applySub(sub',sort)
		    val (sort',sub') = if null(args) andalso not(F.isGround(sort)) then 
                                       F.renameAux(sort',sub') else (sort',sub')
                    val vars' = map (fn v => ATV.applySortSub(sub',v)) vars	        
		    val poly_constants' = List.filter (fn (_,sort) => not(F.isGround(sort)))
                                                      (List.map (fn (c,sort) => (c,F.applySub(sub',sort))) 
						      		poly_constants)
                in
                  (App({root=root,
		        hash_code=hash_code,
		        args=args',
		        sort=sort',
		        bits=bits,
		        vars=vars',
		        poly_constants=poly_constants'}),
                   sub')
                 end
         and g(t,sub) = if not(isPoly(t)) then (t,sub) else f(t,sub)		 
         and fLst([],sub,results) = (rev(results),sub)
           | fLst(t::more,sub,results) = 
                let val (t',sub') = g(t,sub)
                in
		   fLst(more,sub',t'::results)
                end                         
      in
         (fn (t,sub) => f(t,sub),fn (terms,sub) => fLst(terms,sub,[]))
      end

fun renameSortVars(t) = 
            let val (t',_) = renameSortVarsAux(t,F.empty_sub)
            in
	      t'
            end

fun renameSortVarsLst(terms) = 
            let val (terms',_) = renameSortVarsAuxLst(terms,F.empty_sub)
            in
	      terms'
            end

fun sortVars(t) = 
      let fun loop(tapp as App({root,args,sort,bits,vars,hash_code,poly_constants,...}),res) = 
           let val vars = (F.getVars sort)
           in
               loopLst(args,vars@res)
           end
            | loop(Var(v),res) = (F.getVars (ATV.getSort v))@res
            | loop(_,res) = res
          and loopLst([],res) = res
            | loopLst(t::more,res) = loopLst(more,loop(t,res))
         val res = loop(t,[])
      in
         Basic.removeDuplicatesEq(res,F.varEq)
      end
                 
fun getSortSub(App({root=root1,args=args1,sort=sort1,...}),App({root=root2,args=args2,sort=sort2,...})) =  
     if (MS.modSymEq(root1,root2)) then
         let val arg_sorts_1 = map getSort args1
	     val arg_sorts_2 = map getSort args2
	     val sort_list_1 = arg_sorts_1 @ [sort1]
	     val sort_list_2 = arg_sorts_2 @ [sort2]
         in
	    (case FTerm.unifyLst(sort_list_1,sort_list_2)  of
                SOME(sub) => SOME(sub)
              | _ => let val _ = print("\nUnification failed!\n") in NONE end)
         end
     else 
          NONE

fun getSortSubForFirstTerm(terms,t2 as App({root=root2,args=args2,sort=sort2,...})) =  
         (case (List.filter (fn App({root=root3,...}) => MS.modSymEq(root3,root2) | _ => false) terms) of
             [] => NONE
           | t1::_ => getSortSub(t1,t2))

fun applySortSub(sub,t) = 
	if F.isEmptySub(sub) then t 
	else 
	      let fun f(App({root,args,sort,bits,vars,hash_code,poly_constants,...})) = 
			 let val sort' = F.applySub(sub,sort)
			     val vars' = map (fn v => ATV.applySortSub(sub,v)) vars
			     val poly_constants' = List.filter (fn (_,sort) => not(F.isGround(sort)))
                                                               (List.map (fn (c,sort) => (c,F.applySub(sub,sort))) poly_constants)
			     val args' = map g args
	 		     val root_word = makeWord({poly=F.hasVars(sort'),non_canonical=isNonCanonicalWord(bits),
                                                       involves_pred_based_sorts=involvesPredBasedSortsWord(bits),
                                                       hasVars=not(null(vars'))})
			     val bits' = orTermWords(args',root_word)
			 in
		            App({root=root,hash_code=hash_code,
			         args=args',sort=sort',bits=bits',vars=vars',poly_constants=poly_constants'})
			 end
                    | f(Var(v)) = Var(ATV.applySortSub(sub,v))
                  and g(t) = if not(isPoly(t)) then t else f(t)
	      in
	         g t
	      end

fun applySortSubLst(sub,terms) =  
          if F.isEmptySub(sub) then terms 
          else  map (fn (t) => applySortSub(sub,t)) terms

fun doVars(terms,sub) = ATV.reconcileVars(terms,getVars,sub)

fun getPolyConstants(App({poly_constants,...})) = poly_constants
  | getPolyConstants(_) = []

fun doPolyConstants(terms,sub) = ATV.reconcilePolyConstants(terms,getPolyConstants,sub)

fun apply(sort_sub,new_vars,new_poly_constants_and_sorts,t) = 
          let fun f(t as App({root,args,sort,bits,vars,hash_code,poly_constants,...})) = 
		     if null(vars) then 
			  let val t' = applySortSub(sort_sub,t)
			  in
			     t'
			  end
		     else let val vars' = ATV.update(vars,new_vars)
                              val poly_constants' = ATV.updatePolyConstants(poly_constants,new_poly_constants_and_sorts)
			      val args' = map f args
			      val sort' = F.applySub(sort_sub,sort)
	 		      val root_word = makeWord({poly=F.hasVars(sort'),non_canonical=isNonCanonicalWord(bits),
                                                        involves_pred_based_sorts=involvesPredBasedSortsWord(bits),hasVars=not(null(vars'))})
			      val bits' = orTermWords(args',root_word)
			  in 
			    App({root=root,args=args',sort=sort',hash_code=hash_code,bits=bits',vars=vars',poly_constants=poly_constants'})
			  end
                | f(Var(v)) = (case Basic.findInList(new_vars,fn v' => ATV.nameEq(v,v')) of
				  SOME(v') => Var(v')
				| _ => Var(ATV.applySortSub(sort_sub,v)))
	        | f(t) = t
          in 
	     f(t)
	  end

fun applyLst(sort_sub,new_vars,new_poly_constants_and_sorts,terms) = map (fn t => apply(sort_sub,new_vars,new_poly_constants_and_sorts,t)) terms

fun makeNumApp(f:MS.mod_symbol,terms) = 
		let val f_code = MS.code(f) 
                    datatype num_sort = varSort | someNumSubsort of FTerm.term 
                    fun getRoot(sort) = case F.isApp(sort) of SOME(f,_) => f
		    fun getNSort(sort) = if F.isVar(sort) then varSort 
                                         else if SortOrder.areSubsorts(getRoot(sort),D.mreal_sort_symbol)
                                              then someNumSubsort(sort) 
					 else failLst(["Numeric sort was expected; instead, the sort "^
						      (F.toString(sort,F.makeVarSortPrinter()))^" was found."])
                    fun doBinaryApp(t1,t2) = 
	   	        let val (sort1,sort2) = (getSort(t1),getSort(t2))
			    fun makeSub(sort) = let val sub = F.empty_sub
						    val sub' = (case F.isVarOpt(sort1) of
								   SOME(v) => F.incSub(sub,(v,sort))
								 | _ => sub)
						in
						   (case F.isVarOpt(sort2) of
						       SOME(v) => F.incSub(sub',(v,sort))
                                                     | _ => sub')
						end
			    fun resSortAndSub() = 
				   (case (getNSort(sort1),getNSort(sort2)) of 
			                 (varSort,varSort) => (Data.real_sort,makeSub(Data.real_sort))
                                       | (someNumSubsort(sort1),someNumSubsort(sort2)) => (case SortOrder.lub(getRoot(sort1),getRoot(sort2)) of
                                                                                              SOME(s) => let val sort = FTerm.makeMConstant(s)
                                                                                                         in 
                                                                                                            (sort,makeSub(sort))
                                                                                                         end
                                                                                            | _ => Basic.fail("Not numeric subsorts..."))
                                       | (someNumSubsort(sort),varSort) => (sort1,makeSub(sort))
                                       | (varSort,someNumSubsort(sort)) => (sort,makeSub(sort)))
                       in
			 let   
                               val (res_sort,theta) = resSortAndSub()
                               val res_sort' = if f_code >= Util.less_sym_code andalso f_code <= Util.geq_sym_code then F.boolean_sort 
                                               else if f_code = Util.div_sym_code then F.real_sort else res_sort 
  	  	               val ((new_vars,theta'),vars_diff) = doVars([t1,t2],theta)
  	                       val ((new_poly_constants_and_their_sorts,theta''),constants_diff) = doPolyConstants([t1,t2],theta')
		  	      (* Also, optimize for the case when theta' is empty and vars_diff is false *)
		               val new_vars' = ATV.applySortSubLst(theta'',new_vars)
 	                       val new_poly_constants_and_their_sorts' = map (fn (c,sort) => (c,F.applySub(theta'',sort))) new_poly_constants_and_their_sorts
			       val terms' = applyLst(theta'',new_vars',new_poly_constants_and_their_sorts',terms)
			       val root_word = makeWord({poly=false,non_canonical=true,hasVars=false,involves_pred_based_sorts=false})
                               val hc = Basic.hashTwoWords(Basic.hashInt(f_code),Basic.hashWordList(terms',fastHash))
		         in
			    App({root=f,args=terms',sort=res_sort',vars=new_vars',poly_constants=new_poly_constants_and_their_sorts',hash_code=hc,
				bits=orTermWords(terms',root_word)})
			 end
                       end
                  fun PlusOrMinus(f) = (f_code = Util.sub_sym_code orelse f_code = Util.add_sym_code)
                  fun doUnaryApp(t) = 
                         let val arg_sort = getSort(t)
                             fun makeSub(sort) = (case F.isVarOpt(arg_sort) of SOME(v) => F.incSub(F.empty_sub,(v,sort))
						                             | _ => F.empty_sub)
 			     fun resSortAndSub() = 
				   (case getNSort(arg_sort) of
                                         varSort => (Data.int_sort,makeSub(Data.int_sort))
                                       | someNumSubsort(sort) => (sort,makeSub(sort)))
			    val (res_sort,theta) = resSortAndSub()
		            val ((new_vars,theta'),vars_diff) = doVars([t],theta)

			  (* Optimize for the case when theta' is empty and vars_diff is false *)
		            val new_vars' = ATV.applySortSubLst(theta',new_vars)
 	                    val new_poly_constants_and_their_sorts =  getPolyConstants(t)
			    val terms' = applyLst(theta',new_vars',new_poly_constants_and_their_sorts,terms)
			    val root_word = makeWord({poly=false,non_canonical=true,hasVars=false,involves_pred_based_sorts=false})
                            val hc = Basic.hashTwoWords(Basic.hashInt(f_code),Basic.hashWordList(terms',fastHash))
                         in
                            (if PlusOrMinus(f) then
			        App({root=f,args=terms',sort=res_sort,vars=new_vars',poly_constants=new_poly_constants_and_their_sorts,hash_code=hc,
				 bits=orTermWords(terms',root_word)})
			     else failLst [])
                         end
               in
                  (case terms of
                      [t1,t2] => doBinaryApp(t1,t2)
                    | [t] => doUnaryApp(t)
                    | _ => failLst [])
               end

fun doUnaryMinusOnLiteral(t,is_int) = 
    let val f = Names.msubtraction_symbol
        val sym_code = MS.code(f) 
        val hc = Basic.hashTwoWords(Basic.hashInt(sym_code),fastHash(t))
        val root_word = makeWord({poly=false,non_canonical=true,hasVars=false,involves_pred_based_sorts=false})
    in
      App({root=f,
           args=[t],
  	   sort=(if is_int then Data.int_sort else Data.real_sort),
 	   vars=[],
	   poly_constants=[],
	   hash_code=hc,
	   bits=orTermWords([t],root_word)})
    end

fun makeAppNormallyAndReturnSortSub(f,terms,from_side,param_sorts,result_sort,is_poly,has_pred_based_sorts) = 
                              let val arg_sorts = map getSort terms
 		                  val U = F.chooseUnificationProcedureForSortLists(param_sorts,arg_sorts)
		                  val theta = U(arg_sorts,param_sorts,from_side)
 	                          val ((new_vars,theta'),vars_diff) = doVars(terms,theta)
	                          val ((new_poly_constants_and_their_sorts,theta''),constants_diff) = doPolyConstants(terms,theta')
	                          val new_vars' = ATV.applySortSubLst(theta'',new_vars)
	                          val new_poly_constants_and_their_sorts' = map (fn (c,sort) => (c,F.applySub(theta'',sort))) new_poly_constants_and_their_sorts
		                  val terms' = applyLst(theta'',new_vars',new_poly_constants_and_their_sorts',terms)
	                          val sort' = F.applySub(theta'',result_sort)
                                  val poly_flag = F.hasVars(sort')
		                  val root_word = makeWord({poly=poly_flag,non_canonical=not(Data.isStructureConstructorBool(f)),hasVars=false,
                                                            involves_pred_based_sorts=has_pred_based_sorts})
		                  val new_poly_constants_and_their_sorts'' = if null(terms) andalso poly_flag then [(f,sort')] else new_poly_constants_and_their_sorts'
                                  val hc = Basic.hashTwoWords(Basic.hashInt(S.code(f)),Basic.hashWordList(terms',fastHash))
				  val app = App({root=f,args=terms',sort=sort',vars=new_vars',hash_code=hc,
				  		 poly_constants=new_poly_constants_and_their_sorts'',bits=orTermWords(terms',root_word)})
                              in
		                  (app,theta')
                              end

fun makeAppNormally(f,terms,from_side,param_sorts,result_sort,is_poly,has_pred_based_sorts) =
  #1(makeAppNormallyAndReturnSortSub(f,terms,from_side,param_sorts,result_sort,is_poly,has_pred_based_sorts))

fun makeAppAndReturnSortSubCore(f:MS.mod_symbol,terms) =  
	if Util.notNumeric(f) then 
           let val (param_sorts,result_sort,is_poly,has_pred_based_sorts) = D.getSignature(f)
           in
            if has_pred_based_sorts then
                 Basic.fail("Can't check pred-based sorts yet.")
            else makeAppNormallyAndReturnSortSub(f,terms,1,param_sorts,result_sort,is_poly,has_pred_based_sorts)
          end
	else (makeNumApp(f,terms),F.empty_sub)

fun makeAppAndReturnSortSub(f,terms) = makeAppAndReturnSortSubCore(f,terms)
	                    handle Basic.FailLst(msgs) => 
					failLst("Unable to infer a sort for the term: \n"^
						(fauxTermToPrettyString(0,f,terms))::msgs)
		      	         | F.solverIncompleteness => 
					failLst(["Unable to infer a sort for the term: \n"^
 			                         (fauxTermToPrettyString(0,f,terms))])

fun sortsMatch(fun_sort,arg_sorts) = 
   (case Data.funSortArity(fun_sort) of 
       SOME(n) => n = length(arg_sorts)
     | _ => false)

fun getFunctorSignature(f,args) = 
   if  MS.modSymEq(f,Names.app_fsym_mname) then 
         let val actual_args = tl args 
             val (fun_sort, arg_sorts, res_sort) = D.makeFunSort(actual_args)
             val lifted_app_sym_opt = (case (hd args) of 
                                          (t as App({root,args=[],...})) => 
                                            if Data.isLiftedFSym(root) andalso sortsMatch(getSort(t),arg_sorts) then SOME(MS.unlift(root)) else NONE
			                | _ => NONE)
         in
            ((fun_sort::arg_sorts,res_sort,true,false),lifted_app_sym_opt)
         end 
   else (D.getSignature(f),NONE)

fun makeApp1(f,terms,from_side) = 
	if Util.notNumeric(f) then 
           let val ((param_sorts,result_sort,is_poly,has_pred_based_sorts),lifted_app_sym_opt) = getFunctorSignature(f,terms)
           in
            (case lifted_app_sym_opt of 
               SOME(g) => makeApp1(g,tl terms,from_side)
             | _ => 
             if has_pred_based_sorts then
              ((makeAppNormally(f,terms,from_side,param_sorts,result_sort,is_poly,has_pred_based_sorts))
                handle _ => 
                  let fun loop([],_,arg_sorts',tccs) = (rev(arg_sorts'),tccs)
                        | loop(arg::more_args,param_sort::more_param_sorts,arg_sorts',tccs) = 
                              if F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(param_sort) then
                                 let val new_tcc = (arg,param_sort)
                                 in
                                   loop(more_args,more_param_sorts,param_sort::arg_sorts',new_tcc::tccs)
                                 end
                              else
                                   loop(more_args,more_param_sorts,(getSort arg)::arg_sorts',tccs)
                      val _ = print("\nGetting TCCs...\n")
                      val (arg_sorts,tccs) = loop(terms,param_sorts,[],[])
                      val _ = global_tccs := tccs@(!global_tccs)
	    	      val U = F.chooseUnificationProcedureForSortLists(param_sorts,arg_sorts)
		      val theta = U(arg_sorts,param_sorts,from_side)
	              val ((new_vars,theta'),vars_diff) = doVars(terms,theta)
	              val ((new_poly_constants_and_their_sorts,theta''),constants_diff) = doPolyConstants(terms,theta')
	              val new_vars' = ATV.applySortSubLst(theta'',new_vars)
	              val new_poly_constants_and_their_sorts' = map (fn (c,sort) => (c,F.applySub(theta'',sort))) new_poly_constants_and_their_sorts
		      val terms' = applyLst(theta'',new_vars',new_poly_constants_and_their_sorts',terms)
	              val sort' = F.applySub(theta'',result_sort)
                      val poly_flag = F.hasVars(sort')
		      val root_word = makeWord({poly=poly_flag,non_canonical=not(Data.isStructureConstructorBool(f)),hasVars=false,
                                                involves_pred_based_sorts=has_pred_based_sorts})
		      val new_poly_constants_and_their_sorts'' = if null(terms) andalso poly_flag then [(f,sort')] else new_poly_constants_and_their_sorts'
                      val hc = Basic.hashTwoWords(Basic.hashInt(S.code(f)),Basic.hashWordList(terms',fastHash))
		      val res = App({root=f,args=terms',sort=sort',vars=new_vars',hash_code=hc,
                                     poly_constants=new_poly_constants_and_their_sorts'',bits=orTermWords(terms',root_word)})
	          in
		    res
		  end)
            else 
                let 
                    val arg_sorts = map getSort terms
		    val U = F.chooseUnificationProcedureForSortLists(param_sorts,arg_sorts)
		    val theta = U(arg_sorts,param_sorts,from_side)
	            val ((new_vars,theta'),vars_diff) = doVars(terms,theta) 
	            val ((new_poly_constants_and_their_sorts,theta''),constants_diff) = doPolyConstants(terms,theta')
	            val new_vars' = ATV.applySortSubLst(theta'',new_vars)
	            val new_poly_constants_and_their_sorts' = map (fn (c,sort) => (c,F.applySub(theta'',sort))) new_poly_constants_and_their_sorts
		    val terms' = applyLst(theta'',new_vars',new_poly_constants_and_their_sorts',terms)
	            val sort' = F.applySub(theta'',result_sort)
                    val poly_flag = F.hasVars(sort')
		    val root_word = makeWord({poly=poly_flag,non_canonical=not(Data.isStructureConstructorBool(f)),hasVars=false,
                                              involves_pred_based_sorts=has_pred_based_sorts})
		    val new_poly_constants_and_their_sorts'' = if null(terms) andalso poly_flag then [(f,sort')] else new_poly_constants_and_their_sorts'
                    val hc = Basic.hashTwoWords(Basic.hashInt(S.code(f)),Basic.hashWordList(terms',fastHash))
		    val res = App({root=f,args=terms',sort=sort',vars=new_vars',hash_code=hc,
                                   poly_constants=new_poly_constants_and_their_sorts'',bits=orTermWords(terms',root_word)})
	        in
		   res
		end)
           end
	else 
            let
            in
	      makeNumApp(f,terms)
	    end

fun makeAppBinary(f,term1,term2,from_side) =  makeApp1(f,[term1,term2],from_side)

fun makeAppUnary(f,term,from_side) =  
	if Util.notNumeric(f) then 
           let val ((param_sorts,result_sort,is_poly,has_pred_based_sorts),lifted_app_sym_opt) = getFunctorSignature(f,[term])
           in
             if has_pred_based_sorts then
 	        let val arg_sort = getSort term
                    val arg_sorts = [arg_sort]
		    val U = F.chooseUnificationProcedureForSortLists(param_sorts,arg_sorts)
		    val theta = U(arg_sorts,param_sorts,from_side)
	            val ((new_vars,theta'),vars_diff) = ((getVars(term),theta),false)
	            val ((new_poly_constants_and_their_sorts,theta''),constants_diff) = ((getPolyConstants(term),theta'),false)
	            val new_vars' = ATV.applySortSubLst(theta'',new_vars)
	            val new_poly_constants_and_their_sorts' = map (fn (c,sort) => (c,F.applySub(theta'',sort))) new_poly_constants_and_their_sorts
		    val term' = apply(theta'',new_vars,new_poly_constants_and_their_sorts,term)
	            val sort' = F.applySub(theta'',result_sort)
                    val poly_flag = F.hasVars(sort')
		    val root_word = makeWord({poly=poly_flag,non_canonical=not(Data.isStructureConstructorBool(f)),hasVars=false,
                                              involves_pred_based_sorts=has_pred_based_sorts=has_pred_based_sorts})
		    val new_poly_constants_and_their_sorts'' = new_poly_constants_and_their_sorts'
                    val hc = Basic.hashTwoWords(Basic.hashInt(S.code(f)),fastHash(term'))
                    val terms' = [term']
		    val res = App({root=f,args=terms',sort=sort',vars=new_vars',hash_code=hc,
                                   poly_constants=new_poly_constants_and_their_sorts'',bits=orTermWords(terms',root_word)})
	        in
		   res
		end
             else 
 	        let val arg_sort = getSort term
                    val arg_sorts = [arg_sort]
		    val U = F.chooseUnificationProcedureForSortLists(param_sorts,arg_sorts)
		    val theta = U(arg_sorts,param_sorts,from_side)
	            val ((new_vars,theta'),vars_diff) = ((getVars(term),theta),false)
	            val ((new_poly_constants_and_their_sorts,theta''),constants_diff) = ((getPolyConstants(term),theta'),false)
	            val new_vars' = ATV.applySortSubLst(theta'',new_vars)
	            val new_poly_constants_and_their_sorts' = map (fn (c,sort) => (c,F.applySub(theta'',sort))) new_poly_constants_and_their_sorts
		    val term' = apply(theta'',new_vars,new_poly_constants_and_their_sorts,term)
	            val sort' = F.applySub(theta'',result_sort)
                    val poly_flag = F.hasVars(sort')
		    val root_word = makeWord({poly=poly_flag,non_canonical=not(Data.isStructureConstructorBool(f)),hasVars=false,
                                              involves_pred_based_sorts=has_pred_based_sorts=has_pred_based_sorts})
		    val new_poly_constants_and_their_sorts'' = new_poly_constants_and_their_sorts'
                    val hc = Basic.hashTwoWords(Basic.hashInt(S.code(f)),fastHash(term'))
                    val terms' = [term']
		    val res = App({root=f,args=terms',sort=sort',vars=new_vars',hash_code=hc,
                                   poly_constants=new_poly_constants_and_their_sorts'',bits=orTermWords(terms',root_word)})
	        in
		   res
		end
           end
	else makeNumApp(f,[term])

fun makeAppGeneric(f,terms,thunk) =  
                                 ((thunk()) 			      
    			            handle Basic.FailLst(msgs) => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,terms))
                                        in
					  failLst(msg::msgs)
                                        end
				   | F.solverIncompleteness => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,terms))
                                        in
					  failLst([msg])
                                        end)

fun makeAppGenericNew(f,terms) =  
                                 ((makeApp1(f,terms,1)) 
    			            handle Basic.FailLst(msgs) => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,terms))
                                        in
					  failLst(msg::msgs)
                                        end
				   | F.solverIncompleteness => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,terms))
                                        in
					  failLst([msg])
                                        end)

fun makeAppGenericUnaryNew(f,term) =  
                                 ((makeAppUnary(f,term,1))
    			            handle Basic.FailLst(msgs) => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,[term]))
                                        in
					  failLst(msg::msgs)
                                        end
				   | F.solverIncompleteness => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,[term]))
                                        in
					  failLst([msg])
                                        end)
					
fun makeAppGenericBinaryNew(f,term1,term2) =  
                                 ((makeAppBinary(f,term1,term2,1))
    			            handle Basic.FailLst(msgs) => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,[term1,term2]))
                                        in
					  failLst(msg::msgs)
                                        end
				   | F.solverIncompleteness => 
                                        let val msg = "Unable to infer a sort for the term: \n"^(fauxTermToPrettyString(0,f,[term1,term2]))
                                        in
					  failLst([msg])
                                        end)

fun makeVar(v) = Var(v)

fun makeAppUnary(f,term) = makeAppGenericUnaryNew(f,term)
fun makeAppBinary(f,term1,term2) = makeAppGenericBinaryNew(f,term1,term2)


fun makeApp(f,terms) = let val res = makeAppGeneric(f,terms,(fn () => makeApp1(f,terms,1)))
                       in res end

fun makeApp(f,terms) = makeAppGenericNew(f,terms)

fun makeApp'(f,terms) = makeAppGeneric(f,terms,(fn () => makeApp1(f,terms,2)))

fun makeConstant(c) = makeApp(c,[])

fun makeSortedConstant(c,tagged_sort) = 
	let val poly_flag = F.hasVars(tagged_sort)
            val root_word = makeWord({poly=poly_flag,non_canonical=not(Data.isStructureConstructorBool(c)),hasVars=false,
                                      involves_pred_based_sorts=F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(tagged_sort)})
            val new_poly_constants_and_their_sorts = if poly_flag then [(c,tagged_sort)] else []
            val hc = Basic.hashTwoWords(Basic.hashInt(S.code(c)),0w0)
	in
  	   App({root=c,args=[],hash_code=hc,poly_constants=new_poly_constants_and_their_sorts,sort=tagged_sort,vars=[],bits=root_word})
	end

fun makeSortedConstantAux(c,given_sort,is_poly) = 
        let val new_poly_constants_and_their_sorts = if is_poly then [(c,given_sort)] else []
            val hc = Basic.hashTwoWords(Basic.hashInt(S.code(c)),0w0)
        in
	   App({root=c,args=[],hash_code=hc,sort=given_sort,vars=[],poly_constants=new_poly_constants_and_their_sorts,
                bits=makeWord({poly=is_poly,non_canonical=not(Data.isStructureConstructorBool(c)),hasVars=false,
                               involves_pred_based_sorts=F.findOutDynamicallyIfASortHasPredicateBasedSortSymbolsInIt(given_sort)})})
        end
      									    
fun makeEquality(t1,t2) = makeApp(Names.mequal_logical_symbol,[t1,t2])

val default_word = 0w15 (* I.e., 1111  *)

fun isVarOpt(Var(v)) = SOME(v) 
  | isVarOpt(_) = NONE

fun isVar(Var(v)) = true
  | isVar(_) = false

fun isConstant(App({root,args=[],...})) = SOME(root)
  | isConstant(_) = NONE

fun isNumConstantOpt(numTerm(ath_num)) = SOME(ath_num)
  | isNumConstantOpt(_) = NONE

fun isNumConstant(numTerm(_)) = true
  | isNumConstant(_) = false

fun isIdeConstant(ideTerm(s)) = SOME(MetaId.name(s))
  | isIdeConstant(_) = NONE

fun isGeneralConstant(App({args=[],...})) = true
  | isGeneralConstant(numTerm(_)) = true
  | isGeneralConstant(ideTerm(_)) = true
  | isGeneralConstant(_) = false

fun isGround(t) = not(hasVars(t))

fun areGround(terms) = List.all isGround terms
     
fun getConstantChildren(App({args,...})) = List.filter isGeneralConstant args
  | getConstantChildren(_) = []

fun getChildren(App({args,...})) = args
 |  getChildren(_) = []

fun isGeneralConstant2(App({root,args=[],...})) = SOME(S.name(root))
  | isGeneralConstant2(numTerm(n)) = SOME(A.athNumberToString(n))
  | isGeneralConstant2(ideTerm(x)) = SOME(MetaId.name(x))
  | isGeneralConstant2(_) = NONE

fun isApp(App({root,args,...})) = SOME(root,args)
  | isApp(_) = NONE
  
fun dom(t) = let fun loop([],i,results) = results
                   | loop(ith_child::rest,i,results) = let val S = map (fn pos => i::pos) (dom ith_child)
                                                       in
							  loop(rest,i+1,S@results)
                                                       end
             in
               (case isApp(t) of 
                   SOME(f,children) => ([]::(loop(children,1,[])))
                 | _ => [[]])
             end

fun subterm(t,[]) = t
  | subterm(t,i::rest) = subterm(Basic.nth(getChildren(t),i-1),rest)
     
fun distance(t1,t2) = 
          (case (isApp(t1),isApp(t2)) of 
              (SOME(f1,args1),SOME(f2,args2)) => if MS.modSymEq(f1,f2) then 
                                                   (if null(args1) then 0.0 else
                                                       let val e1 = Real.*(2.0,Real.fromInt(length(args1))) 
                                                           val e2 = distanceLst(args1,args2,0.0)
                                                       in
                                                          Real.*(Real./(1.0,e1),e2)
                                                       end)
                                                 else 1.0
            | _ => (if termEq(t1,t2) then 0.0 else 1.0))
and distanceLst([],[],sum) = sum 
  | distanceLst(t1::rest1,t2::rest2,sum) = distanceLst(rest1,rest2,sum+(distance(t1,t2)))

fun varOccursIn(v,t) = 
           let fun f(Var(v')) = varEq(v,v')
                 | f(App({vars,...})) = Basic.findInSorted(v,vars,ATV.compare)
                 | f(_) = false
           in
              if hasVars(t) then f(t) else false  
           end

fun replaceVarByVar(v1,v2,t) = 
      (** Replace every occurrence of v1 inside t by v2  **)
      (** We assume that v1 and v2 have identical sorts. **)
      let fun f(s as Var(v)) = if ATV.nameEq(v1,v) then Var(v2) else s
  	    | f(s as App({root,hash_code,args,sort,bits,poly_constants,vars,...})) = 
                if Basic.findInSorted(v1,vars,ATV.compareNames) then 
		     let val args' = map g args
		       val vars' = Basic.removeAndInsertInSortedList(v1,v2,vars,ATV.compareNames)
                       val hc = Basic.hashTwoWords(Basic.hashInt(S.code(root)),Basic.hashWordList(args',fastHash))
                   in
		      App({root=root,hash_code=hc,args=args',sort=sort,bits=bits,poly_constants=poly_constants,vars=vars'})		
		   end
                else s
            | f(t) = t
          and g(s) = if hasVars(s) then f(s) else s
      in
         g t
      end

fun replaceFSymsByFsyms(t,fmap) = 
           let fun loop(t as Var(_)) = t
                 | loop(App({root,hash_code,args,sort,bits,poly_constants,vars,...})) = 
                     let val root' = (case MS.lookUp(fmap,root) of
                                         SOME(sym) => sym
                                       | _ => root)
                         val (_,res_sort,_,has_pred_based_sorts) = Data.getSignature(root')
                         val args' = map loop args
                         val arg_bits = if involvePredBasedSorts(args') orelse has_pred_based_sorts then hasPredBasedSortsWord else zeroWord
                         val hc' = Basic.hashTwoWords(Basic.hashInt(S.code(root')),Basic.hashWordList(args',fastHash))
                         val bits' = orWords(bits,arg_bits)
                     in
                        App({root=root',args=args',hash_code=hc',sort=sort,bits=bits',poly_constants=poly_constants,vars=vars})
                     end
                 | loop(t) = t
           in
              loop(t)
           end
fun fsymOccursIn(f,App({root,args,...})) = fsymEq(f,root) orelse Basic.exists(args,fn t => fsymOccursIn(f,t))
  | fsymOccursIn(f,_) = false

fun getVarsAndHeights(t) = 
          let fun f(Var(v),n,map) = (case ATV.lookUp(map,v) of
                                        SOME(v,lst) => ATV.enter(map,v,(v,n::lst))
                                      | _ => ATV.enter(map,v,(v,[n])))
                | f(App({root,args as _::_,...}),n,map) = fLst(args,n+1,map)
                | f(_,_,map) = map                 
              and fLst([],n,map) = map
                | fLst(t::more,n,map) = fLst(more,n,f(t,n,map))
          in
             ATV.listImages(f(t,0,ATV.empty_mapping))
          end            

fun makeVarHeightMap(t,vars) = 
          let fun f(Var(v),n,map) = if Basic.isMemberEq(v,vars,ATV.athTermVarEq)
                                    then GMap.augment(map,(v,n)) else map
                | f(App({args as _::_,...}),n,map) = fLst(args,n+1,map)
                | f(_,_,map) = map
              and
                  fLst([],n,map) = map
                | fLst(t::more,n,map) = fLst(more,n,f(t,n,map))
          in
             f(t,0,GMap.empty)
          end 

fun posReplace(s,pos,t) = 
       let fun loop([],current,i,rest_pos,results) = rev(results)
       	     | loop(terms as (arg::more),current,i,rest_pos,results) = 
                    let val res = if current = i then posReplace(arg,rest_pos,t)
                                  else arg
                    in
                       loop(more,current+1,i,rest_pos,res::results)
                    end
       in 
          (case pos of
              [] => t
            | i::rest => (let val _ = ()
                          in                          
                            (case isApp(s) of 
                               SOME(f,args) => let val results = loop(args,1,i,rest,[])
                                               in makeApp(f,results)
                                               end)
                          end))
       end

(*====================================================================================
                           Substitutions for Athena terms
====================================================================================*)

type sub = (variable * term) ATV.name_mapping

val empty_sub = ATV.empty_name_mapping 

fun isEmptySub(tab) = ATV.isEmptyNameMapping(tab) 

fun supp(tab:sub) = 
          let fun f((v,_),accum) = v::accum
          in
              ATV.nameFoldl f [] tab
          end

fun incSub(tab:sub,(v,term)) = 
           ((case (isApp(makeEquality(Var(v),term))) of 
                SOME(_,[Var(new_var),new_term]) => (ATV.nameEnter(tab,new_var,(new_var,new_term))))
           handle _ => tab)

fun incSubAndReturnSubAndSuccessFlag(tab:sub,(v,term)) = 
           ((case (isApp(makeEquality(Var(v),term))) of 
                SOME(_,[Var(new_var),new_term]) => ((ATV.nameEnter(tab,new_var,(new_var,new_term))),true))
         handle _ => (tab,false))

infix ++

fun sub ++ (v,t) = incSub(sub,(v,t))

fun extendSub(sub,[]) = sub 
  | extendSub(sub,(v,t)::rest) = extendSub(sub++(v,t),rest)

fun makeSub(pairs) = extendSub(empty_sub,pairs)

fun applySub(tab:sub,t) = 
       let fun appSub(t as App({root,args,bits,...})) = 
		  if hasVarsWord(bits) then
		     let val args' = map appSub args 
                         val res = makeApp'(root,args') 
		     in
			  res 
		     end 
		  else t
             | appSub(t as Var(v)) = 
                  let val v_sort = ATV.getSort(v)
                      fun debugPrint(str) = if !Options.silent_mode then () else print(str)
                  in
                    (case ATV.nameLookUp(tab,v) of 
                        SOME(var,var_val) => ((let val var_sort = ATV.getSort(var)
                                                   val U = F.chooseUnificationProcedureForSorts(var_sort,v_sort)
                                                   val sort_sub = U([var_sort],[v_sort],~1)
                                                   val term_res' = applySortSub(sort_sub,var_val)
                                                 in
                                                    term_res'
                                                 end) handle _ => t)
                      | _ => t)
                  end
             | appSub(t) = t
       in
         appSub(t)
       end

fun subToString(tab) = 
		let val support = supp(tab)
		in
		   Basic.printListStr(support,fn v => (toStringDefault(Var(v)))^" --> "^
			 	 	              (toStringDefault(applySub(tab,Var v))),"\n")
		end

fun makeMonomorphicInstance(t) = 
       let val svars = sortVars(t)
           val sort_sub  = F.makeMonoSortSub(svars)
       in
         applySortSub(sort_sub,t)
       end
	
fun applySubLst(sub,lst) = map (fn t => applySub(sub,t)) lst
     
fun rangeVars(tab:sub) =  
      let val var_set = ATV.nameFoldl (fn ((_,t),accum) => (getVars t)@accum) [] tab
      in
         var_set 
      end

fun inSupp(v,s) = not (applySub(s,Var(v)) == Var(v))


fun nameInSupp(v,sub) =
        (case ATV.nameLookUp(sub,v) of 
            SOME(_) => true
          | _ => false)

fun inSupp(v,s) = nameInSupp(v,s) 

fun subEq(sub1 as tab1,sub2 as tab2) = 
      let val supp1 = supp(sub1)
      in
         Basic.listEq(supp1,supp(sub2),ATV.athTermVarEq) andalso
         Basic.forall(supp1,(fn v => applySub(sub1,Var(v)) == applySub(sub2,Var(v))))
      end

fun composeSubs(sub2 as tab2, sub1 as tab1) = 
         let val sub1' as tab1' = ATV.nameMap (fn (v,v_val) => (v,applySub(sub2,v_val))) tab1
             fun f((v,v_val),sub_accum) = 
                   if inSupp(v,sub1') then sub_accum else ATV.nameEnter(sub_accum,v,(v,v_val))
         in
            ATV.nameFoldl f tab1' tab2
         end

fun replace(v,t1,t2) =
        if isGround(t2) then t2 
        else
           let val unit_sub = makeSub([(v,t1)])
           in
             applySub(unit_sub,t2)
	   end 

fun testSub(sub as tab) = 
      let val db = false 
      in
          if db then (print("\nNumber of variables in support: "^(Int.toString(length(supp(sub))))^"\n");
                      Basic.continue())
          else ()
      end

fun sameVars(v,s) = 
          (case s of
              Var(v') => ATV.athTermVarLitEq(v,v')
            | _ => false)

fun isDoubleNegation(App({root=root1,args=[App({root=root2,args=[numTerm(n)],...})],...})) = 
        if (MS.modSymEq(root1,Names.msubtraction_symbol) andalso MS.modSymEq(root2,Names.msubtraction_symbol)) 
	then SOME(n) else NONE

val (match,matchLst) = 
          let fun m(App({root=fsym1,sort=sort1,args=args1,...}),
		    App({root=fsym2,sort=sort2,args=args2,...}),sub,sort_sub) = 
			let val sort_sub' = F.matchModuloSub(sort1,sort2,sort_sub)
			in
		           if MS.modSymEq(fsym1,fsym2) 
			   then mLst(args1,args2,sub,sort_sub)
			   else failLst([])
			end
                | m(s:term,t as Var(v),sub,sort_sub) = 
                      let val (term_sort,var_sort) = (getSort(s),getSort(t))
                          val new_sort_sub = F.matchModuloSub(term_sort,var_sort,sort_sub)
                          val new_var_sort = F.applySub(new_sort_sub,var_sort)
                          val new_var = ATV.athTermVarWithSort(ATV.name(v),new_var_sort)
                          val new_term = applySortSub(new_sort_sub,s)
                      in
                           if inSupp(new_var,sub) then
                              (if termEq(applySub(sub,Var(new_var)),new_term) then 
                                  (sub,new_sort_sub)
                               else failLst([]))
                            else 
                               (ATV.nameEnter(sub,new_var,(new_var,new_term)),new_sort_sub)
                      end
                | m(s as numTerm(n1),t as numTerm(n2),sub,sort_sub) = 
                         if A.athNumEquality(n1,n2) then (sub,sort_sub) else failLst([])
                | m(ideTerm(x1),ideTerm(x2),sub,sort_sub) = if MetaId.eq(x1,x2) then (sub,sort_sub) else failLst([])
                | m(_) = failLst([])
              and mLst(s::more1,t::more2,sub,sort_sub) =   
                    let val (sub',sort_sub') = m(s,t,sub,sort_sub)
                    in 
                       mLst(more1,more2,composeSubs(sub',sub),F.composeSubs(sort_sub',sort_sub))
                    end
                | mLst([],[],sub,sort_sub) = (sub,sort_sub)
                | mLst(_) = failLst([])
          in
            ((fn (s,t) => ((case m(s,t,empty_sub,F.empty_sub) of 
                               (sub,sort_sub) => (SOME(sub))) handle _ => NONE),
             (fn (slst,tlst) => ((case mLst(slst,tlst,empty_sub,F.empty_sub) of 
                                     (sub,sort_sub) => SOME(sub)) handle _ => NONE))))
          end

val (matchRWraw,matchLstRWraw) = 
          let fun m(App({root=fsym1,sort=sort1,args=args1,...}),
		    App({root=fsym2,sort=sort2,args=args2,...}),sub,sort_sub,uvars) = 
		    if MS.modSymEq(fsym1,fsym2) then
			let val sort_sub' = F.matchModuloSub(sort1,sort2,sort_sub)
			in
                           mLst(args1,args2,sub,sort_sub',uvars)
			end
                    else failLst([])
                | m(s:term,t as Var(v),sub,sort_sub,uvars) = 
                   if Basic.isMemberEq(v,uvars,ATV.varInstance) then 
                      if sameVars(v,s) then
                          (sub,sort_sub)
	              else                               
                      let val (term_sort,var_sort) = (getSort(s),getSort(t))
                          val new_sort_sub = F.matchModuloSub(term_sort,var_sort,sort_sub)
                          val new_var_sort = F.applySub(new_sort_sub,var_sort)
                          val new_var = ATV.athTermVarWithSort(ATV.name(v),new_var_sort)
                          val new_term = applySortSub(new_sort_sub,s)
                          val cond1 = inSupp(new_var,sub)
                          fun cond2() = let val term = applySub(sub,Var(new_var))
                                            val res = termEq(term,new_term)
                                        in res end
                      in
                           if cond1 then
                              (if cond2() then 
                                  (sub,new_sort_sub)
                               else failLst([]))
                            else 
                               (ATV.nameEnter(sub,new_var,(new_var,new_term)),new_sort_sub)
                      end
                   else (if termEq(s,t) then (sub,sort_sub) else failLst([]))
                | m(s as numTerm(n1),t as numTerm(n2),sub,sort_sub,_) = 
                         if A.athNumEquality(n1,n2) then (sub,sort_sub) else failLst([])
                | m(ideTerm(x1),ideTerm(x2),sub,sort_sub,_) = if MetaId.eq(x1,x2) then (sub,sort_sub) else failLst([])
                | m(_) = failLst([])
              and mLst(s::more1,t::more2,sub,sort_sub,uvars) =   
                    let val (sub',sort_sub') = m(s,t,sub,sort_sub,uvars)
                    in 
                       mLst(more1,more2,composeSubs(sub',sub),F.composeSubs(sort_sub',sort_sub),uvars)
                    end
                | mLst([],[],sub,sort_sub,_) = (sub,sort_sub)
                | mLst(_) = failLst([])
          in
            ((fn (s,t,sub,sort_sub,uvars) => (let val _ = ()
                                                  val res = (case m(s,t,sub,sort_sub,uvars) of 
                                                              (sub,sort_sub) => SOME(sub,sort_sub))
                                                  val _ = ()
                                              in
                                                res
                                              end) handle _ => NONE),
             (fn (slst,tlst,sub,sort_sub,uvars) => ((case mLst(slst,tlst,sub,sort_sub,uvars) of 
                                                      (sub,sort_sub) => SOME(sub,sort_sub)) handle _ => NONE)))
          end

(***
matchRWrawWithBanned works just like matchRWraw, except that it also 
takes an additional last argument, a list of variables V. The substitution
cannot contain any bindings x -> t if t contains an element of V.
Essentially, the variables in V are "banned" from appearing in the resulting
substitution.
***)

fun hasNoBannedVars(new_term:term,banned:variable list) =
   let val term_vars = getVars(new_term)
   in
       Basic.forall(term_vars,fn v:variable => not(Basic.isMemberEq(v,banned,ATV.athTermVarEq)))
   end

val (matchRWrawWithBanned,matchLstRWrawWithBanned) = 
          let fun m(App({root=fsym1,sort=sort1,args=args1,...}),
		    App({root=fsym2,sort=sort2,args=args2,...}),sub,sort_sub,uvars,banned) = 
		    if MS.modSymEq(fsym1,fsym2) then
			let val sort_sub' = F.matchModuloSub(sort1,sort2,sort_sub)
			in
                           mLst(args1,args2,sub,sort_sub',uvars,banned)
			end
                    else failLst([])
                | m(s:term,t as Var(v),sub,sort_sub,uvars,banned) = 
                   if Basic.isMemberEq(v,uvars,ATV.varInstance) then 
                      if sameVars(v,s) then
                          (sub,sort_sub)
	              else                               
                      let val (term_sort,var_sort) = (getSort(s),getSort(t))
                          val new_sort_sub = F.matchModuloSub(term_sort,var_sort,sort_sub)
                          val new_var_sort = F.applySub(new_sort_sub,var_sort)
                          val new_var = ATV.athTermVarWithSort(ATV.name(v),new_var_sort)
                          val new_term = applySortSub(new_sort_sub,s)
                          val cond1 = inSupp(new_var,sub)
                          fun cond2() = let val term = applySub(sub,Var(new_var))
                                            val res = termEq(term,new_term)
                                        in res end
                      in
                           if cond1 then
                              (if cond2() then 
                                  (sub,new_sort_sub)
                               else failLst([]))
                            else 
                               if hasNoBannedVars(new_term,banned) then
			          (ATV.nameEnter(sub,new_var,(new_var,new_term)),new_sort_sub)
                               else failLst([])
                      end
                   else (if termEq(s,t) then (sub,sort_sub) else failLst([]))
                | m(s as numTerm(n1),t as numTerm(n2),sub,sort_sub,_,banned) = 
                         if A.athNumEquality(n1,n2) then (sub,sort_sub) else failLst([])
                | m(ideTerm(x1),ideTerm(x2),sub,sort_sub,_,_) = if MetaId.eq(x1,x2) then (sub,sort_sub) else failLst([])
                | m(_) = failLst([])
              and mLst(s::more1,t::more2,sub,sort_sub,uvars,banned) =   
                    let val (sub',sort_sub') = m(s,t,sub,sort_sub,uvars,banned)
                    in 
                       mLst(more1,more2,composeSubs(sub',sub),
		       F.composeSubs(sort_sub',sort_sub),uvars,banned)
                    end
                | mLst([],[],sub,sort_sub,_,_) = (sub,sort_sub)
                | mLst(_) = failLst([])
          in
            ((fn (s,t,sub,sort_sub,uvars,banned:variable list) => 
	    	 	(let val res = (case m(s,t,sub,sort_sub,uvars,banned) of 
                                          (sub,sort_sub) => SOME(sub,sort_sub))
                         in
                            res
                         end) handle _ => NONE),
             (fn (slst,tlst,sub,sort_sub,uvars,banned:variable list) =>	
	     	 ((case mLst(slst,tlst,sub,sort_sub,uvars,banned) of 
                                                      (sub,sort_sub) => SOME(sub,sort_sub)) handle _ => NONE)))
          end



fun matchRW(s,t,uvars) = 
  (case matchRWraw(s,t,empty_sub,F.empty_sub,uvars) of 
     SOME(sub,_) => SOME(sub)
   | _ => NONE)

fun matchLstRW(s_lst,t_lst,uvars) = 
       (case matchLstRWraw(s_lst,t_lst,empty_sub,F.empty_sub,uvars) of 
           SOME(sub,_) => SOME(sub)
         | _ => NONE)

fun matches(s,t) = case match(s,t) of NONE => false | _ => true

fun variants(s,t) = matches(s,t) andalso matches(t,s)

fun specialMatch(s,t) = 
       let val match = ref(true)
           fun f(_,Var(_),ov) = ov
             | f(Var(x),App(_),ov) = (match := false;x::ov)
             | f(App({root=f,args=terms1,sort=sort1,...}),
		 App({root=g,args=terms2,sort=sort2,...}),ov) = 
			if not(MS.modSymEq(f,g)) orelse not(F.isInstanceOf(sort1,sort2)) 
			then failLst([]) else fLst(terms1,terms2,ov)
             | f(_,_,_) = failLst([])
           and
               fLst(s::more1,t::more2,ov) = fLst(more1,more2,f(s,t,ov))
             | fLst([],[],ov) = ov
             | fLst(_,_,_) = raise Basic.Never 
           val ov = f(s,t,[]) handle _ => (match := false;[])
       in          
          (!match,ov)
       end

val (unifyEx,unifyExLst) = 
             let fun error(t1,t2,msgs) = let val msg1 = ("\nFailed to unify the terms\n"^
				                        (toPrettyString(0,t1,F.varToString))^ 
					 	       "\nand\n"^(toPrettyString(0,t2,F.varToString))^".\n")
					    val messages = msg1::msgs
					in
					   failLst(messages)
					end
		 fun errorLst(L1,L2,msgs) = let val msg1 = ("\nFailed to unify the term lists:\n"^
							  (Basic.printListStrCommas(L1,fn s => 
								toPrettyStringDefault(0,s)))^
							  "\nand\n"^(Basic.printListStrCommas(L2,
		 					     fn s => toPrettyStringDefault(0,s))))
					       val messages = msg1::msgs
					   in	
					      Basic.failLst(messages)
					   end
		 fun U(t1 as App({root=f,args=terms1,sort=sort1,...}),
		       t2 as App({root=g,args=terms2,sort=sort2,...})) = 
			 let val (sort1,sort2) = (getSort(t1),getSort(t2))
                             val U = F.chooseUnificationProcedureForSorts(sort1,sort2)
			     val sort_sub = U([sort1],[sort2],~1)
				     handle _ => failLst(["Attempt to unify two terms of incompatible "^
						          "sorts:\n"^F.toPrettyString(0,sort1,F.varToString)^
							  "\nand\n"^F.toPrettyString(0,sort2,F.varToString)])
			     val (terms1',terms2') = (applySortSubLst(sort_sub,terms1),
						      applySortSubLst(sort_sub,terms2))
                         in
			    if fsymEq(f,g) then ULst(terms1',terms2') else 
			    failLst(["Cannot unify "^(toStringDefault(t1))^" and "^(toStringDefault(t2))])
			 end 			    
                  | U(s as Var(v),t) = 
                    let val v_sort = ATV.getSort(v)
                        fun occursCheck() = if hasVars(t) then Basic.exists(getVars t,fn v' => ATV.nameEq(v,v') andalso F.unifiable(ATV.getSort(v'),v_sort)) else false 
                    in
	             if occursCheck() then
                        (if t == s then empty_sub
                         else failLst(["Failed occurs check: "^(ATV.toStringDefault(v))^
				        " occurs in "^(toStringDefault(t))]))
                     else
                         (case incSubAndReturnSubAndSuccessFlag(empty_sub,(v,t)) of 
                            (sub,true) => sub
                          | (_,false) => (case t of 
                                            Var(v') => (case incSubAndReturnSubAndSuccessFlag(empty_sub,(v',s)) of  
                                                         (sub,true) => sub
                                                       | _ => failLst([]))))
                    end
                  | U(s,t as Var(_)) = U(t,s)
                  | U(t1 as numTerm(n1),t2 as numTerm(n2)) = 
			if A.athNumEquality(n1,n2) then empty_sub else error(t1,t2,[])
                  | U(t1 as ideTerm(x1),t2 as ideTerm(x2)) = 
			 if MetaId.eq(x1,x2) then empty_sub else error(t1,t2,[])
                  | U(t1,t2) = failLst([])
                  and
                    ULst(t1::rest1,t2::rest2) = 
                       let val sub = U(t1,t2)
                           val (new_rest1,new_rest2) = (applySubLst(sub,rest1),applySubLst(sub,rest2))
                           val sub' = ULst(new_rest1,new_rest2)
                           in
                             composeSubs(sub',sub)
                       end
                  | ULst([],[]) = empty_sub
                  | ULst(_,_) = failLst(["Attempt to unify two term lists of different length"])
                 in
                   (fn (s,t) => if areGround([s,t]) then
                                   (if FTerm.unifiable(getSort(s),getSort(t)) andalso 
				      termEq(s,t) then empty_sub else error(s,t,[]))
                                else U(s,t) handle Basic.FailLst(msgs) => error(s,t,msgs),
                    fn (slist,tlist) => ULst(slist,tlist) handle Basic.FailLst(msgs) => errorLst(slist,tlist,msgs))
             end

fun unify(s,t) = SOME(unifyEx(s,t)) handle _ => NONE

fun unifyLst(sl,tl) = SOME(unifyExLst(sl,tl)) handle _ => NONE

val (unifyExRW,unifyExLstRW) = 
             let fun error(t1,t2,msgs) = let val msg1 = ("\nFailed to unify the terms\n"^
				                        (toPrettyString(0,t1,F.varToString))^ 
					 	       "\nand\n"^(toPrettyString(0,t2,F.varToString))^".\n")
					    val messages = msg1::msgs
					in
					   failLst(messages)
					end
		 fun errorLst(L1,L2,msgs) = let val msg1 = ("\nFailed to unify the term lists:\n"^
							  (Basic.printListStrCommas(L1,fn s => 
								toPrettyStringDefault(0,s)))^
							  "\nand\n"^(Basic.printListStrCommas(L2,
		 					     fn s => toPrettyStringDefault(0,s))))
					       val messages = msg1::msgs
					   in	
					      Basic.failLst(messages)
					   end
		 fun U(t1 as App({root=f,args=terms1,sort=sort1,...}),
		       t2 as App({root=g,args=terms2,sort=sort2,...}),var_constants) = 
			 let val (sort1,sort2) = (getSort(t1),getSort(t2))
                             val U = F.chooseUnificationProcedureForSorts(sort1,sort2)
			     val sort_sub = U([sort1],[sort2],~1)
				     handle _ => failLst(["Attempt to unify two terms of incompatible "^
						          "sorts:\n"^F.toPrettyString(0,sort1,F.varToString)^
							  "\nand\n"^F.toPrettyString(0,sort2,F.varToString)])
			     val (terms1',terms2') = (applySortSubLst(sort_sub,terms1),
						      applySortSubLst(sort_sub,terms2))
                         in
			    if fsymEq(f,g) then ULst(terms1',terms2',var_constants) else 
			    failLst(["Cannot unify "^(toStringDefault(t1))^" and "^(toStringDefault(t2))])
			 end 			    
                  | U(s as Var(v),t,var_constants) = 
                     if not(Basic.isMemberEq(v,var_constants,ATV.athTermVarEq)) then 
   	                (if varOccursIn(v,t) then
                           (if t == s then empty_sub
                            else failLst(["Failed occurs check: "^(ATV.toStringDefault(v))^
   				           " occurs in "^(toStringDefault(t))]))
                         else
                            (case incSubAndReturnSubAndSuccessFlag(empty_sub,(v,t)) of 
                               (sub,true) => sub
                             | (_,false) => (case t of 
                                               Var(v') => (case incSubAndReturnSubAndSuccessFlag(empty_sub,(v',s)) of  
                                                            (sub,true) => sub
                                                          | _ => failLst([])))))
                     else (case t of 
                             Var(v') => (case incSubAndReturnSubAndSuccessFlag(empty_sub,(v',s)) of  
                                            (sub,true) => if not(Basic.isMemberEq(v',var_constants,ATV.athTermVarEq)) 
                                                          then sub else 
                                                           (if ATV.athTermVarEq(v,v') then empty_sub else failLst([]))
                                           | _ => (if ATV.athTermVarEq(v,v') then empty_sub else failLst([])))
                           | _ => failLst([]))
                  | U(s,t as Var(_),var_constants) = U(t,s,var_constants)
                  | U(t1 as numTerm(n1),t2 as numTerm(n2),_) = 
			if A.athNumEquality(n1,n2) then empty_sub else error(t1,t2,[])
                  | U(t1 as ideTerm(x1),t2 as ideTerm(x2),_) = 
			 if MetaId.eq(x1,x2) then empty_sub else error(t1,t2,[])
                  | U(t1,t2,_) = failLst([])
                  and
                    ULst(t1::rest1,t2::rest2,var_constants) = 
                       let val sub = U(t1,t2,var_constants)
                           val (new_rest1,new_rest2) = (applySubLst(sub,rest1),applySubLst(sub,rest2))
                           val sub' = ULst(new_rest1,new_rest2,var_constants)
                           in
                             composeSubs(sub',sub)
                       end
                  | ULst([],[],_) = empty_sub
                  | ULst(_) = failLst(["Attempt to unify two term lists of different length"])
                 in
                   (fn (s,t,var_constants) => if areGround([s,t]) then
                                         (if FTerm.unifiable(getSort(s),getSort(t)) andalso 
    				             termEq(s,t) then empty_sub else error(s,t,[]))
                                      else U(s,t,var_constants) handle Basic.FailLst(msgs) => error(s,t,msgs),
                    fn (slist,tlist,var_constants) => ULst(slist,tlist,var_constants) 
                                                        handle Basic.FailLst(msgs) => errorLst(slist,tlist,msgs))
             end

fun unifyRW(s,t,var_constants) = SOME(unifyExRW(s,t,var_constants)) handle _ => NONE

fun unifyLstRW(terms1,terms2,var_constants) = SOME(unifyExLstRW(terms1,terms2,var_constants)) handle _ => NONE

fun hashConstant(code) = Basic.hashTwoWords(Basic.hashInt(code),0w0)

val true_term = App({root=Names.mtrue_logical_symbol,
                     hash_code=hashConstant(MS.code(Names.mtrue_logical_symbol)),args=[],poly_constants=[],sort=F.boolean_sort,bits=zeroWord,vars=[]});

val false_term = App({root=Names.mfalse_logical_symbol,hash_code=hashConstant(MS.code(Names.mfalse_logical_symbol)),args=[],sort=F.boolean_sort,bits=zeroWord,poly_constants=[],vars=[]})

val (makePolySpassTerm,makePolySpassTermLst) = 
   let fun makeBoth(fvars,variableRenamer,fsymRenamer,printer) = 
     let val st = "st" 
         val (lp,rp,comma) = ("(",")",",")
         fun f(term as Var(v),data as {vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                let val sort = ATV.getSort(v)
                    val (sort_str,{vars=vs',fsyms=fs'}) = F.toPolyString(sort,printer)    
                in
			 let val vname = variableRenamer(ATV.name(v))
                             val (vname',flag) = if Basic.isMemberEq(v,fvars,ATV.nameEq) 
                                                 then ("c"^vname,true) else ("X"^vname,false)
                             val v_str = st^lp^sort_str^comma^vname'^rp
                             val vs'' = vs'@vs 
                             val fs'' = if flag then ((lp^vname'^",0"^rp)::fs')@fs else fs'@fs 
                             val os' = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                           SOME(sorts) => sorts@os
                                         | _ => os)
                 
                         in
                             (v_str,{vars=vs'',fsyms=fs'',fsymbols=fsymbols,osorts=os'})
                         end
                end
           | f(numTerm(an as A.int_num(_)),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                              let val cname = "c"^A.athNumberToString(an)
                                  val sort_str = (atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.int_sort_symbol))))
                                  val term_str = st^lp^sort_str^comma^cname^rp 
                                  val os' = Data.mint_sort_symbol::os
			      in 
                                 (term_str,{vars=vs,fsyms=("("^cname^",0)")::("("^sort_str^",0)")::fs,
                                            fsymbols=(msym(Symbol.symbol cname))::fsymbols,osorts=os'})
                              end
           | f(numTerm(an as A.real_num(r,_)),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                 let val cname = let val (floor,ceil) = (Int.toString(Real.floor(Real.realFloor(r))),Int.toString(Real.ceil(Real.realCeil(r))))
                                   in "c"^floor^"_"^ceil  end
                    val sort_str = (atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.real_sort_symbol))))
                    val term_str = st^lp^sort_str^comma^cname^rp
                    val os' = Data.mreal_sort_symbol::os 
                 in 
                   (term_str,{vars=vs,fsyms=("("^cname^",0)")::("("^sort_str^",0)")::fs,fsymbols=(msym (Symbol.symbol cname))::fsymbols,osorts=os'})
                 end
           | f(ideTerm(x),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
                                           let val cname = "ide_nti_fier_"^(MetaId.name(x))
                                               val sort_str = (atp_sort_prefix)^(Basic.fsymRenamer(Basic.toLower(Symbol.name(Names.ide_sort_symbol))))
                                               val term_str = st^lp^sort_str^comma^cname^rp 
					   in
                               	             (term_str,{vars=vs,fsyms=("("^cname^",0)")::fs,fsymbols=(msym (Symbol.symbol cname))::fsymbols,osorts=os})
					   end
           | f(App({root=f,sort,args as [],...}),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os}) = 
			  let val cname = "c"^(fsymRenamer(MS.name(f)))
                              val (sort_str,{vars=vs',fsyms=fs'}) = F.toPolyString(sort,printer)
                              val c_str = st^lp^sort_str^comma^cname^rp
                              val fs'' = ((lp^cname^",0"^rp)::fs')@fs
                              val vs'' = vs'@vs 
                              val os' = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                            SOME(sorts) => sorts@os
                                           | _ => os)
			      in
                               	(c_str,{vars=vs'',fsyms=fs'',fsymbols=f::fsymbols,osorts=os'})
	       	              end
           | f(App({root=f,sort,args=terms,...}),{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os,...}) = 
		    let val is_eq = MS.modSymEq(f,Names.mequal_logical_symbol)
			val fname = if is_eq then "equal" else "f"^(fsymRenamer(MS.name(f)))
                        val (sort_str,{vars=vs',fsyms=fs'}) = F.toPolyString(sort,printer)				    
                        val os' = (case F.findOutDynamicallyIfASortHasOrderSortedSymbolsInIt'(sort) of
                                      SOME(sorts) => sorts@os
                                    | _ => os)
			val arity = Int.toString(length(terms))
                        val (arg_sorts,_,_,has_pred_based_sorts) = 
                                               let val res = Data.getSignature(f)
                                               in res end
                        val fs_new = toPolyString1Lst(arg_sorts,printer) 
                        val os'' = (case findOutDynamicallyIfASortLstHasOrderSortedSymbolsInIt(arg_sorts) of
                                      SOME(sorts) => sorts@os'
                                    | _ => os')
			val (term_strings,{vars=vs'',fsyms=fs'',fsymbols=fsymbols',osorts=os'''},n) = 
                                  fLst(terms,[],{vars=vs'@vs,fsyms=fs'@fs,fsymbols=fsymbols,osorts=os''},0)
                        val f_str = fname^lp^(Basic.printListStr(term_strings,fn x => x,comma))^rp 
                        val term_str = st^lp^sort_str^comma^f_str^rp
			val fs''' = if is_eq then fs'' 
				      else ("("^fname^","^n^")")::fs''
		     in
			(term_str,{vars=vs'',fsyms=fs_new@fs''',fsymbols=f::fsymbols',osorts=os'''})
		     end
         and
             fLst([],strings,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os},i) = 
                        (rev(strings),{vars=vs,fsyms=fs,osorts=os,fsymbols=fsymbols},Int.toString(i))
           | fLst(t::rest,strings,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os},i) =  
                    let val (str,{vars=vs',fsyms=fs',fsymbols=fsymbols',osorts=os'}) = f(t,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os})
                    in
		      fLst(rest,str::strings,{fsyms=fs',vars=vs',fsymbols=fsymbols',osorts=os'},i+1)
      	            end
     in
        (f,fLst)
     end
    in
       (fn (t,fvars,variableRenamer,fsymRenamer,printer) => let val (f,_) = makeBoth(fvars,variableRenamer,fsymRenamer,printer) 
                                                                val (str,{vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os}) = 
                                                                             f(t,{vars=[],fsyms=[],fsymbols=[],osorts=[]})
                                                                val st_str = "(st,2)"
                                                            in  (str,{vars=vs,fsyms=st_str::fs,fsymbols=fsymbols,osorts=os}) end,
       fn (terms:term list,fvars,variableRenamer,fsymRenamer,printer) => let val (_,f) = makeBoth(fvars,variableRenamer,fsymRenamer,printer) 
                                                                             val (strings,res as {vars=vs,fsyms=fs,fsymbols=fsymbols,osorts=os},_) = 
                                                                                     f(terms,[],{vars=[],fsyms=[],fsymbols=[],osorts=[]},0)
                                                                             val st_str = "(st,2)"
                                                                         in  (strings,{vars=vs,fsyms=st_str::fs,fsymbols=fsymbols,osorts=os}) end)
    end

end (**  of "abstype term with..."  **)

end (** of AthTerm struct **)

