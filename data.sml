(*======================================================================

This structure implements functionality for handling data declarations
(such as sort or datatype definitions, function symbol declarations,
and so on). 

=======================================================================*)

structure Data = 

struct

structure A = AbstractSyntax

structure F = FTerm

structure S = Symbol

structure MS = ModSymbol

structure O = SortOrder

open SortOrder

fun mark(str) = print("\n"^str^"\n")

exception ObTypeCheckFailure

fun illegalSortName(name) = (String.sub(name,0) = Names.sort_variable_prefix_as_char)

exception GenEx of string 

fun genEx(str,pos_opt,file) = raise GenEx(Util.makeErrorMessage(str,pos_opt))

val boolean_sort_symbol = Names.boolean_sort_symbol
val mboolean_sort_symbol = Names.mboolean_sort_symbol
val pos_int_sort_symbol = Names.pos_int_sort_symbol
val neg_int_sort_symbol = Names.neg_int_sort_symbol
val non_neg_int_sort_symbol = Names.non_neg_int_sort_symbol
val int_sort_symbol = Names.int_sort_symbol
val mint_sort_symbol = Names.mint_sort_symbol
val real_sort_symbol = Names.real_sort_symbol
val mreal_sort_symbol = Names.mreal_sort_symbol
val ide_sort_symbol = Names.ide_sort_symbol
val mide_sort_symbol = Names.mide_sort_symbol
val option_structure_symbol = Names.option_structure_symbol
val moption_structure_symbol = Names.moption_structure_symbol

val predefined_sorts =
  [boolean_sort_symbol,int_sort_symbol,real_sort_symbol,ide_sort_symbol,option_structure_symbol]
  
val mpredefined_sorts =
  [mboolean_sort_symbol,mint_sort_symbol,mreal_sort_symbol,mide_sort_symbol,moption_structure_symbol]

fun isPredefinedSort(name) = Basic.isMemberEq(name,predefined_sorts,Symbol.symEq)

fun misPredefinedSort(name) = Basic.isMemberEq(name,mpredefined_sorts,MS.modSymEq)

fun intendedPredefinedSubsorts(name1,name2) =
  (S.symEq(name1,int_sort_symbol) andalso S.symEq(name2,real_sort_symbol))
  
fun mintendedPredefinedSubsorts(name1,name2) =
  (MS.modSymEq(name1,mint_sort_symbol) andalso MS.modSymEq(name2,mreal_sort_symbol))

val num_negation_fun_symbol: S.symbol option ref = ref(NONE)

val boolean_object_type = F.boolean_sort
val boolean_sort = F.boolean_sort

val int_sort = FTerm.int_sort
val real_sort = FTerm.real_sort
val ide_sort = FTerm.ide_sort
val ide_object_type = FTerm.makeMConstant mide_sort_symbol

(*==================================================================================
		Bit fields for function symbols (constructors, declared,
		and defined function symbols):

The lowest bit represents whether the symbol is polymorphic
(i.e., whether its signature contains any sort parameters).

The next highest bit indicates whether or not the signature
of the symbol involves any predicate-based sorts.

==================================================================================*)

val zeroWord:Word8.word = 0w0     
val polyWord:Word8.word = 0w1
val predBasedWord:Word8.word = 0w2
val orWords = Word8.orb

fun isPolyWord(w) = (Word8.andb(w,polyWord) = polyWord)

fun isPredBasedSortWord(w) = (Word8.andb(w,predBasedWord) = predBasedWord)

fun makeWord({poly=true,pred_based_sig=false}) = polyWord 
  | makeWord({poly=true,pred_based_sig=true}) = 0w3 
  | makeWord({poly=false,pred_based_sig=true}) = predBasedWord
  | makeWord({poly=false,pred_based_sig=false}) = zeroWord

type ath_struc_constructor = {name:MS.mod_symbol,
			      arity:int,
			      mother_structure:MS.mod_symbol,
                              reflexive:bool,
			      bits:Word8.word,
			      selectors:MS.mod_symbol option list,
                              argument_types:F.term list,
			      range_type:F.term, 
			      prec:int ref,
                              absyn_argument_types: A.absyn_term list, 
			      assoc:bool option ref,
                              sym_range_type: SymTerm.term}

fun reflexivePositions(c:ath_struc_constructor as
                       {name,arity,mother_structure,absyn_argument_types,...}) = 
      let val pos_lst = ref([])
          val i = ref(1)
      in
         while (!i <= arity) do
           if SymTerm.fsymOccursInTagged(mother_structure,List.nth(absyn_argument_types,!i-1)) then
               pos_lst := !i::(!pos_lst)
              else Basic.inc(i);
           !i
      end
 
type ath_structure = {name:MS.mod_symbol,arity:int,obtype_params:S.symbol list,option_valued_selectors:bool,
                      constructors:ath_struc_constructor list,free:bool}

type declared_fun_sym = {name:MS.mod_symbol,obtype_params:S.symbol list, bits:Word8.word,
                         argument_types:F.term list,
			 range_type:F.term, 
			 prec:int ref,
			 assoc:bool option ref,
                         absyn_argument_types: A.absyn_term list,
			 arity: int, 
                         absyn_range_type:A.absyn_term}


fun liftMSName(name:MS.mod_symbol) = 
      let val (mods,last) = MS.split(name)
          val last' = S.symbol(S.name(last) ^ "^")
      in
          MS.makeModSymbol'(mods,last')
      end				    

fun isFunSort(t:F.fsymbol) = MS.modSymEq(t,Names.fun_name_msym)

fun funSortArity(t) = 
   (case F.isApp(t) of 
       SOME(sort,args) => if not(isFunSort(sort)) then NONE
                          else SOME(length(args)-1)
    |  _ => NONE)

fun makeLiftedRangeType(argument_types:F.term list,range_type: F.term) = 
    F.makeApp(Names.fun_name_msym,argument_types @ [range_type])

fun isLiftedFSym(name:MS.mod_symbol) = 
  let val name_as_string = S.name(MS.lastName(name))
  in 
    (String.sub(name_as_string,String.size(name_as_string)-1) = #"^")
  end 

fun makeLiftedAbsynType(absyn_argument_types:A.absyn_term list, absyn_range_type: A.absyn_term) = 
     SymTerm.makeTaggedApp(Names.fun_name_msym,
			   SymTerm.getTopTag(absyn_range_type),
			   absyn_argument_types @ [absyn_range_type])

fun lift(dfs as {name:MS.mod_symbol,
		 obtype_params:S.symbol list, 
		 bits:Word8.word,
		 argument_types:F.term list,
		 range_type:F.term, 
		 prec:int ref,
		 assoc:bool option ref,
		 absyn_argument_types: A.absyn_term list,
		 arity: int, 
		 absyn_range_type:A.absyn_term}:declared_fun_sym,
	 lifted_ms_name) = 
    let val lifted_version:declared_fun_sym = 
	    {name = lifted_ms_name,
	     obtype_params = obtype_params,
	     bits = bits,
	     argument_types = [],
	     range_type = makeLiftedRangeType(argument_types,range_type),
	     prec = ref(0),
	     assoc = ref(!assoc),
	     absyn_argument_types = [],
	     arity = 0,
	     absyn_range_type = makeLiftedAbsynType(absyn_argument_types,absyn_range_type)}
     in
	 lifted_version
     end
	     	   
fun makeFunSort(proper_args) =  
   let val fresh_arg_sorts = map (fn (_) => FTerm.makeFreshVar()) proper_args
       val res_sort = FTerm.makeFreshVar()
       val fun_sort = FTerm.makeApp(Names.fun_name_msym,fresh_arg_sorts@[res_sort])     
   in
     (fun_sort,fresh_arg_sorts,res_sort)
   end 

type defined_fun_sym = {name:MS.mod_symbol,argument_types:F.term list,range_type:F.term,bits:Word8.word,arity:int,
                        prec:int ref,assoc:bool option ref}

(*** The main datatype for Athena function symbols: ***)

datatype ath_fun_sym = declared of declared_fun_sym 
		     | defined of defined_fun_sym 
		     | struc_con of ath_struc_constructor

fun hashAthFunSym(declared({name,...})) = Basic.hashInt(MS.code(name))
  | hashAthFunSym(defined({name,...})) = Basic.hashInt(MS.code(name))
  | hashAthFunSym(struc_con({name,...})) = Basic.hashInt(MS.code(name))

fun switchNames(new_name,declared({name,obtype_params,bits,argument_types,range_type,prec,assoc,absyn_argument_types,arity,absyn_range_type})) = 
          declared({name=new_name,obtype_params=obtype_params,bits=bits,argument_types=argument_types,range_type=range_type,
                    prec=prec,assoc=assoc,absyn_argument_types=absyn_argument_types,arity=arity,absyn_range_type=absyn_range_type})
  | switchNames(new_name,defined({name,argument_types,range_type,bits,arity,prec,assoc})) = 
                  defined({name=new_name,argument_types=argument_types,range_type=range_type,bits=bits,arity=arity,prec=prec,assoc=assoc})
  | switchNames(_,f) = f

fun fsymName(declared({name,...})) = name
  | fsymName(struc_con({name,...})) = name
  | fsymName(defined({name,...})) = name

fun fsymArity(declared({arity,...})) = arity
  | fsymArity(struc_con({arity,...})) = arity
  | fsymArity(defined({arity,...})) = arity
         
fun fsymPrec(declared({prec,...})) = prec
  | fsymPrec(struc_con({prec,...})) = prec
  | fsymPrec(defined({prec,...})) = prec

fun fsymAssoc(declared({assoc,...})) = assoc 
  | fsymAssoc(struc_con({assoc,...})) = assoc
  | fsymAssoc(defined({assoc,...})) = assoc

val structure_table: ath_structure MS.htable = MS.makeHTable()

val structure_sequential_code = ref(0)

val structure_sequential_code_table: int MS.htable = MS.makeHTable()

fun getAllStructures() =  MS.listItems structure_table

val constructor_table: ath_struc_constructor MS.htable = MS.makeHTable()

val selector_table: {is_polymorphic:bool} MS.htable = MS.makeHTableWithInitialSize(29)

fun isSelector(msym) = (case MS.find(selector_table,msym) of
                           SOME(_) => true
                         | _ => false)

fun isPolySelector(msym) = (case MS.find(selector_table,msym) of
                              SOME({is_polymorphic}) => is_polymorphic
                         | _ => false)

val fsym_table: ath_fun_sym MS.htable = MS.makeHTable()

val structure_and_domain_arities: int MS.mapping ref = ref(MS.empty_mapping)

fun sortConstructorArity(sc_name) = MS.lookUp(!structure_and_domain_arities,sc_name)

val sort_abbreviations: SymTerm.term MS.htable = MS.makeHTable()

fun addStructure(s as {name,...}:ath_structure) = (MS.insert(structure_table,name,s);
                                                   MS.insert(structure_sequential_code_table,name,Basic.returnAndInc(structure_sequential_code)))

fun getSequentialStructureCode(struc_name) = 
    (case MS.find(structure_sequential_code_table,struc_name) of
        SOME(i) => i
      | _ => ~1)

fun deleteStructure(s as {name,...}:ath_structure) = MS.removeHT(structure_table,name)

fun addDomain(s as {name,...}:ath_domain) = MS.insert(sort_table,name,s)

fun addConstructor(c as {name,...}:ath_struc_constructor) = MS.insert(constructor_table,name,c)

fun allFSyms() = MS.listItems(fsym_table)

fun allFSymsAsStrings() = let val res:string list = (map (fn x => MS.name(fsymName(x))) 
                                                         (MS.listItems(fsym_table)))
                          in res end

val max_prime_suffix = ref(0)

fun updateMaxSuffix(msym) =  
      let val str = S.name(MS.lastName(msym))
          val len = String.size(str)
          fun loop(i,count) = if (i >= 0) andalso String.sub(str,i) = Names.standardEvalProcNameTailCharacter then loop(i-1,count+1) else count
          val count = loop(len-1,0)
      in
        if count > !max_prime_suffix then max_prime_suffix := count else ()
      end


(** 
If f: [S_1 ... S_n] -> S, then add f^:(Fun S_1 ... S_n S)
**)

fun addFSym(f as declared(dfs as {name,...})) = 
    let val lifted_name = liftMSName(name)
        val lifted_version = declared(lift(dfs,lifted_name))
        val _ = 	(updateMaxSuffix(name);
			 MS.insert(fsym_table,name,f);
			 MS.insert(fsym_table,lifted_name,lifted_version))
    in
       (lifted_name,lifted_version)
    end 
  | addFSym(f as defined({name,...})) = 
      let val _ = (updateMaxSuffix(name);
		   MS.insert(fsym_table,name,f))
      in
	  (name,f)
      end
  | addFSym(f as struc_con({name,...})) = 
    let val _ = (updateMaxSuffix(name);
		 MS.insert(fsym_table,name,f))
    in
       (name,f)
    end


fun findStructure(sym) = MS.find(structure_table,sym)

fun isStructure(sym) = (case findStructure(sym) of 
                           NONE => false
                         | _ => true)

fun isNonFreeDT(sym) = (case findStructure(sym) of 
                            NONE => false
                          | SOME({free,...}) => not(free))
 
fun findDomain(sym) = MS.find(sort_table,sym)

fun isSort(sym) = (case MS.find(sort_table,sym) of
                      NONE => false | _ => true)

fun isAnySort(sym) = isStructure(sym) orelse isSort(sym)

fun isAnySortFlexible(sym) = isAnySort(sym) orelse  
                               (case MS.lookUp(!structure_and_domain_arities,sym) of
                                   SOME(_) => true
                                 | _ => false)

fun findConstructor(sym) = MS.find(constructor_table,sym)

fun isFreeStructure(struc_name) = 
             (case findStructure(struc_name) of 
                 SOME(ath_struc as {free,...}) => free
               | _ => false)

fun isFreeStructureConstructor(name) = 
      (case MS.find(constructor_table,name) of
          NONE => false
        | SOME(x:ath_struc_constructor as {mother_structure,...}) => (case findStructure(mother_structure) of
                                                                         SOME({free,...}) => free
                                                                       | _ => false))

fun hasOptionValuedSelectors(struc_name) = 
             (case findStructure(struc_name) of 
                 SOME(ath_struc as {option_valued_selectors,...}) => option_valued_selectors
               | _ => false)

fun isConstantStructureConstructor(name) = 
    (case MS.find(constructor_table,name) of
          SOME({arity,...}) => 
             if arity = 0 then true else false
        | _ => false)

fun isConstantFSymConstructor(name) = 
    (case MS.find(fsym_table,name) of
          SOME(declared({argument_types,...})) => 
             if length(argument_types) = 0 then true else false
        | SOME(defined({argument_types,...})) =>
             if length(argument_types) = 0 then true else false
        | _ => false)

fun isConstantTermConstructor(name) = 
      if not(A.parseNumberKind(MS.name(name)) = 0) then
         true 
      else
         (isConstantStructureConstructor(name) orelse isConstantFSymConstructor(name))

fun isNonConstantStructureConstructor(name) = 
    (case MS.find(constructor_table,name) of
          SOME({arity,...}) => 
             if arity > 0 then true else false
        | _ => false)

fun getWord(name) = 
     (case MS.find(constructor_table,name) of
         SOME({bits,...}) => bits
       | _ => (case MS.find(fsym_table,name) of
                  SOME(declared({bits,...})) => bits
                | SOME(defined({bits,...})) => bits
                | _ => genEx("Symbol not found: "^MS.name(name),NONE,"")))

fun isUnaryFunSym(sym_name) = 
     (case MS.find(fsym_table,sym_name) of
                  SOME(declared({argument_types,range_type,...})) => 
                       (case argument_types of
                           [arg_type] => SOME(arg_type,range_type)
                         | _ => NONE)
                | SOME(defined({argument_types,range_type,...})) => 
                       (case argument_types of
                           [arg_type] => SOME(arg_type,range_type)
                         | _ => NONE)
                | _ => NONE)

fun isStructureConstructorAsMS(con_name) = 
     (case MS.find(constructor_table,con_name) of
         SOME({mother_structure,...}) => SOME(mother_structure)
       | _ => NONE)

fun isStructureConstructorBool(name) = 
      (case MS.find(constructor_table,name) of
          NONE => false
        | _ => true)

fun isStructureConstructorOpt(con_name) = MS.find(constructor_table,con_name)

fun areConstructorsOfSameStructure(name1,name2) = 
      (case (isStructureConstructorAsMS(name1),isStructureConstructorAsMS(name2)) of
          (SOME(sname1),SOME(sname2)) => MS.modSymEq(sname1,sname2)
        | _ => false)

fun isNonConstantFSymConstructor(name) = 
    (case MS.find(fsym_table,name) of
          SOME(declared({argument_types,...})) => 
             if length(argument_types) > 0 then true else false
        | SOME(defined({argument_types,...})) => 
             if length(argument_types) > 0 then true else false
        | _ => false)

fun isNonConstantTermConstructor(name) = 
    isNonConstantStructureConstructor(name) orelse isNonConstantFSymConstructor(name)

fun isTermConstructor(name) = 
     (case MS.find(constructor_table,name) of
         SOME({arity,...}) => SOME(arity)
       | _ => (case MS.find(fsym_table,name) of
                  SOME(declared({argument_types,...})) => SOME(length(argument_types))
                | SOME(defined({argument_types,...})) => SOME(length(argument_types))
                | _ => NONE))

fun isTermConstructorAsFSymOption(name) = MS.find(fsym_table,name)

(** Look at the constructor_table first: **)

fun isTermConstructorAsFSymOptionGeneral(name) = 
     (case MS.find(constructor_table,name) of
         SOME(c) => SOME(struc_con(c))
       | _ => MS.find(fsym_table,name))

fun isTermConstructorBool(name) = (case isTermConstructor(name) of NONE => false | _ => true)

fun hasBooleanRangeType(name) = 
     let fun checkFTerm(t) =
              (case FTerm.isConstant(t) of
                  SOME(fsym) => MS.modSymEq(fsym,mboolean_sort_symbol)
                | _ => false)
     in
        (case MS.find(constructor_table,name) of
              SOME({range_type,...}) => checkFTerm(range_type)
       | _ => (case MS.find(fsym_table,name) of
                  SOME(declared({range_type,...})) => checkFTerm(range_type)
                | SOME(defined({range_type,...})) => checkFTerm(range_type)
                | _ => false))
     end

fun isLogicalSymbol(name) = A.isPropCon(name)

fun getObType(f) = 
    case MS.find(constructor_table,f) of
       SOME({argument_types,bits,range_type,...}:ath_struc_constructor) =>
             ((argument_types,range_type),bits)
     | _ => (case MS.find(fsym_table,f) of
                SOME(declared({argument_types,range_type,bits,...})) =>
                      ((argument_types,range_type),bits)
              | SOME(defined({argument_types,range_type,bits,...})) =>
                      ((argument_types,range_type),bits)
              | _ => (let val n = A.parseNumberKind(MS.name(f))
		      in
			  (if n = 1 then (([],int_sort),zeroWord) else 
			   if n = 2 then (([],real_sort),zeroWord)
			   else let val real_fail_message = "\nCannot find a signature for "^(MS.name(f))
                                in 
                                   Basic.fail("")
                                end)
		      end))

val (getSignature,removeMemoizedSignature) = 
   let val ht: (FTerm.term list * FTerm.term * bool * bool) MS.htable = MS.makeHTableWithInitialSize(79)
   in
    ((fn fsym => 
         (case MS.find(ht,fsym) of
             SOME(res as (sorts,sort,is_poly,involves_pred_based_sorts)) => 
                                              if is_poly then 
                                                 let val sorts' = F.renameLst(sort::sorts)
                                                 in 
                                                   (tl sorts',hd sorts',is_poly,involves_pred_based_sorts)
                                                 end
                                              else res
           | _ => let val ((arg_sorts,result_sort),bits) = getObType(fsym) 
                      val is_poly = isPolyWord(bits)
                      val involves_pred_based_sorts = isPredBasedSortWord(bits)
                      val (arg_sorts,result_sort) = if is_poly then 
                                                       let val  all_sorts = F.renameLst(result_sort::arg_sorts)
                                                       in
                                                         (tl all_sorts,hd all_sorts)
                                                       end
                                                    else (arg_sorts,result_sort)
                      val res = (arg_sorts,result_sort,is_poly,involves_pred_based_sorts)
                      val _ = MS.insert(ht,fsym,res)
                  in
                    res
                  end)),
     (fn fsym => ((MS.removeHT(ht,fsym);()) handle _ => ())))
   end

fun deleteFSym(fsym_name) = (removeMemoizedSignature(fsym_name);MS.removeHT(fsym_table,fsym_name))

fun deleteConstructor(c as {name,...}:ath_struc_constructor) = 
             (removeMemoizedSignature(name);MS.removeHT(constructor_table,name))

fun removeFSym(f as declared({name,...})) = (removeMemoizedSignature(name);MS.removeHT(fsym_table,name))
  | removeFSym(f as defined({name,...})) = (removeMemoizedSignature(name);MS.removeHT(fsym_table,name))
  | removeFSym(f as struc_con({name,...})) = (removeMemoizedSignature(name);MS.removeHT(fsym_table,name))

fun removeFSymByName(name) = 
    (case MS.find(fsym_table,name) of
          SOME(f) => (removeFSym(f);())
        | _ => ())

val isPolySymbol =
   let val ht: bool MS.htable = MS.makeHTableWithInitialSize(79)
   in
    (fn fsym => 
       (case MS.find(ht,fsym) of
           SOME(res) => res
         | _ => let val res = isPolyWord(#2(getObType(fsym)))
                    val _ = MS.insert(ht,fsym,res)
                in
                   res
                end))
   end

val reference_array = Array.array(10,ide_sort_symbol)

(* This table maps a string representing a monomorphic sort, like "Person" or "(List-Of Int)" to a set
of function symbols that act as constructors for the sort, when the latter is approximated by a datatype
for model-finding purposes. *)

fun clearSignature() = 
   (MS.clearHTable(sort_table);
    MS.clearHTable(structure_table);
    MS.clearHTable(constructor_table);
    MS.clearHTable(selector_table);
    MS.clearHTable(fsym_table);
    structure_and_domain_arities := MS.empty_mapping;
    MS.clearHTable(sort_abbreviations);
    sort_index := 0;
    domain_max := sort_increment;
    global_sort_matrix := makeSortMatrix(!domain_max);
    order_sorted_array := Array.array((!domain_max)+1,false))

val domains_as_datatypes_table: (string,ath_fun_sym list) HashTable.hash_table = HashTable.mkTable(Basic.hashString, op=) (15,Basic.Never)
     
end
