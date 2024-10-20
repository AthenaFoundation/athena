signature PROP = 
sig

   type variable

   type term

(* prop is the type of sentences in Athena *)

   type prop

   type sort

(*
   A function to convert a sentence into a string that takes as additional input
   a procedure that can convert sort variables into strings.
*)   
   val toString: prop * (FTerm.variable -> string) -> string

(* This is the default way to convert a sentence to a string: *)
   val toStringDefault: prop  -> string

   val toStringWithVarSortsAsTheyAre: prop -> string

   val display: prop -> unit
 
   val toPrettyString: int * prop * (FTerm.variable -> string) -> string 

   val toPrettyStringDefault: int * prop  -> string 

(* Alphabetic equivalence for Athena sentences - a fundamental relation: *)
   val alEq: prop * prop -> bool 

(* Literal equality (unlike alpha equality): *)
   val literalEq: prop * prop -> bool 

(* Return all the atomic sentences that occur in the input sentence: *)
   val allAtoms: prop -> term list

   val freeVars: prop -> variable list 
   val boundVars: prop -> variable list 

   val freeVarsSet: prop -> AthTermVar.var_set
   val freeVarsSetLst: prop list -> AthTermVar.var_set

   val freeVarsLst: prop list -> variable list 

   val occursFree: variable * prop -> bool

(* Given a variable x:S and sentence p, occursFreeUpToSubsorting checks to see 
   whether p contains free occurrences of any variable of the form x:T, where S 
   is an instance of T. This is thus much more general than occursFree. 
*)
   val occursFreeUpToSubsorting: variable * prop -> bool
   
   val subterms: prop -> term list

   val applySortSub: FTerm.sub * prop -> prop 

   val applySortSubLst: FTerm.sub * prop list -> prop list 

   val applyExtractedSortSub: (prop  * term) -> prop option

   val sortVars: prop -> FTerm.variable list
   
   val makeMonomorphicInstance: prop -> prop

   val true_prop: prop
   val false_prop: prop 

   val makeAtom: term -> prop 
   val makeAtomOpt: term -> prop option

   val makeNegation: prop -> prop
   val makeComplement: prop -> prop

   val makeConjunction: prop list -> prop
   val makeDisjunction: prop list -> prop
   val makeConditional: prop * prop -> prop
   val makeBiConditional: prop * prop -> prop
   val makeUGen: variable list * prop -> prop
   val makeEGen: variable list * prop -> prop
   val makeEGenUnique: variable list * prop -> prop

   val close: prop -> prop 

   val isPoly: prop -> bool

   val isZeroHeightProp: prop -> bool

   val hasFreeVars: prop -> bool
   
   val hasBoundVars: prop -> bool

   val getCode: prop -> int option ref 

   val setCode: prop * int -> unit 

   val compare: prop * prop -> order 

   val isAtom: prop -> term option 
   val isNeg: prop -> prop option 
   val isConj: prop -> (prop list option)
   val isDisj: prop -> (prop list option)
   val getDisjuncts: prop -> prop list 
   val getDisjunctsWithoutDups: prop -> prop list 
   val isCond: prop -> ((prop * prop) option)
   val isBiCond: prop -> ((prop * prop) option)
   val isUGen: prop-> ((variable * prop) option)
   val isEGen: prop-> ((variable * prop) option)
   val isEGenUnique: prop-> ((variable * prop) option)
   val isQuant: prop -> (AbstractSyntax.prop_con * variable * prop) option 
   val isCompound: prop -> (AbstractSyntax.prop_con * prop list) option 
   val isBoolCompound: prop -> (AbstractSyntax.prop_con * prop list) option 
   val isBooleanConstant: prop -> string 
   val isBooleanFalse: prop -> bool
   val isBooleanTrue: prop -> bool

   val isVarAtom: prop -> bool

   val replace: variable * term * prop -> prop
   val replaceVarByVar: variable * variable * prop -> prop
   val replaceFSymsByFsyms: prop * (ModSymbol.mod_symbol ModSymbol.mapping)  -> prop 
   val replaceLst: variable list * term list * prop -> prop
   val  replaceVarByTermOfSomeSubSort: variable * term * prop * FTerm.sub -> prop

   val renameQProp: string list * prop -> prop 

   val alphaRename: prop -> prop

   val getMaxHashLength: unit -> int
   val setMaxHashLength: int -> unit 
   val hash: prop -> Word.word 
   val fastHash: prop -> Word.word 

   val makeFalseProp: unit -> prop
   val makeTrueProp: unit -> prop
   val dedup: prop list -> prop list 

   val makeEquality: term * term -> prop 
   val isEquality: prop -> (term * term) option 
   val isRefEquality: prop -> bool
   val swapEquality: prop -> prop
   val leaves: prop -> term list
   val applySub: AthTerm.sub * prop -> prop 

   val propKind: prop -> string 
  
   val splitVars: prop -> (AbstractSyntax.prop_con option * variable list * prop)

   val decomposeConjunctions: prop -> prop list
   val decomposeConjunctionsStrict: prop -> prop list

   val getConjuncts: prop -> prop list
   val getConjunctsOnly: prop -> prop list
   val getConjunctsLst: prop list -> prop list

   val foldConditionals: prop list * prop -> prop
   
   val match: prop * prop -> AthTerm.sub option 
   val matchLst: prop list * prop list -> AthTerm.sub option 

   val matchRWraw: prop * prop * AthTerm.sub * FTerm.sub * variable list  -> (AthTerm.sub * FTerm.sub) option
   val matchLstRWraw: prop list * prop list * AthTerm.sub * FTerm.sub * variable list  -> (AthTerm.sub * FTerm.sub) option

   val matchRW: prop * prop * variable list -> AthTerm.sub option
   val matchLstRW: prop list * prop list * variable list -> AthTerm.sub option

   val isSortInstance: prop * prop -> FTerm.sub option 

   val unify: prop * prop -> AthTerm.sub option 

   val makeSpassUgen: string list * string * string -> string 
   val makeSpassPropList: prop list * (string -> string) -> string * string * string list 

   val makePolySpassProp: prop * (string -> string) * (string -> string) -> string * string list * ModSymbol.mod_symbol list * string list * string list * ModSymbol.mod_symbol list  
   val makePolySpassPropList: prop list -> (string * string list * ModSymbol.mod_symbol list) * (string * string list) * string list * ModSymbol.mod_symbol list 

   val makePolyProp: prop * (string -> string) * (string -> string) * string -> string * string list * ModSymbol.mod_symbol list * string list * string list * ModSymbol.mod_symbol list  

   val makePolyPropList: prop list * string * (string -> string) -> (string * string list * ModSymbol.mod_symbol list) * (string * string list) * string list * ModSymbol.mod_symbol list 

(* satSolveTableau is a simple tableau-based propositional sat solver. If the input sentences are satisfiable, the result
   is SOME(L) where L is list of literals representing a satisfying interpretation; otherwise NONE is returned. *)
   
   val satSolveTableau: prop list -> prop list option
   
(* satSolvableTableau uses a similar technique but only returns a yes/no answer. *)
   val satSolvableTableau: prop list -> bool option 

   val size: prop -> int 
   val sizeLst: prop list -> int 

   val makeTPTPProp: prop -> string 
   val makeTPTPPropList: prop list -> string list 
   val makePolyTPTPProp: prop -> string 
   val makeTSTPProp: prop -> string 
   val makeTSTPPropFast: prop -> CharArray.array * int 
   val translateAthenaProp: prop -> Sat.prop 

   val makeSubsortAxioms: ModSymbol.mod_symbol list * ModSymbol.mod_symbol list * variable list * string -> string list 

   val writeSMT: prop * {domain_stream:TextIO.outstream, 
                         dec_stream: TextIO.outstream,
                         main_stream: TextIO.outstream, 
			 var_table: variable AthTermVar.htable,
			 sel_counter:int ref,
                         fsym_table: bool ModSymbol.htable, 
			 domain_table: bool ModSymbol.htable,
			 poly_to_mono_sort_table: (string,(sort list * sort)) HashTable.hash_table} -> unit 

   val writeCVC: prop * {domain_stream:TextIO.outstream, dec_stream: TextIO.outstream,
                         main_stream: TextIO.outstream, sel_counter:int ref,fsym_counter:int ref,dom_counter:int ref,var_counter: int ref, 
                         var_table: string AthTermVar.htable,inverse_var_table: (string,variable) HashTable.hash_table, 
                         fsym_table: string ModSymbol.htable, inverse_fsym_table: (string,ModSymbol.mod_symbol) HashTable.hash_table, 
                         domain_table: (string,string) HashTable.hash_table,inverse_domain_table: (string,string) HashTable.hash_table} -> unit

   val writeSMTLst: prop list * 
                    string list *  (*** These are the weights of the props. If not a Max-Sat problem, pass [] as the value ***)
                    {domain_stream:TextIO.outstream, 
                     dec_stream: TextIO.outstream,
		     main_stream: TextIO.outstream, 
                     var_table: variable AthTermVar.htable,
                     sel_counter:int ref,
                     fsym_table: bool ModSymbol.htable,
                     domain_table: bool ModSymbol.htable,
                     poly_to_mono_sort_table: (string,(sort list * sort)) HashTable.hash_table} -> unit

   val writeSMTDefs: (term * prop) list * string * string -> unit 

(* 
In the table below, "obsolete axioms" are axioms whose constructive content has been captured 
by different equations in the defining_equations list, and therefore can be considered as 
extra noise for many practical purposes. It is important to have an easy way of identifying
such axioms, hence the obsolete list. An example: if the user asserts as an axiom for a 
list membership operator "in" the sentence "~ x in nil", the "defining axiom" extracted
from this will be "x in nil = false", and hence the original can be disregarded for many
purposes (e.g., for model building).
*)

   val fsym_def_table: {eval_proc_name:string, 
                        eval_proc_name_with_full_mod_path:string,
                        evaluator_being_defined:bool ref, 
                        guard_syms: ModSymbol.mod_symbol list, 
                        code: string ref,
			red_code: string ref,
                        dcode: string ref,
			needed_by: ModSymbol.mod_symbol list, 
			obsolete_axioms: prop list,
                        occurring_syms: ModSymbol.mod_symbol list, 
			defining_equations: prop list,
			defining_equations_finished: bool ref,
			bicond_sources: (prop * prop) list} ModSymbol.htable

   val proc_name_table: (string,ModSymbol.mod_symbol) HashTable.hash_table

   val module_ab_table: (string,((prop,string option) HashTable.hash_table)) HashTable.hash_table

   val renameSortVarsAux: prop * FTerm.sub -> prop * FTerm.sub 
   val renameSortVarsAuxLst: prop list * FTerm.sub -> prop list * FTerm.sub 
   val renameSortVars: prop -> prop
   val renameSortVarsLst: prop list -> prop list

   val addToModuleAb: Symbol.symbol list * prop * string option -> unit
   val removeFromModuleAb: Symbol.symbol list * prop -> unit
   val removeFromAllModuleAbs: prop -> unit

   exception HT		       
   val isEvalProcName: string -> ModSymbol.mod_symbol option

   val structure_equality_table: (term * term -> prop) ModSymbol.htable
   val tc: ModSymbol.mod_symbol -> ModSymbol.set
   val tc': ModSymbol.mod_symbol -> ModSymbol.set

   val fastSat: prop list * ((AthTerm.term * bool) -> bool) -> (AthTerm.term * bool) list option 
   val sort_predicate_table: (ModSymbol.mod_symbol, ModSymbol.mod_symbol * (AthTerm.term list -> prop)) HashTable.hash_table 

   val evalCanonical: term * prop -> bool 

   val funSymbols: prop -> ModSymbol.mod_symbol list
   val funSymbolsLst: prop list -> ModSymbol.mod_symbol list
   val predSymbols: prop -> (ModSymbol.mod_symbol * int) list
   val predSymbolsLst: prop list -> (ModSymbol.mod_symbol * int) list

(** Negation normal form: **)
   val nnf: prop -> prop
   
   type cnf_array_entry

   type clause = int list
   type clauses = clause list

   type cnf_conversion_result = {clauses: clauses,
                                 table: (int,prop) HashTable.hash_table,
                                 total_var_num: int,
				 tseitin_var_num: int,
				 clause_num: int,
				 array_n: int,
				 cnf_conversion_time: real}


    val cnf: prop -> cnf_conversion_result

    val cnfLst: prop list -> cnf_conversion_result

(*
The makeDimacsFile function takes a cnf_conversion_result and 
writes a dimacs CNF file with that content, where the file 
is specified as a string:
*)

   val makeDimacsFile: cnf_conversion_result * string -> unit

   val propSat: prop list * (('a,'b) HashTable.hash_table)  * (prop -> 'a) * (bool -> 'b) 
        		  -> {assignment: ('a,'b) HashTable.hash_table option,
			      total_var_num: int,
			      tseitin_var_num: int,
			      clause_num: int,
			      cnf_conversion_time: real,
			      dimacs_file_prep_time: real,
			      sat_solving_time:real}

end

