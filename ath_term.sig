(*======================================================================

The API of Athena terms. Some fundamental functionality (e.g., term unification)
is specified in this file. 

=======================================================================*)

signature ATHENA_TERM = 
sig

   type variable

   type fsymbol

   type term

   type sort

   val toStringDefault: term -> string
   
   val toString: term * (FTerm.variable -> string) -> string 

   val termSymbols: term -> fsymbol list 
   val termSymbolsLst: term list -> fsymbol list
   val termSymbolsFastAux: term * (fsymbol,fsymbol) HashTable.hash_table -> unit         
   val termSymbolsFast: term  -> fsymbol list
   val termSymbolsLstFast: term list  -> fsymbol list    

   val dom: term -> int list list 
   val subterm: term * int list -> term 
   val posReplace: term * int list * term -> term 

   val toJson: term -> JSON.value 						 

   val hasTaggedSortVars: term -> bool

   val subterms: term * (term,bool) HashTable.hash_table -> unit
   val subtermsDefault: term  -> term list 
     
   val toPrettyString: int * term * (FTerm.variable -> string) -> string 
   val toPrettyStringDefault: int * term  -> string 

   val display: term -> unit 

   val varEq: variable * variable -> bool  (* Equality predicate on variables *)

   val fsymEq: fsymbol * fsymbol -> bool   (* Equality predicate on function symbols *)

   val termEq: term * term -> bool         (* Equality predicate on terms *)

   (* Equality predicate with strict sort equality for polymorphic constants: *)
   val termEqWithPolyConstants: term * term -> bool

   val getSort: term -> sort

   (*
      isSortInstance takes two Athena terms and returns a substitution option, depending on whether or not
      the first term is a sort instance of the second. If the result is SOME(theta), then theta is the 
      substitution that supports the instance relation. isSortInstanceAux is a more basic function that
      is used to implement isSortInstance. It's exported because it may be useful in other contexts
      (e.g., it's used in prop.sml).
   *)
   
   val isSortInstanceAux: term * term * (sort list * sort list) -> (sort list * sort list)
   val isSortInstance: term * term -> FTerm.sub option

   val sortOfVarInTerm: variable * term -> sort option 

   val getSortSub: term * term -> FTerm.sub option
   val getSortSubForFirstTerm: term list * term -> FTerm.sub option

   val applySortSub: FTerm.sub * term -> term
   val applySortSubLst: FTerm.sub * term list -> term list 

   val makeVar: variable -> term

   val makeConstant: fsymbol -> term

   val makeSortedConstantAux: fsymbol * sort * bool -> term
   
   val makeSortedConstant: fsymbol * sort -> term

   val makeNumTerm: AbstractSyntax.ath_number -> term

   val makeNumConstant: AbstractSyntax.ath_number -> term

   val makeIdeConstant: string -> term

   val leaves: term -> term list 

   val makeApp: fsymbol * term list -> term
   (** A few custom versions of makeApp for convenience: ***)   
   val makeAppUnary: fsymbol * term -> term
   val makeAppBinary: fsymbol * term * term -> term   
   val makeNumApp: fsymbol * term list -> term
   val doUnaryMinusOnLiteral: term * bool -> term
   
   val makeInternalAppTerm: fsymbol * term list * Word.word * sort * Word8.word * (fsymbol * sort) list * variable list -> term 
   val makeAppAndReturnSortSub: fsymbol * term list -> (term * FTerm.sub)
   val getBits:term -> Word8.word
   val makeEquality: term * term -> term 

   val isPoly: term -> bool

   val hasVars: term -> bool
   val involvesPredBasedSorts: term -> bool

   val renameSortVarsAux: term * FTerm.sub -> term * FTerm.sub 
   val renameSortVarsAuxLst: term list * FTerm.sub -> term list * FTerm.sub 

   val renameSortVars: term -> term 
   val renameSortVarsLst: term list -> term list 
   val sortVars: term -> FTerm.variable list 
   val makeMonomorphicInstance: term -> term

   val isVar: term -> bool   
   val isVarOpt: term -> variable option
   
   val isConstant: term -> fsymbol option

   val isNumConstantOpt: term -> AbstractSyntax.ath_number option 
   val isNumConstant: term -> bool 

   val getNumVal: term -> (AbstractSyntax.ath_number * bool) option 

   val isIdeConstant: term -> string option

   val isGeneralConstant: term -> bool

   val isApp: term -> (fsymbol * term list) option

   val isGround: term -> bool

   val areGround: term list -> bool

   val varOccursIn: variable * term -> bool

   val compare: term * term -> order

   val fsymOccursIn: fsymbol * term -> bool

   val getVars: term -> variable list
   val getVarsInOrder: term -> variable list
   val getVarsInOrderLst: term list -> variable list

   val isCanonical: term -> bool 

   val getPolyConstants: term -> (fsymbol * sort) list 

   val getVarsAndHeights: term -> (variable * int list) list 

   val makeVarHeightMap: term * variable list -> ((variable,int) GMap.map)

   val getVarsLst: term list -> variable list

   val replace: variable * term * term -> term

   val replaceFSymsByFsyms:  term * (ModSymbol.mod_symbol ModSymbol.mapping)  -> term

   val distance: term * term -> real

   val weedOutDups: variable list -> variable list 

(* The call replace(v,t1,t2) replaces every occurence of the *)
(* variable v in t2 by the term t1. So it should be read as  *)
(* "Replace v by t1 in t2."                                  *)

   type sub

   val empty_sub: sub
 
   val isEmptySub: sub -> bool 

   val incSub: sub * (variable * term) -> sub
   val incSubAndReturnSubAndSuccessFlag: sub * (variable * term) -> sub * bool 

   val extendSub: sub * (variable * term) list -> sub

   val makeSub: (variable * term) list -> sub

   val nameInSupp: variable * sub -> bool

   val inSupp: variable * sub -> bool

   val supp: sub -> variable list

   val rangeVars: sub -> variable list

   val subEq: sub * sub -> bool

   val applySub: sub * term -> term

   val applySubLst: sub * term list -> term list


   val subToString: sub -> string

   val composeSubs: sub * sub -> sub
 
   val match: term * term -> sub option

   val matchLst: term list * term list -> sub option

   val matchRWraw: term * term * sub * FTerm.sub * variable list -> (sub * FTerm.sub) option
   val matchLstRWraw: term list * term list * sub * FTerm.sub * variable list -> (sub * FTerm.sub) option

   val matchRWrawWithBanned: term * term * sub * FTerm.sub * variable list * 
   variable list -> (sub * FTerm.sub) option

   val matchLstRWrawWithBanned: term list * term list * sub * FTerm.sub * 
   variable list * variable list -> (sub * FTerm.sub) option

   val matchRW: term * term * variable list -> sub option

   val matchLstRW: term list * term list * variable list -> sub option

   val specialMatch: term * term -> (bool * (variable list))

   val matches: term * term -> bool

   val variants: term * term -> bool

   val height: term -> int 

   val sizeCumulative: term * int -> int 
   val size: term -> int 
   val sizeLst: term list -> int 

   val unifyEx: term * term -> sub

   val unifyExLst: term list * term list -> sub

   val unify: term * term -> sub option 

   val unifyLst: term list * term list -> sub option 

(** unifyRW and unifyLstRW below take an extra third argument, a list of variables. 
These variables are treated as constants and cannot appear in the support of
the resulting substitution. This is useful for the proper handling of free 
sentence variables. **)

   val unifyRW: term * term * variable list -> sub option 

   val unifyLstRW: term list * term list * variable list -> sub option 

   val hash: term * Word.word * int * int * (string AthTermVar.mapping) -> Word.word * int 

   val hashTerm: term -> Word.word 

   val fastHash: term -> Word.word 

   val getChildren: term -> term list

   val getConstantChildren: term -> term list

   val sortNameSMT: sort -> string

   val writeSMT: term * {domain_stream:TextIO.outstream, 
                         dec_stream: TextIO.outstream,
                         main_stream: TextIO.outstream, 
			 var_table: variable AthTermVar.htable,
			 sel_counter:int ref,
                         fsym_table: bool ModSymbol.htable, 
			 domain_table: bool ModSymbol.htable, 
			 poly_to_mono_sort_table: (string,(sort list * sort)) HashTable.hash_table} -> (ModSymbol.mod_symbol * string) list 

   val writeCVC: term * {domain_stream:TextIO.outstream, dec_stream: TextIO.outstream,
                         main_stream: TextIO.outstream, var_table: string AthTermVar.htable,inverse_var_table: (string,variable) HashTable.hash_table, 
                         sel_counter:int ref,dom_counter:int ref, fsym_counter:int ref,var_counter: int ref, 
                         fsym_table: string ModSymbol.htable, inverse_fsym_table: (string,ModSymbol.mod_symbol) HashTable.hash_table, 
                         domain_table: (string,string) HashTable.hash_table,inverse_domain_table: (string,string) HashTable.hash_table} -> (string * string) list 

   val replaceVarByVar: variable * variable * term -> term 

   val true_term: term
   val false_term: term
   val isTrueTerm: term -> bool
   val isFalseTerm: term -> bool

   val makeConservativeName: string -> string
   val makeTPTPTerm: term * (variable list) -> string
   val makePolyTPTPTerm: term * (variable list) * (FTerm.variable -> string) * string list -> string * string list 
   val makePolyTPTPTermLst: term list * (variable list) * (FTerm.variable -> string) * string list -> string list * string list 
   val makeTSTPTerm: term * (variable list) * bool -> string
   val makeTSTPTermFast: term * (variable list) * bool * CharArray.array * int -> int 

   val makeSpassTerm: term * (variable list) * (string -> string) * (string -> string) * (string,string) HashTable.hash_table -> string

   val makePolySpassTerm: term * (variable list) * (string -> string) * (string -> string) * (FTerm.variable -> string)  -> 
                                 (string * {vars:string list,fsyms:string list,fsymbols:fsymbol list,osorts: ModSymbol.mod_symbol list})

   val makePolySpassTermLst: term list * (variable list) * (string -> string) * (string -> string) * (FTerm.variable -> string) -> 
                                         (string list * {vars:string list,fsyms:string list,fsymbols:fsymbol list,osorts: ModSymbol.mod_symbol list})

   val makePolyTerm: term * (variable list) * (string -> string) * (string -> string) * (FTerm.variable -> string) * string -> 
                            (string * {vars:string list,fsyms:string list,fsymbols:fsymbol list,osorts: ModSymbol.mod_symbol list})

   val makePolyTermLst: term list * (variable list) * (string -> string) * (string -> string) * (FTerm.variable -> string) * string -> 
                                    (string list * {vars:string list,fsyms:string list,fsymbols:fsymbol list,osorts: ModSymbol.mod_symbol list})

   val global_tccs: (term * sort) list ref 

   val tccsToString: (term * sort) list -> string

   val apply: FTerm.sub * (variable list) * (fsymbol * sort) list * term -> term
   val applyLst: FTerm.sub * (variable list) * (fsymbol * sort) list * term list -> term list 

   val evaluateString:(string -> unit) ref
   val fauxTermToPrettyString: int * fsymbol * term list -> string 

end

