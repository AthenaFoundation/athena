(*======================================================================

Signature for Athena term variables.

=======================================================================*)

signature ATH_TERM_VAR =
sig

  type ath_term_var;

  type sort

(** athTermVarWithSort makes an explicitly sorted variable, where the sort is passed as the second argument: **)

  val athTermVarWithSort : string * sort -> ath_term_var;

(** athTermVar makes a sorted variable with the given name and with a fresh polymorphic sort: **)

  val athTermVar : string -> ath_term_var;
  
  val name : ath_term_var -> string

  val tagVar: ath_term_var -> ath_term_var
  val isTagged: ath_term_var -> bool 

  val applySortSub: FTerm.sub * ath_term_var -> ath_term_var 
  val applySortSubLst: FTerm.sub * ath_term_var list -> ath_term_var list

  val athTermVarEq: ath_term_var * ath_term_var -> bool
  val athTermVarLitEq: ath_term_var * ath_term_var -> bool

  val nameEq: ath_term_var * ath_term_var -> bool

  val varInstance: ath_term_var * ath_term_var -> bool

  val getSort: ath_term_var -> sort 

  val isPoly: ath_term_var -> bool 

  val hash: ath_term_var -> Word.word

  val fresh: unit -> ath_term_var

  val freshWithPrefix: string -> ath_term_var

  val freshLst: 'a list -> ath_term_var list

  val freshWithSort: sort -> ath_term_var

  val freshWithSortAndPrefix: string * sort -> ath_term_var

  val freshVarName: unit -> string 

  val changeNames: ath_term_var * string -> ath_term_var

  val toString: ath_term_var * (FTerm.variable -> string) -> string
  val toStringDefault: ath_term_var  -> string

  val toStringWithSort: ath_term_var -> string

  val toPrettyString: int * ath_term_var * (FTerm.variable -> string) -> string
  val toPrettyStringDefault: int * ath_term_var -> string
  val toPrettyStringDefaultLst: int * (ath_term_var list) -> (string list)

  val fresh_name_prefix: string

  val renameSortVars: ath_term_var * FTerm.sub -> ath_term_var * FTerm.sub

  val compare: ath_term_var * ath_term_var -> order  

  val compareNames: ath_term_var * ath_term_var -> order  

  val reconcileVars: 'a list * ('a -> ath_term_var list) * FTerm.sub -> (ath_term_var list * FTerm.sub) * bool 

  val reconcilePolyConstants: 'a list * ('a -> (ModSymbol.mod_symbol * sort) list) * FTerm.sub -> ((ModSymbol.mod_symbol * sort) list * FTerm.sub) * bool 

  val simpleMerge:  ath_term_var list * ath_term_var list -> ath_term_var list

  val simpleMergeLst: 'a list * ('a -> ath_term_var list) -> ath_term_var list
  
  val swapSorts: ath_term_var * sort -> ath_term_var

  val update: ath_term_var list * ath_term_var list -> ath_term_var list
  val updatePolyConstants: (ModSymbol.mod_symbol * sort) list * (ModSymbol.mod_symbol * sort) list -> (ModSymbol.mod_symbol * sort) list 

  val varListsMatch: ath_term_var list * ath_term_var list -> bool 

  type 'a htable
  val makeHTable: unit -> 'a htable;
  val makeHTableWithVarEq: ((ath_term_var * ath_term_var) -> bool)  -> 'a htable;
  val insert: 'a htable * ath_term_var * 'a -> unit
  val clearTable: 'a htable -> unit
  val removeHT: 'a htable * ath_term_var -> 'a 
  val find: 'a htable * ath_term_var  -> 'a option 
  val numItems: 'a htable ->  int
  val listItems: 'a htable -> 'a list
  val listItemsi : 'a htable -> (ath_term_var * 'a) list
  val exists: 'a htable * ath_term_var -> bool   

  type var_set
  val empty: var_set
  val isEmpty: var_set -> bool
  val size: var_set -> int
  val equal: var_set * var_set -> bool 
  val isSubset: var_set * var_set -> bool 
  val add: ath_term_var * var_set -> var_set
  val addLst: ath_term_var list * var_set -> var_set
  val remove: ath_term_var * var_set -> var_set
  val union: var_set * var_set -> var_set
  val intersection: var_set * var_set -> var_set
  val isMember: ath_term_var * var_set -> bool
  val listVars: var_set -> ath_term_var list  


  type 'a mapping
  val empty_mapping : 'a mapping
  val isEmptyMapping : 'a mapping -> bool 
  val enter : 'a mapping * ath_term_var * 'a -> 'a mapping
  val enter_lst: 'a mapping * (ath_term_var *'a) list -> 'a mapping
  val augment: 'a mapping * 'a mapping * ath_term_var list -> 'a mapping
  val lookUp  : 'a mapping * ath_term_var -> 'a option
  val listImages: 'a mapping -> 'a list
  val listAll: 'a mapping -> (ath_term_var * 'a) list
  val foldl:  ('a * 'b -> 'b) -> 'b -> 'a mapping -> 'b
  val map:  ('a -> 'b) -> 'a mapping -> 'b mapping


  type 'a name_mapping
  val empty_name_mapping : 'a name_mapping
  val isEmptyNameMapping:  'a name_mapping -> bool
  val nameEnter : 'a name_mapping * ath_term_var * 'a -> 'a name_mapping
  val nameEnterLst: 'a name_mapping * (ath_term_var * 'a) list -> 'a name_mapping
  val nameAugment: 'a name_mapping * 'a name_mapping * ath_term_var list -> 'a name_mapping
  val nameLookUp  : 'a name_mapping * ath_term_var -> 'a option
  val nameListImages: 'a name_mapping -> 'a list
  val nameListAll: 'a name_mapping -> (ath_term_var * 'a) list
  val nameFoldl:  ('a * 'b -> 'b) -> 'b -> 'a name_mapping -> 'b
  val nameMap:  ('a -> 'b) -> 'a name_mapping -> 'b name_mapping

end;


