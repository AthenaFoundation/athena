(*======================================================================

This file specifies the API of module-enabled Athena symbols. The key
functionality is the same as for flat symbols.

=======================================================================*)

signature MOD_SYMBOL =sig

  eqtype mod_symbol

  val makeModSymbol : Symbol.symbol list * Symbol.symbol * Symbol.symbol -> mod_symbol

  val makeModSymbol' : Symbol.symbol list * Symbol.symbol -> mod_symbol

  val makeSimpleName: string -> mod_symbol

  val name : mod_symbol -> string

  val nameAsSymbol : mod_symbol -> Symbol.symbol 

  val unlift: mod_symbol -> mod_symbol				       

  val makeName: Symbol.symbol list * Symbol.symbol -> string

  val modulePrefix: mod_symbol -> string 

  val split : mod_symbol -> (Symbol.symbol list * Symbol.symbol)

  val modules: mod_symbol -> Symbol.symbol list 

  val lastName: mod_symbol -> Symbol.symbol
  
  val code: mod_symbol -> int 

  val modSymEq: mod_symbol * mod_symbol -> bool

  val isPlainSymbol: mod_symbol -> bool

  val compare: mod_symbol * mod_symbol -> order

  val dum_modsym: string -> mod_symbol

  type 'a htable = (mod_symbol,'a) HashTable.hash_table;
  val makeHTable: unit -> 'a htable;
  val makeHTableWithInitialSize: int -> 'a htable;
  val augmentHT: 'a htable * 'a htable -> unit 
  val clearHTable: 'a htable -> unit;
  val insert: 'a htable * mod_symbol * 'a -> unit
  val removeHT: 'a htable * mod_symbol -> 'a 
  val insertLst: 'a htable * (mod_symbol * 'a) list -> unit
  val find: 'a htable * mod_symbol -> 'a option 
  val numItems: 'a htable ->  int
  val listItems: 'a htable -> 'a list
  val listItemsi : 'a htable -> (mod_symbol * 'a) list
  val exists: 'a htable * mod_symbol -> bool
  val tableToString: 'a htable * ('a -> string) -> string

  type 'a mapping
  val empty_mapping : 'a mapping
  val enter : 'a mapping * mod_symbol * 'a -> 'a mapping
  val enterLst: 'a mapping * (mod_symbol *'a) list -> 'a mapping
  val removeBinding: 'a mapping * mod_symbol -> 'a mapping * 'a
  val augment: 'a mapping * 'a mapping  -> 'a mapping
  val lookUp  : 'a mapping * mod_symbol -> 'a option
  val map: ('a -> 'a) * 'a mapping -> 'a mapping
  val listImages: 'a mapping -> 'a list 

   type set
   val empty_set: set
   val singleton: mod_symbol -> set
   val isEmpty: set -> bool
   val size: set -> int
   val setMap: (mod_symbol -> mod_symbol) -> set -> set
   val setApp: (mod_symbol -> unit) -> set -> unit 
   val equal: set * set -> bool 
   val add: mod_symbol * set -> set
   val addLst: mod_symbol list * set -> set 
   val symListToSet: mod_symbol list -> set 
   val remove: mod_symbol * set -> set
   val union: set * set -> set
   val unionLst: set list -> set 
   val intersection: set * set -> set
   val difference: set * set -> set
   val isMember: mod_symbol * set -> bool
   val listModSymbols: set -> mod_symbol list
  val restoreTable: mod_symbol list * set * 'a htable -> unit 



end;
