(*======================================================================

This file specifies the signature of flat Athena symbols. Every Athena
identifier that is not inside a module is a symbol of this type, e.g.,
when one writes

define x := 3

at the top level, the identifier x is stored as a value of this type. 

=======================================================================*)

signature SYMBOL =sig

  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string
  val symEq: symbol * symbol -> bool
  exception Symbol

  val printSymCounter: unit -> unit 

  val hashSymbol:symbol -> Word.word 
  val code: symbol -> int 

  val compare: symbol * symbol -> order
  
  val freshSymbol: string option -> symbol 

(******* Hash tables for Athena symbols: *******)

  type 'a htable
  val makeHTable: unit -> 'a htable;
  val makeHTableWithInitialSize: int -> 'a htable;
  val augmentHT: 'a htable * 'a htable -> unit 
  val clearHTable: 'a htable -> unit;
  val insert: 'a htable * symbol * 'a -> unit
  val removeHT: 'a htable * symbol -> 'a 
  val insertLst: 'a htable * (symbol * 'a) list -> unit
  val find: 'a htable * symbol -> 'a option 
  val numItems: 'a htable ->  int
  val listItems: 'a htable -> 'a list
  val listItemsi : 'a htable -> (symbol * 'a) list
  val exists: 'a htable * symbol -> bool   

  val makePrivateString: string -> string
  val makePrivateSymbol: string -> symbol     

(******* Functional dictionaries for Athena symbols: *******)

  type 'a mapping
  val empty_mapping : 'a mapping
  val enter : 'a mapping * symbol * 'a -> 'a mapping
  val enterLst: 'a mapping * (symbol *'a) list -> 'a mapping
  val augment: 'a mapping * 'a mapping  -> 'a mapping
  val removeBinding: 'a mapping * symbol -> 'a mapping * 'a 
  val lookUp  : 'a mapping * symbol -> 'a option
  val map: ('a -> 'a) * 'a mapping -> 'a mapping
  val listImages: 'a mapping -> 'a list
  val listSymbolsAndImages: 'a mapping -> (symbol * 'a) list
  val domainSize: 'a mapping -> int
  val listSymbolsInDomain: 'a mapping -> symbol list 

(******* Sets for Athena symbols: *******)

   type set
   val empty_set: set
   val singleton: symbol -> set
   val isEmpty: set -> bool
   val size: set -> int
   val equal: set * set -> bool 
   val setMap: (symbol -> symbol) -> set -> set
   val setApp: (symbol -> unit) -> set -> unit 
   val add: symbol * set -> set
   val addLst: symbol list * set -> set 
   val symListToSet: symbol list -> set 
   val remove: symbol * set -> set
   val union: set * set -> set
   val unionLst: set list -> set 
   val intersection: set * set -> set
   val difference: set * set -> set
   val isMember: symbol * set -> bool
   val listSymbols: set -> symbol list
   val fresh: set -> symbol 

(******* Athena mappings with retrievable domains: *******)

  type 'a mappingWD
  val empty_mappingWD : 'a mappingWD
  val enterWD : 'a mappingWD * symbol * 'a -> 'a mappingWD
  val enterLstWD: 'a mappingWD * (symbol *'a) list -> 'a mappingWD
  val augmentWD: 'a mappingWD * 'a mappingWD  -> 'a mappingWD
  val removeBindingWD: 'a mappingWD * symbol -> 'a mappingWD * 'a 
  val lookUpWD  : 'a mappingWD * symbol -> 'a option
  val mapWD: ('a -> 'a) * 'a mappingWD -> 'a mappingWD
  val listImagesWD: 'a mappingWD -> 'a list
  val listSymbolsAndImagesWD: 'a mappingWD -> (symbol * 'a) list
  val domainSizeWD: 'a mappingWD -> int
  val listSymbolsInDomainWD: 'a mappingWD -> symbol list
  
end
