signature SET = 
sig

   type element
   type set
   val empty: set
   val singleton: element -> set
   val isEmpty: set -> bool
   val size: set -> int
   val isSubset: set * set -> bool 
   val equal: set * set -> bool 
   val insert: element * set -> set
   val insertLst: element list * set -> set
   val listToSet: element list -> set
   val remove: element * set -> set
   val difference: set * set -> set 
   val union: set * set -> set
   val unionLst: set list -> set
   val intersection: set * set -> set
   val isMember: element * set -> bool
   val listElements: set -> element list
   val map: (element -> element) -> set -> set 
   val app: (element -> unit) -> set -> unit 
   val foldl: (element * 'a -> 'a) -> 'a -> set -> 'a
end

