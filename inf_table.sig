(*======================================================================

A signature for dictionaries with infinite-integer keys.

=======================================================================*)

signature INF_TABLE = 
sig
   type key
   type 'a table
   val empty : 'a table
   val isEmpty: 'a table -> bool 
   val enter : 'a table * key * 'a -> 'a table
   val enterLst: 'a table * ((key * 'a) list) -> 'a table
   val look  : 'a table * key -> 'a option
   val listItems: 'a table -> 'a list
   val listItemsi: 'a table -> (InfNum.inf_num * 'a) list
   val foldl: (('a * 'b) -> 'b) -> 'b -> 'a table -> 'b
   val foldli: ((InfNum.inf_num * 'a * 'b) -> 'b) -> 'b -> 'a table -> 'b
   val map: ('a -> 'a) -> 'a table -> 'a table 
   val mapi: ((InfNum.inf_num * 'a) -> 'a) -> 'a table -> 'a table 
   val listKeys: ('a table) -> (InfNum.inf_num list)
   val augment: ('a table) * ('a table) -> ('a table)
end
