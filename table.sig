(*======================================================================

This signature, implemented in table.sml, specifies a simple dictionary ADT
in functional style, from a type key to any type 'a (i.e., 'a is the type
of the dictionary values). We assume any key can be efficiently mapped to
a unique integer (via a getInt function that is passed as an argument to
the functor in table.sml that produces structures satisfying this signature).
Such tables are used widely in Athena as dictionaries that map, e.g., Athena
identifiers to Athena values, or Athena term variables (such as ?x) to other
Athena terms, and so on. 

=======================================================================*)

signature TABLE = 
sig
   type key
   type 'a table
   val empty : 'a table
   val enter : 'a table * key * 'a -> 'a table
   val enterLst: 'a table * ((key * 'a) list) -> 'a table
   val remove: 'a table * key -> 'a table * 'a 
   val look  : 'a table * key -> 'a option
   val listItems: 'a table -> 'a list
   val listItemsi: 'a table -> (int * 'a) list
   val foldl: (('a * 'b) -> 'b) -> 'b -> 'a table -> 'b
   val foldli: ((int * 'a * 'b) -> 'b) -> 'b -> 'a table -> 'b
   val map: ('a -> 'a) -> 'a table -> 'a table 
   val mapi: ((int * 'a) -> 'a) -> 'a table -> 'a table 
   val listKeys: ('a table) -> (int list)
   val augment: ('a table) * ('a table) -> ('a table)
   val domainSize: 'a table -> int 
end
