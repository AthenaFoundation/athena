(*======================================================================

This is another dictionary signature, except that instead of assuming that
every key can be mapped to an integer, this dictionary works with a given
total comparison function that maps any two keys to a value of type order
(note: order is a built-in SML datatype with three nullary constructors,
LESS, EQUAL, and GREATER). 

=======================================================================*)

signature OMAP = 
  sig

    type ('a, 'b) mapping 

    exception MapEx

    val makeMap : (('a * 'a) -> order) -> ('a,'b) mapping

    val insert:  (('a,'b) mapping) * 'a * 'b -> ('a,'b) mapping

    val insertLst:  (('a,'b) mapping) * (('a * 'b) list) -> ('a,'b) mapping

    val find:  (('a,'b) mapping) * 'a -> 'b option     

    val remove : ('a,'b) mapping * 'a -> ('a,'b) mapping * 'b
    
   (* Remove an item, returning new map and value removed. Raises MapEx if not found. *)

    val size: ('a,'b) mapping -> int 

    val listKeys: ('a,'b) mapping -> 'a list
    val listValues: ('a,'b) mapping -> 'b list
    val listKeyValuePairs: ('a,'b) mapping -> ('a * 'b) list

    val applyToKeys: ('a -> unit) * ('a,'b) mapping -> unit 
    val applyToValues: ('b -> unit) * ('a,'b) mapping -> unit 
    val applyToKeyValuePairs: (('a * 'b) -> unit) * ('a,'b) mapping -> unit 

    val mapToKeyValuePairs: (('a * 'b) -> 'b) * ('a,'b) mapping -> ('a,'b) mapping
    val mapToValues: ('b -> 'b) * ('a,'b) mapping -> ('a,'b) mapping

    val foldl: ('key_type * 'value_type * 'a -> 'a) * 'a * ('key_type, 'value_type) mapping -> 'a

end 