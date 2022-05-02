(*======================================================================

An implementation of finite-capacity linked lists whose elements drop from
one end as more elements are inserted (to make room for the new additions).
This is not a significant piece of functionality (it's only used to populate
the contents of the call stack, for debugging purposes).

=======================================================================*)

signature LIST = 
sig

   type element
   type drop_list
  
   val prepend: element * drop_list -> unit
   val makeList: element * int -> drop_list
   val assign: drop_list * drop_list -> unit 
   val firstPart: drop_list -> element list 
   val firstPartFilled: drop_list -> bool 
   val setCapacity: int -> unit

   val toList: drop_list * {with_first_part:bool} -> element list 
   val map: (element -> element) * drop_list * {with_first_part:bool} -> element list
   val listLength: drop_list -> int

end

