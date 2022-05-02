(*======================================================================

A trivial list-based implementation of simple dictionaries. Used with/for
very small dictionaries. 

=======================================================================*)

structure GMap:GMAP = 
struct

  type ('d,'r) map = ('d * 'r) list

  val empty = []

  fun lookUp(el,m,eq) = 
    let fun look(d,[]) = NONE 
          | look(d,(d1,r1)::rest) = if (eq(d,d1)) then SOME(r1) else look(d,rest)
    in
      look(el,m)
    end

  fun augment(m,(d,r)) = (d,r)::m

  fun augmentLst(map,new_bindings) = new_bindings@map

  fun join(old_map,new_map) = new_map@old_map

  fun make(bindings) = bindings

end (** of structure GMap **)
