(*======================================================================

A very simple generic-dictionary API.

=======================================================================*)

signature GMAP = 
sig 
   type ('d,'r) map
   val empty: ('d,'r) map
   val lookUp: ('d * ('d,'r) map * ('d * 'd -> bool)) -> 'r option
   val augment: (('d,'r) map * ('d * 'r)) -> ('d,'r) map
   val augmentLst: (('d,'r) map * ('d * 'r) list) -> ('d,'r) map
   val join: ('d,'r) map * ('d,'r) map -> ('d,'r) map
   val make: ('d * 'r) list -> ('d,'r) map
end   
