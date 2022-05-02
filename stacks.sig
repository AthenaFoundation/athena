(*======================================================================

A simple stack signature.

=======================================================================*)

signature STACK =
sig

   exception EmptyStack 

   type 'a stack

   val empty: 'a stack

   val top: 'a stack -> 'a

   val push: 'a * 'a stack -> 'a stack

   val pop: 'a stack -> 'a stack 

   val isEmpty: 'a stack -> bool

   val list: 'a stack -> 'a list 

   val size: 'a stack -> int

end
