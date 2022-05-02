(*======================================================================

A trivial but useful implementation of stacks as a simple wrapper around
cons lists.

=======================================================================*)

structure LStack : STACK = 
struct

  type 'a stack = 'a list

  exception EmptyStack 

  fun top([]) = raise EmptyStack
    | top(a::_) = a;

  val empty = []

  val push = op::

  val pop = tl

  val isEmpty = null

  fun list(l) = l;

  fun size(s) = length(s);

end;
