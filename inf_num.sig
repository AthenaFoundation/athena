(*======================================================================

A very light-weight API for (practically) infinite numbers, used
for counters that may grow very large. 

=======================================================================*)

signature INF_NUM = sig

  type inf_num;

  val eq: inf_num * inf_num -> bool

  val compare: inf_num * inf_num -> General.order

  val makeInfNum: unit -> inf_num;

  val makeInfNumTagged: unit -> inf_num;

  val tagged: inf_num -> bool;

  val tag: inf_num -> inf_num;

  val increment: inf_num -> inf_num;
 
  val fromInt:  int -> inf_num;

  val fromString: string -> inf_num;

  val top: inf_num -> int;

  val toString: inf_num -> string;

  val print: inf_num -> unit;

end;
