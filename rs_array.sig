(*======================================================================

Signature for resizable arrays.

=======================================================================*)

signature RS_ARRAY = 

sig

  type 'a rs_array
  val setIncrement: int -> unit 
  val makeRSArray : int * 'a -> 'a rs_array
  val makeEmptyRSArray: unit -> 'a rs_array
  val length : 'a rs_array -> int
  val sub : 'a rs_array * int -> 'a
  val app : 'a rs_array * ('a -> unit) -> unit 
  val update : 'a rs_array * int * 'a * 'a option * int -> unit
  val updateDefault : 'a rs_array * int * 'a -> unit
  val copy : 'a rs_array * int -> 'a rs_array

end
