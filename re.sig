(*======================================================================

A core-functionality signature for regexp-based value matching.

=======================================================================*)

signature RE = 
sig

  type value
  type pat
  type constraint

  type tag0 = constraint GeneralRE.tag0

  type RE0 = (pat,constraint) GeneralRE.RE0

  val reToString: RE0 -> string

  val tt: tag0

  val concatLst: RE0 list -> RE0

  val inside_constraint: bool ref

  val match: RE0 * int * 
             value list * 
             value Symbol.mapping * 
             (pat * value -> value Symbol.mapping option) * 
             ((constraint *  (Symbol.symbol list  * value Symbol.mapping * Symbol.symbol list  * value list Symbol.mapping)) -> bool) *
             (Symbol.symbol -> value option)
                  -> ((Symbol.symbol list * value Symbol.mapping * Symbol.symbol list * value list Symbol.mapping) * real) option
end 