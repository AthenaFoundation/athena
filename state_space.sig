(*======================================================================

A signature for search states, and for state tables. State-based search
is used for automating proof chains.

=======================================================================*)

signature STATE_SPACE =
sig

type state
type state_table

val eq: state * state -> bool 

val stateToString: state -> string 

val makeStateTable: unit -> state_table
val addState: state * state_table -> state_table
val isMember: state * state_table -> bool
val remove: state * state_table -> state_table

end