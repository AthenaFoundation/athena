(*======================================================================

A signature for state-space-based search.

=======================================================================*)

signature STATE_SPACE_SEARCH =
sig

structure state_space: STATE_SPACE 

datatype search_style = depth_first | breadth_first | best_first;

val isSilentOutput: unit -> bool

val silenceOutput: unit -> unit 

val unSilenceOutput: unit -> unit 

type search_function = state_space.state * (state_space.state -> bool) * int ->
                       (state_space.state * int) option 

val makeSearchFunction: (state_space.state * state_space.state list * int -> unit) *
                        (state_space.state -> state_space.state list) *
                        search_style * 
                        ((state_space.state -> real) option) -> search_function

end
