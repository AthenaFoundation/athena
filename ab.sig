(*======================================================================

The signature of assumption bases.

=======================================================================*)

signature ABASE = 
sig 

    type assum_base
   
    val empty_ab: assum_base

    val isMember: Prop.prop * assum_base -> bool 

    val areMembers: Prop.prop list * assum_base -> bool

    val insert: Prop.prop * assum_base -> assum_base

    val insertAlongWithConjuncts: Prop.prop * assum_base -> assum_base

    val remove: assum_base * Prop.prop  -> assum_base

    val augment: assum_base * Prop.prop list -> assum_base

    val fetch: assum_base * (Prop.prop -> bool) -> Prop.prop option

    val fetchAll: assum_base * (Prop.prop -> bool) -> Prop.prop list

    val getAll: assum_base -> Prop.prop list 

    val getTag: assum_base -> int 

    val getPropCode: Prop.prop -> int 

    val occursFree: AthTermVar.ath_term_var * assum_base -> bool 

    val occursFreeUpToSubsorting: AthTermVar.ath_term_var * assum_base -> bool 

    (* occursFreeUpToSubsorting uses Prop.occursFreeUpToSubsorting *)

    val propCount: unit -> int

    val insertions: int ref

    val look_ups: int ref

    val bucketSizes: unit -> int list 
    val getBucketSizeStatistics: unit -> string

    val getAssertions: assum_base -> Prop.prop list
    val addAssertion: Prop.prop * assum_base -> assum_base
    val addAssertionAlongWithConjuncts: Prop.prop * assum_base -> assum_base
    val addAssertions: Prop.prop list * assum_base -> assum_base
    val isAssertion: Prop.prop * assum_base -> bool 

    val adjustHashTable: assum_base -> unit 

    val top_assum_base: assum_base ref
    
end
