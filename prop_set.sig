(*======================================================================

A signature for sets of sentences.

=======================================================================*)

signature PROP_SET = 
sig 

    type prop_set
   
    val empty_prop_set: prop_set

    val isMember: Prop.prop * prop_set -> bool 

    val areMembers: Prop.prop list * prop_set -> bool

    val insert: Prop.prop * prop_set -> prop_set

    val insertVal: SemanticValues.value * prop_set -> prop_set

    val remove: prop_set * Prop.prop  -> prop_set
    val removeLst: Prop.prop list * prop_set  -> prop_set
    val removeVal: prop_set * SemanticValues.value  -> prop_set
    val removeValLst: SemanticValues.value list * prop_set  -> prop_set

    val insertLst: Prop.prop list * prop_set -> prop_set
    val insertValLst: SemanticValues.value list * prop_set -> prop_set

    val list: prop_set -> Prop.prop list

    val enterDependency: Prop.prop * (Prop.prop list)  -> unit
    val lookUpDependency: Prop.prop -> (Prop.prop list option)
    val lookUpDependencyTransitively: Prop.prop -> Prop.prop list 

end
