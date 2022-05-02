(*======================================================================

An implementation of the set-of-sentences signature.

=======================================================================*)

structure PropSet: PROP_SET = 

struct

structure HTable = HashTable

open Prop

val dependency_table : (prop,prop list) HashTable.hash_table = HashTable.mkTable(hash,alEq) (500,Basic.Fail("Hashing Exception"))

fun enterDependency(p,props) = (HashTable.insert dependency_table (p,props))

fun lookUpDependency(p) = (HashTable.find dependency_table p)

fun lookUpDependencyTransitively(p) = 
     let val mem: (prop,prop list) HashTable.hash_table = HashTable.mkTable(hash,alEq) (100,Basic.Fail("Hashing Exception"))
         fun look(p) = 
               (case (HashTable.find mem p) of
                   SOME(L) => []
                 | _ => let val props = (case (HashTable.find dependency_table p) of
                                            SOME(L) => L | _ => [])
                            val _ = (HashTable.insert mem (p,props)) 
                        in
			   props@(Basic.flatten(map look props))
                        end)
      in
        Prop.dedup(look(p))
      end

type prop = Prop.prop

type prop_set = prop IntBinaryMap.map

val empty_prop_set:prop IntBinaryMap.map = IntBinaryMap.empty

fun isMember(p,pset) = 
  (case IntBinaryMap.find(pset,ABase.getPropCode(p)) of
     NONE => false
   | _ => true)
    
fun areMembers(props,pset) = Basic.forall(props,fn p => isMember(p,pset))

fun insert(p,pset:prop_set) = IntBinaryMap.insert(pset,ABase.getPropCode(p),p)

fun insertLst([],res) = res
  | insertLst(p::more,res:prop_set) = insertLst(more,insert(p,res))

fun insertVal(v,pset) = (case SemanticValues.coerceValIntoProp(v) of
                            SOME(p) => insert(p,pset)
                          | _ => Basic.fail("\nTrying to insert a non-sentential value into a propset.\n"))

fun insertValLst([],res) = res
  | insertValLst(v::more,res:prop_set) = insertValLst(more,insertVal(v,res))

fun remove(pset,p) = let val (pset',_) = IntBinaryMap.remove(pset,ABase.getPropCode(p)) in pset' end handle _ => pset

fun removeVal(pset,v) =
                     (case SemanticValues.coerceValIntoProp(v) of
                         SOME(p) => remove(pset,p)
                       | _ => Basic.fail("\nTrying to remove a non-sentential value from a propset.\n"))

fun removeValLst([],res) = res
  | removeValLst(v::more,res:prop_set) = removeValLst(more,removeVal(res,v))

fun removeLst([],res) = res
  | removeLst(p::more,res:prop_set) = removeLst(more,remove(res,p))

fun list(pset) = IntBinaryMap.listItems pset 

end (** of structure PropSet **)



