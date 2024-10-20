(*======================================================================

An implementation of the assumption base signature.

=======================================================================*)

structure ABase: ABASE = 
struct

structure HTable = HashTable

exception AssumptionBase

val insertions = ref(0)

val look_ups = ref(0)

val sizeHint = 32257

open Prop

val max_prop_hash_length = getMaxHashLength()

val next_code = ref 2

type code_type = int

val hash = Prop.hash

val hashtable : (prop,(code_type * bool)) HashTable.hash_table = 
     		 HashTable.mkTable(hash, (fn (p1,p2) => (Prop.alEq(p1,p2)))) (sizeHint,AssumptionBase)

fun bucketSizes() = HashTable.bucketSizes(hashtable)

fun getBucketSizeStatistics() = 
      let val bucket_sizes = bucketSizes()
          val max_bucket_size = Basic.maxLst(bucket_sizes)
          val _ = print("\nMax bucket size: "^(Int.toString(max_bucket_size)))
          val A = Array.array(max_bucket_size + 1,0)
          fun loop([]) = ()
            | loop(sz::more) = (Array.update(A,sz,Array.sub(A,sz) + 1);loop(more))
          val _ = loop(bucket_sizes)
          val str = "\nThere were "^(Int.toString(length(bucket_sizes)))^" buckets in total."
          val str1 = "\nThe sizes were distributed as follows:\n\n"
          val AL:int list = Basic.arrayToList(A)
          val lines = Basic.mapWithIndex((fn (x,i) => "There were "^(Int.toString(x))^" buckets of size "^(Int.toString(i))),AL)
          val str2 = Basic.printListStr(lines,fn x => x,"\n")
      in
         str^str1^str2
      end

fun propCount() = HashTable.numItems(hashtable)
 
fun printHashTable() = 
   let val pair_list: (prop * (code_type * bool)) list = HashTable.listItemsi(hashtable)
      val res =       Basic.printListStr(pair_list,fn (p,(i,b)) => let val s1 = "\nHT prop: "
                                                                       val s2 = (Prop.toPrettyStringDefault(0,p))
								       val s3 = ", HT code: " ^ (Int.toString(i))
								       val s4 = " and HT assertion type: " ^ (Basic.boolToString(b))
                                                                   in
								      s1 ^ s2 ^ s3 ^ s4
                                                                   end,
                                         "\n")

   in
      res 
   end

fun getPropCodeAux P = 
   let val res = (case (HashTable.find hashtable P) of 
                          SOME (i,_) => i
                       | _ => let val i = !next_code
                                  val _ = next_code := !next_code + 1
                                  in
                                    (HashTable.insert hashtable (P,(i,false));i)
                                  end)
   in
     res
    end

val no_adjustments_yet = ref(true)

fun getPropCode(P) = 
    if !no_adjustments_yet then
       case getCode(P) of
          ref(SOME(i)) => i
        | _ => let val i = getPropCodeAux(P)
               in
                 (setCode(P,i);i)
               end
    else getPropCodeAux(P)			    

val next_ab_tag = ref 0

fun hashFun(code:int,tag:int) = Basic.hashPair(code,tag)

fun equalityFun((code1,tag1),(code2,tag2)) = code1 = code2 andalso tag1 = tag2

val memoization_table: ((int * int),bool) HashTable.hash_table = HashTable.mkTable(hashFun, equalityFun) (3467,AssumptionBase)

val count = ref 0

val inc = Basic.incAndReturn

structure Table = IntMapTable(type key = int 
                              fun getInt(n) = n)

datatype assum_base = abase of {prop_table: prop IntBinaryMap.map,tag:int}

fun getTag(abase({tag,...})) = tag

val empty_prop_table: prop IntBinaryMap.map = IntBinaryMap.empty

val empty_ab = abase {prop_table=empty_prop_table,tag=0}

val assertions = ref(empty_prop_table)

fun remove(ab as (abase {prop_table,tag,...}),P) = 
  let val code = getPropCode(P)
      val (m,_) = (IntBinaryMap.remove(prop_table,code)) handle _ => (prop_table,P)
  in
    abase({prop_table=m,tag=inc(next_ab_tag)})
  end 

fun addAssertion(p,abase({prop_table,tag,...}):assum_base) = 
 let val _ = (case (HashTable.find hashtable p) of 
                 SOME (i,_) => (HashTable.insert hashtable (p,(i,true)))
               | _ => let val i = !next_code
                          val _ = next_code := !next_code + 1
                      in
                        ((HashTable.insert hashtable (p,(i,true)));
                         setCode(p,i))
                      end)
 in
   abase({prop_table=prop_table,tag=inc(next_ab_tag)})
 end

fun addAssertions(props,beta:assum_base) = 
  let fun loop([],res) = res
        | loop(a::more,res) = loop(more,addAssertion(a,res))
  in 
    loop(props,beta) 
  end

fun addAssertionAlongWithConjuncts(p,ab) = addAssertions(p::(Prop.getConjunctsOnly p),ab)

fun isAssertion(p,abase({prop_table,...}):assum_base) = 
      (case IntBinaryMap.find(prop_table,getPropCode(p)) of
           NONE => false
         | _ => (case (HashTable.find hashtable p) of 
                    SOME (_,b) => b
                  | _ => false))

fun isAssertionAlt(p) = 
                (case (HashTable.find hashtable p) of 
                    SOME (_,b) => b
                  | _ => false)

fun getAssertions(abase({prop_table,...}):assum_base) =  
      List.filter isAssertionAlt (IntBinaryMap.listItems prop_table)

fun isMember(P,ab as abase({prop_table,...}): assum_base) = 
       (Basic.inc(look_ups);
        let val code = getPropCode(P)
        in
         (case IntBinaryMap.find(prop_table,code) of
             NONE => false
           | _ => true)
        end)

fun adjustHT(ab) = 
 let val _ = HashTable.filteri (fn (p,_) => isMember(p,ab)) hashtable 
 in
    no_adjustments_yet := false
 end

val adjustment_size_trigger_1 = 1000000
val adjustment_size_trigger_2 = 2000000

fun adjustHashTable(ab:assum_base as abase({prop_table,...})) =
       let val hash_table_count = HashTable.numItems(hashtable)
           val ab_count = Table.domainSize(prop_table)
           val deciding_condition_1 = (hash_table_count > adjustment_size_trigger_1 andalso hash_table_count < adjustment_size_trigger_2 
                                       andalso hash_table_count > 7 * ab_count)
           val deciding_condition_2 = (hash_table_count > adjustment_size_trigger_2
                                       andalso hash_table_count >= 2 * ab_count)
       in
         if deciding_condition_1 orelse deciding_condition_2 then adjustHT(ab) else ()
       end

fun isMemberMem(P,ab as abase({prop_table,tag,...}): assum_base) = 
       (Basic.inc(look_ups);
        let val code = getPropCode(P)
        in
           (case (HashTable.find memoization_table (code,tag)) of
               SOME(res) => res 
              | _ => (case IntBinaryMap.find(prop_table,code) of
                         NONE => let val res = false
                                     val _ = HashTable.insert memoization_table ((code,tag),res)
                                 in
                                    res
                                 end
                       | _ => let val res = true 
                                     val _ = HashTable.insert memoization_table ((code,tag),res)
                                 in
                                    res
                                 end))
        end)

fun areMembers(props,ab) = List.all (fn p => isMember(p,ab)) props

fun insertAux(P,ab as abase({prop_table,tag,...}): assum_base) =  
     let val _ = Basic.inc(insertions)
	 val code = getPropCode(P)
     in 
       abase({prop_table=IntBinaryMap.insert(prop_table,code,P),tag=inc(next_ab_tag)})
     end

fun insert(P,ab) = insertAux(P,ab)

fun augment(ab,props) = List.foldl insert ab props

fun insertAlongWithConjuncts(P,ab) = augment(ab,P::(Prop.getConjunctsOnly P))

fun getAll(ab as abase({prop_table,...}):assum_base) = IntBinaryMap.listItems(prop_table)

fun occursFree(v,ab) = List.exists (fn (P) => Prop.occursFree(v,P)) (getAll ab) 

fun occursFreeUpToSubsorting(v,ab) = List.exists (fn (P) => Prop.occursFreeUpToSubsorting(v,P)) (getAll ab) 

fun fetchAll(ab as abase({prop_table,...}):assum_base,test) = 
    IntBinaryMap.foldl (fn (P,accum) => if test(P) then P::accum else accum) [] prop_table

exception FetchResult of Prop.prop

fun fetch(ab as abase({prop_table,...}):assum_base,test) = 
      let fun f() = IntBinaryMap.foldl 
                    (fn (P,accum) => if test(P) then raise FetchResult(P) else accum) [] prop_table;
      in
         (f();NONE) handle FetchResult(P) => SOME(P)
      end

val top_assum_base = ref(empty_ab)

end



