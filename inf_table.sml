(*======================================================================

Dictionaries with infinite-integer keys, used in the implementation of
'fast terms' (fterm.sml). 

=======================================================================*)


structure InfIntMapTable : INF_TABLE = 

struct 

  type key=InfNum.inf_num;

  type 'a table = 'a InfIntMap.map

  val empty = InfIntMap.empty

  val isEmpty = InfIntMap.isEmpty;

  fun enter(t,k,a) = InfIntMap.insert(t,k,a)

  fun remove(t,a) = InfIntMap.remove(t,a)

  fun enterLst(t,[]) = t 
    | enterLst(t,(k,a)::more) = enterLst(enter(t,k,a),more);

  fun look(t,k) = InfIntMap.find(t,k)

  val listItems = InfIntMap.listItems;

  val listItemsi = InfIntMap.listItemsi;

  val foldl = InfIntMap.foldl;

  val foldli = InfIntMap.foldli;

  val map = InfIntMap.map;

  val mapi = InfIntMap.mapi;

  val listKeys = InfIntMap.listKeys 

  fun augment(t1,t2) = let val keys = listKeys t2
                           fun f(t,[]) = t
                             | f(t,k::rest) = (case InfIntMap.find(t2,k) of
						 SOME(a) => f(InfIntMap.insert(t,k,a),rest)
                                               | _ => raise Basic.Never)
                       in
                          f(t1,keys) 
                       end 
end
