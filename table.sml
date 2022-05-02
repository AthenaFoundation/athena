 functor IntMapTable (type key
		     val getInt: key -> int) : TABLE =
struct
  type key=key
  type 'a table = 'a IntBinaryMap.map
  val empty = IntBinaryMap.empty
  fun enter(t,k,a) = IntBinaryMap.insert(t,getInt k,a)
  fun remove(t,k) = IntBinaryMap.remove(t,getInt k) 
  fun enterLst(t,[]) = t 
    | enterLst(t,(k,a)::more) = enterLst(enter(t,k,a),more);
  fun look(t,k) = IntBinaryMap.find(t,getInt k)
  val listItems = IntBinaryMap.listItems;
  val listItemsi = IntBinaryMap.listItemsi;
  val foldl = IntBinaryMap.foldl;
  val foldli = IntBinaryMap.foldli;
  val map = IntBinaryMap.map;
  val mapi = IntBinaryMap.mapi;
  val listKeys = IntBinaryMap.listKeys 
  fun domainSize(t) = IntBinaryMap.numItems t 
  fun augment(t1,t2) = let val keys = listKeys t2
                           fun f(t,[]) = t
                             | f(t,k::rest) = (case IntBinaryMap.find(t2,k) of
						 SOME(a) => f(IntBinaryMap.insert(t,k,a),rest)
                                               | _ => raise Basic.Never)
                       in
                          f(t1,keys) 
                       end 
end

