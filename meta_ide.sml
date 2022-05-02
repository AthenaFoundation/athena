structure MetaId :> META_ID = 

struct

  type meta_id = string * int
       
  structure H = HashTable

  exception MetaId

  val next_mid = ref 0

  val sizeHint = 512

  fun hash(_,i) = Basic.hashInt(i)

  val hashtable : (string,int) H.hash_table = 
          		H.mkTable(HashString.hashString, op = ) (sizeHint,MetaId)

  fun makeMetaId name =
    let val res = case H.find hashtable name
                     of SOME i => (name,i)
                      | NONE => let val i = !next_mid
   	                        in 
                                   next_mid := i+1;
		                   H.insert hashtable (name,i);
		                   (name,i)
		                end
    in
      res 
    end 

  fun name(s,n) = s

  fun code(s,n) = n

  fun compare((_,n1),(_,n2)) = Int.compare(n1,n2);

  fun eq((s1,n1),(s2,n2)) = (n1 = n2)
					  
end
