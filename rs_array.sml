structure RSA: RS_ARRAY = 

struct 

val default_increment = ref 0

fun setIncrement(k) = default_increment := k 

type 'a rs_array = 'a array ref

fun makeRSArray(count,x) = ref(Array.array(count,x))

fun makeEmptyRSArray() = ref(Array.fromList([]))

fun copy(ref(A),how_many) = 
      let val len = Array.length(A)
      in 
         if len < 1 then ref(Array.fromList([]))
         else let val v = Array.sub(A,0)
                  val A' = Array.array(len,v)
                  val block_size = if how_many >= 0 then SOME how_many else NONE
                  val _ = Array.copy({src=A,dst=A',si=0,di=0,len=block_size})
              in 
                 ref(A')  
              end
      end

fun app(ref(A),f) = Array.app f A

fun length(ref(A)) = Array.length(A)

fun sub(ref(A),i) = Array.sub(A,i)

fun update(rs_A as ref(A),index,x,fill_val_opt,increment) = 
   let val alen = Array.length(A)
   in 
     (if index >= alen then 
        let val diff = (index + 1 - alen)  
            val fill_val = (case fill_val_opt of
                              SOME v => v
                            | _ => x)
            val A' = Array.array(alen+diff+increment,fill_val)
            val _ = rs_A := A'
            val _ = Array.copy({src=A,si=0,dst=A',di=0,len=NONE})
            val _ = Array.update(A',index,x)
        in () end
    else Array.update(A,index,x))
   end

fun updateDefault(rs_A as ref(A),index,x) = 
   let val alen = Array.length(A)
   in 
     (if index >= alen then 
        let val diff = (index + 1 - alen)  
            val fill_val = x
            val A' = Array.array(alen+diff+(!default_increment),fill_val)
            val _ = rs_A := A'
            val _ = Array.copy({src=A,si=0,dst=A',di=0,len=NONE})
            val _ = Array.update(A',index,x)
        in () end
    else Array.update(A,index,x))
   end

end 

