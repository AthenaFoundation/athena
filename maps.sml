structure Maps : OMAP = 

struct
 
datatype ('a,'b) map = E | T of {key : 'a,value : 'b, cnt : int,left : ('a,'b) map, right : ('a,'b) map};

type ('a,'b) mapping = {compare: ('a * 'a) -> order, m: ('a,'b) map};

fun makeMap(c) = {compare=c,m=E};

fun wt (i : int) = i + i + i

fun isEmpty E = true
  | isEmpty _ = false

fun numItems E = 0
  | numItems (T{cnt,...}) = cnt

fun size({compare,m}) = numItems(m);

fun N(k,v,E,E) = T{key=k,value=v,cnt=1,left=E,right=E}
      | N(k,v,E,r as T n) = T{key=k,value=v,cnt=1+(#cnt n),left=E,right=r}
      | N(k,v,l as T n,E) = T{key=k,value=v,cnt=1+(#cnt n),left=l,right=E}
      | N(k,v,l as T n,r as T n') = 
          T{key=k,value=v,cnt=1+(#cnt n)+(#cnt n'),left=l,right=r};

    
fun single_L (a,av,x,T{key=b,value=bv,left=y,right=z,...}) = 
          N(b,bv,N(a,av,x,y),z)
      | single_L _ = raise Match;

fun single_R (b,bv,T{key=a,value=av,left=x,right=y,...},z) = 
          N(a,av,x,N(b,bv,y,z))
      | single_R _ = raise Match;

    
fun double_L (a,av,w,T{key=c,value=cv,left=T{key=b,value=bv,left=x,right=y,...},right=z,...}) =
          N(b,bv,N(a,av,w,x),N(c,cv,y,z))
      | double_L _ = raise Match
    
fun double_R (c,cv,T{key=a,value=av,left=w,right=T{key=b,value=bv,left=x,right=y,...},...},z) = 
          N(b,bv,N(a,av,w,x),N(c,cv,y,z))
      | double_R _ = raise Match
    
fun T' (k,v,E,E) = T{key=k,value=v,cnt=1,left=E,right=E}
      | T' (k,v,E,r as T{right=E,left=E,...}) =
          T{key=k,value=v,cnt=2,left=E,right=r}
      | T' (k,v,l as T{right=E,left=E,...},E) =
          T{key=k,value=v,cnt=2,left=l,right=E}

      | T' (p as (_,_,E,T{left=T _,right=E,...})) = double_L p
      | T' (p as (_,_,T{left=E,right=T _,...},E)) = double_R p

        (* these cases almost never happen with small weight*)
      | T' (p as (_,_,E,T{left=T{cnt=ln,...},right=T{cnt=rn,...},...})) =
          if ln < rn then single_L p else double_L p
      | T' (p as (_,_,T{left=T{cnt=ln,...},right=T{cnt=rn,...},...},E)) =
          if ln > rn then single_R p else double_R p

      | T' (p as (_,_,E,T{left=E,...})) = single_L p
      | T' (p as (_,_,T{right=E,...},E)) = single_R p

      | T' (p as (k,v,l as T{cnt=ln,left=ll,right=lr,...},
                      r as T{cnt=rn,left=rl,right=rr,...})) =
          if rn >= wt ln then (*right is too big*)
            let val rln = numItems rl
                val rrn = numItems rr
            in
              if rln < rrn then  single_L p  else  double_L p
            end
        
          else if ln >= wt rn then  (*left is too big*)
            let val lln = numItems ll
                val lrn = numItems lr
            in
              if lrn < lln then  single_R p  else  double_R p
            end
    
          else T{key=k,value=v,cnt=ln+rn+1,left=l,right=r}
      
fun min (T{left=E,key,value,...}) = (key,value)
        | min (T{left,...}) = min left
        | min _ = raise Match
  
fun delmin (T{left=E,right,...}) = right
        | delmin (T{key,value,left,right,...}) = T'(key,value,delmin left,right)
        | delmin _ = raise Match
      
fun delete' (E,r) = r
        | delete' (l,E) = l
        | delete' (l,r) = let val (mink,minv) = min r in
            T'(mink,minv,l,delmin r)
          end

   
fun insert ({compare,m},x,v) = 
  let fun i(E,x,v) = T{key=x,value=v,cnt=1,left=E,right=E}
        | i(T(set as {key,left,right,value,...}),x,v) = 
            if compare(key,x) = GREATER then T'(key,value,i(left,x,v),right)
            else if compare(key,x) = LESS then T'(key,value,left,i(right,x,v))
               else T{key=x,value=v,left=left,right=right,cnt= #cnt set}
      val m' = i(m,x,v)
  in
    {compare=compare,m=m'}
  end;

fun insertLst({compare,m},key_value_pairs) = 
  let fun i(E,x,v) = T{key=x,value=v,cnt=1,left=E,right=E}
        | i(T(set as {key,left,right,value,...}),x,v) = 
            if compare(key,x) = GREATER then T'(key,value,i(left,x,v),right)
            else if compare(key,x) = LESS then T'(key,value,left,i(right,x,v))
               else T{key=x,value=v,left=left,right=right,cnt= #cnt set}
      fun iLst(m,[]) = m
        | iLst(m,(x,v)::more) = iLst(i(m,x,v),more)
      val m' = iLst(m,key_value_pairs)
  in
    {compare=compare,m=m'}
  end;

fun inDomain({compare,m},x) = 
   let fun mem E = false
         | mem (T(n as {key,left,right,...})) =
		if compare(x,key) = General.GREATER then mem right
		else if compare(x,key) = General.LESS then mem left
    		else true
   in
      mem m
   end;
    
fun find({compare,m}, x) = 
  let fun mem E = NONE
        | mem (T(n as {key,left,right,...})) =
		if compare(x,key) = General.GREATER then mem right
		else if compare(x,key) = General.LESS then mem left
		else SOME(#value n)
	  
  in
    mem m
  end;

exception MapEx; 
    
fun remove({compare,m},x) = 
  let fun r(E) = raise MapEx
        | r(set as T{key,left,right,value,...}) =
              if  compare(key,x) = General.GREATER then 
                     let val (left',v) = r(left)
                     in 
                        (T'(key,value,left',right),v)
                     end
              else if compare(key,x) = General.LESS  then
                      let val (right',v) = r(right)
                      in 
                         (T'(key,value,left,right'),v) 
                      end
                   else (delete'(left,right),value)
       val (m',v) = r(m)
  in
     ({compare=compare,m=m'},v)
  end;

fun listKeys({compare,m}) = 
  let fun collect(E,L) = L
        | collect(T{key,left,right,...},L) = collect(left,key::(collect(right,L)))
  in
    collect(m,[])
  end;
    
fun listValues({compare,m}) = 
  let fun collect(E,L) = L
        | collect(T{key,value,left,right,...},L) = collect(left, value::(collect(right,L)))
  in
     collect(m,[])
  end
    
fun listKeyValuePairs({compare,m}) = 
  let fun collect(E,L) = L
        | collect(T{key,value,left,right,...},L) = collect(left,(key,value)::(collect(right,L)))
  in
     collect (m,[])
  end

fun applyToKeyValuePairs(f,{compare,m}) = 
  let fun app E = ()
        | app(T{key,value,left,right,...}) = (app left; f(key,value); app right)
  in
    app m
  end;

fun applyToValues(f,m) = applyToKeyValuePairs((fn (_,v) => f(v)),m)

fun applyToKeys(f,m) = applyToKeyValuePairs((fn (key,_) => f(key)),m)

    
fun mapToKeyValuePairs(f,{compare,m}) = 
  let fun mapFun(E) = E
        | mapFun(T{key,value,left,right,cnt}) = 
             let val left' = mapFun left
  		 val value' = f(key,value)
    		 val right' = mapFun right
             in
   	        T{cnt=cnt, key=key, value=value', left = left', right = right'}
	     end
       val m' = mapFun(m)
   in
      {compare=compare,m=m'}
   end;

fun mapToValues(f,m) = mapToKeyValuePairs(fn (_,v) => f(v),m);

    
fun foldl(f,init,{compare,m}) = 
  let fun fold (E,v) = v
        | fold (T{key,value,left,right,...},v) = fold (right, f(key, value, fold(left, v)))
  in
     fold(m,init)
  end;

end;