(*======================================================================

This file implements code that is used in sort inference with ordered sorts
(i.e., in the presence of subsorting), such as computing the LUB and/or GLB
(least upper bound/greatest lower bound) of two sorts. 

=======================================================================*)

structure SortOrder = 

struct 

structure MS = ModSymbol

type ath_domain = {name:MS.mod_symbol,arity:int,index:int} 

val sort_table: ath_domain MS.htable = MS.makeHTable()

val sort_index = ref 0

val sort_increment = 16

val domain_max = ref sort_increment

type sort_matrix = {matrix: (MS.mod_symbol * MS.mod_symbol * bool) array array, n:int}

fun matrixSize({n,...}:sort_matrix) = n

val dummy_modsym = ModSymbol.dum_modsym("")

fun makeSortMatrix(n) = 
     let val true_entry = (dummy_modsym,dummy_modsym,true)
	 val false_entry = (dummy_modsym,dummy_modsym,false)
         val v = Array.array(n,false_entry)
         val rows = Array.array(n,v)
         fun f(i) = if i < n then (Array.update(rows,i,Array.array(n,false_entry));f(i+1)) else ()
         val _ = f(0)
	 fun setDiagonal(i) = if i < n then (Array.update(Array.sub(rows,i),i,true_entry);setDiagonal(i+1)) else ()
         val _ = setDiagonal(0)
     in
        {matrix=rows,n=n}:sort_matrix 
     end

fun setSortMatrix({matrix,n}:sort_matrix,i,j,v as (s1,s2,b)) = 
	  if (i <= n) andalso (j <= n) then 
	     Array.update(Array.sub(matrix,i-1),j-1,v)
	  else Basic.fail("\nInvalid sort matrix subscripts.");

fun subSortMatrix({matrix,n}:sort_matrix,i,j) = 
	  if (i <= n) andalso (j <= n) then 
	     Array.sub(Array.sub(matrix,i-1),j-1)
	  else  Basic.fail("\nInvalid sort matrix subscripts.")

val global_sort_matrix = ref(makeSortMatrix(!domain_max)) 

val order_sorted_array = ref(Array.array((!domain_max)+1,false))

fun getBit(_,_,b) = b

fun checkGlobalSortMatrix(pos) = 
  let val M = !global_sort_matrix
      val size = matrixSize(M)
      fun check(i,j) = let val (s1,s2,b) = subSortMatrix(M,i,j)
                           val (_,_,b') =  subSortMatrix(M,j,i)
		       in
			  if (b andalso b') then  
			     (print(Util.makeErrorMessage("Cyclic subsorts detected: "^(ModSymbol.name(s1))^" and "^(ModSymbol.name(s2))^
					  " are subsorts of each other.\n",
				          SOME(pos)));
			      Util.killAthena())
			   else ()
		       end 
      fun checkRow(i) = 
           let fun checkCol(j) = if (j > size) then ()
				 else  
				    if j <= i then checkCol(j+1) else 
   				       (check(i,j);checkCol(j+1))
           in
              checkCol(1)
           end
      fun loop(i) = if i > size then () else (checkRow(i);loop(i+1))
  in
     loop(1)
  end
				
fun warshallTransitiveClosure(M as {matrix,n}:sort_matrix) = 
  let fun f((s1,s2,b1),v2,v3) = (s1,s2,b1 orelse (getBit(v2) andalso getBit(v3)))
  in
     Basic.repeat n 
       (fn (k) => Basic.repeat n 
         (fn (i) => Basic.repeat n
           (fn (j) => setSortMatrix(M,i,j,f(subSortMatrix(M,i,j),subSortMatrix(M,i,k),subSortMatrix(M,k,j))))))
  end
    
fun setSortName(i,name) =
  let val M as {matrix,n} = !global_sort_matrix
  in
     (Basic.repeat n 
       (fn j => let val (s1,s2,b) = subSortMatrix(M,i,j)
		in  
		   setSortMatrix(M,i,j,(name,s2,b))
		end);
      Basic.repeat n
	(fn r => let val (s1,s2,b) = subSortMatrix(M,r,i)
                 in
		    setSortMatrix(M,r,i,(s1,name,b))
		 end))
   end

fun printSortMatrix() = 
  let val M as {matrix,n} = !global_sort_matrix
  in  
     Basic.repeat n 
       (fn i => Basic.repeat n 
         (fn j => let val (s1,s2,b) = subSortMatrix(M,i,j)
		      val _ = print("\nIndex ("^(Int.toString(i))^","^Int.toString(j)^")\n")
		      val _ = print("\nThat's domain "^(ModSymbol.name(s1))^" and domain "^(ModSymbol.name(s2))^", respectively.\n")
		  in 
		     if not(ModSymbol.modSymEq(s1,dummy_modsym)) andalso not(ModSymbol.modSymEq(s2,dummy_modsym)) then
			print("\n"^(ModSymbol.name(s1))^" subsort of "^(ModSymbol.name(s2))^": "^(if b then "true\n" else "false\n"))
		     else ()
		  end))
   end
    
fun expandSubsortMatrix () = 
     let val old_size = (!domain_max)
	 val old_matrix = !global_sort_matrix
	 val _ = domain_max := (!domain_max) + sort_increment;
         val _ = global_sort_matrix := makeSortMatrix(!domain_max)
	 val old_order_sorted_array = !order_sorted_array
	 val _ =  order_sorted_array := Array.array((!domain_max)+1,false)
         val _ = Basic.repeat old_size
		  (fn i =>  Array.update(!order_sorted_array,i,Array.sub(old_order_sorted_array,i)))
	 val _ = Basic.repeat old_size 
		  (fn i => Basic.repeat old_size
		    (fn j => setSortMatrix(!global_sort_matrix,i,j,subSortMatrix(old_matrix,i,j))))
	val _ = Basic.repeat old_size
		  (fn i => let val (s1,_,_) = subSortMatrix(old_matrix,i,1)
			   in
			      setSortName(i,s1)
			   end)
     in
        ()
     end

fun getDomainIndex(dom_name) = 
      (case MS.find(sort_table,dom_name) of  
          SOME({index,...}) => SOME(index)
        | _ => NONE)

fun areSubsorts(sym1,sym2) = 
	MS.modSymEq(sym1,sym2) orelse  
	(case (getDomainIndex(sym1),getDomainIndex(sym2)) of
  	    (SOME(i1),SOME(i2)) => getBit(subSortMatrix(!global_sort_matrix,i1,i2))
          | _ => false)

fun upperBounds(dom1,dom2) = 
    let val M as {matrix,n} = !global_sort_matrix
    in 
        (case (getDomainIndex(dom1),getDomainIndex(dom2)) of
            (SOME i1,SOME i2) => Basic.filter((Basic.firstNumbersFast(1,n)),
	    			              (fn j =>  getBit(subSortMatrix(M,i1,j)) andalso
					                getBit(subSortMatrix(M,i2,j))))
          | _ => [])
    end

fun lowerBounds(dom1,dom2) = 
    let val M as {matrix,n} = !global_sort_matrix
    in
        (case (getDomainIndex(dom1),getDomainIndex(dom2)) of
            (SOME j1,SOME j2) =>  Basic.filter((Basic.firstNumbersFast(1,n)),
				               (fn i =>  getBit(subSortMatrix(M,i,j1)) andalso  
							 getBit(subSortMatrix(M,i,j2))))
	  | _ => [])
     end

fun lub(dom1,dom2) = 
   if MS.modSymEq(dom1,dom2) then SOME(dom1)
   else 
   let val upper_bounds = upperBounds(dom1,dom2)
   in
         (case Basic.constructiveExists(upper_bounds,
	    fn i => (Basic.forall(upper_bounds,fn j => getBit(subSortMatrix(!global_sort_matrix,i,j))))) of
          SOME(i) => SOME(#1(subSortMatrix(!global_sort_matrix,i,1)))
        | _ => NONE)
   end   

fun diffGlb(dom1,dom2) = 
(* This function presupposes that dom1 and dom2 are *different* domains, *)
(* i.e., that not(MS.modSymEq(dom1,dom2)). 			         *)

   let val lower_bounds = lowerBounds(dom1,dom2)
   in
      (case Basic.constructiveExists(lower_bounds,
          fn j => (Basic.forall(lower_bounds,fn i => getBit(subSortMatrix(!global_sort_matrix,i,j))))) of
          SOME(j) => SOME(#1(subSortMatrix(!global_sort_matrix,j,j)))
        | _ => NONE)
   end

fun glb(dom1,dom2) = if MS.modSymEq(dom1,dom2) then SOME(dom1) else diffGlb(dom1,dom2)
   
fun isOrderSorted1(i) = Array.sub(!order_sorted_array,i)

fun isOrderSorted(sort_symbol) = 
		(case MS.find(sort_table,sort_symbol) of  
	            SOME({index,arity,...}) => if (Array.sub(!order_sorted_array,index)) then 
						  (if arity > 0 then 2 else 1)
					       else 0
                  | _ => 0)

fun organize(sorts) = 
  let fun test(s1,s2) = (case (getDomainIndex(s1),getDomainIndex(s2)) of
   	                    (SOME(i1),SOME(i2)) => if getBit(subSortMatrix(!global_sort_matrix,i1,i2)) then [(s1,s2)]
                                                   else if getBit(subSortMatrix(!global_sort_matrix,i2,i1)) then [(s2,s1)] else []
                          | _ => [])
      fun compareAgainst(s,[],res) = res
        | compareAgainst(s,t::more,res) = compareAgainst(s,more,(test(s,t))@res)
      fun f([],res) = res
        | f(s::more,res) = f(more,(compareAgainst(s,more,[]))@res)
  in f(sorts,[]) end
                             
end

     
