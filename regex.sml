functor MakeRE (type pat 
	        type value
		type constraint 
                val valEq: value * value -> bool 
		val patToString: pat -> string
		val constraintToString: constraint -> string
		val valToString: value -> string
		val getValCode: value -> real 
                val getListValues: value -> value list option 
                val patBindableIds: pat -> Symbol.symbol list
                val isValOfPat: pat -> Symbol.symbol option
		val constraintFreeIds: constraint -> Symbol.symbol list): RE =                

struct 

type symbol = Symbol.symbol

type value = value

type pat = pat

type constraint = constraint

open GeneralRE

type tag0 = constraint GeneralRE.tag0
type RE0 = (pat,constraint) GeneralRE.RE0

fun tagToString({name=SOME(s),con=NONE}:tag0) = "{name=SOME(" ^ (Symbol.name s) ^ "),constraint=NONE}"
  | tagToString({name=SOME(s),con=SOME(_)}:tag0) = "{name=SOME(" ^ (Symbol.name s) ^ "),constraint=SOME(_)}"
  | tagToString({name=NONE,con=NONE}:tag0) = "{name=NONE,constraint=NONE}"
  | tagToString({name=NONE,con=SOME(_)}:tag0) = "{name=NONE,constraint=SOME(_)}"

fun reToString(lit0(pat,t)) = "lit(" ^ (patToString pat) ^ ")"
  | reToString(any0(t)) = "any(" ^ (tagToString t) ^ ")"
  | reToString(null0(t)) = "null(" ^ (tagToString t) ^ ")"
  | reToString(backref0(s)) = "backref(" ^ (Symbol.name(s)) ^ ")"
  | reToString(range0(e1,e2,t)) = "range(" ^ (Real.toString e1) ^ ", " ^ (Real.toString e2) ^ "," ^ (tagToString t) ^ ")"
  | reToString(concat0(e1,e2,t)) = "concat(" ^ (reToString e1) ^ ", " ^ (reToString e2) ^ "," ^ (tagToString t) ^ ")"
  | reToString(union0(e1,e2,t)) = "union(" ^ (reToString e1) ^ ", " ^ (reToString e2) ^ ","  ^ (tagToString t) ^ ")"
  | reToString(star0(e,t)) = "star(" ^ (reToString e) ^ "," ^ (tagToString t) ^ ")"

val tt0:tag0 = {name=NONE,con=NONE}

fun concatLst0([e]) = e
  | concatLst0(e1::rest) = concat0(e1,concatLst0(rest),tt0)
  | concatLst0([]) = null0(tt0)

val concatLst = concatLst0
val tt = tt0

fun getSubstring(cl,start,count) = 
     let val stop = start + count 
         fun loop(i,res) = if i < stop then loop(i+1,(Unsafe.Array.sub(cl,i))::res) else rev(res)
     in
        loop(start,[])
     end

datatype RE = lit of pat * bool * tag
	    | any of tag
	    | diff of int 
            | empty of tag
            | backref of int 
            | concat of RE *  RE * tag
            | union of RE * RE * tag
            | range of real * real * tag
            | star of RE * tag
            | mark of int 
            | cc of constraint option * Symbol.symbol list

withtype tag = {code: int option, con: constraint option, free_ids: Symbol.symbol list} 

fun tagToString'({code=SOME(s),con=NONE,...}:tag) = "{code=SOME(" ^ (Int.toString s) ^ "),constraint=NONE}"
  | tagToString'({code=SOME(s),con=SOME(_),...}:tag) = "{code=SOME(" ^ (Int.toString s) ^ "),constraint=SOME(_)}"
  | tagToString'({code=NONE,con=NONE,...}:tag) = "{code=NONE,constraint=NONE}"
  | tagToString'({code=NONE,con=SOME(_),...}:tag) = "{code=NONE,constraint=SOME(_)}"

fun reToString'(lit(pat,_,t)) = "lit(" ^ (patToString pat) ^ "," ^ (tagToString' t) ^ ")"
  | reToString'(any(t)) = "any(" ^ (tagToString' t) ^ ")"
  | reToString'(empty(t)) = "empty(" ^ (tagToString' t) ^ ")"
  | reToString'(diff(i)) = "diff(" ^ (Int.toString(i)) ^ ")"
  | reToString'(backref(s)) = "backref(" ^ (Int.toString(s)) ^ ")"
  | reToString'(concat(e1,e2,t)) = "concat(" ^ (reToString' e1) ^ ", " ^ (reToString' e2) ^ "," ^ (tagToString' t) ^ ")"
  | reToString'(union(e1,e2,t)) = "union(" ^ (reToString' e1) ^ ", " ^ (reToString' e2) ^ ","  ^ (tagToString' t) ^ ")"
  | reToString'(range(e1,e2,t)) = "range(" ^ (Real.toString e1) ^ ", " ^ (Real.toString e2) ^ ","  ^ (tagToString' t) ^ ")"
  | reToString'(star(e,t)) = "star(" ^ (reToString' e) ^ "," ^ (tagToString' t) ^ ")"
  | reToString'(cc(SOME(constraint),fids)) = "checkConstraint( " ^ (constraintToString constraint) ^ " WITH free_ids: " ^ (Basic.printListStr(fids,Symbol.name,",")) ^ ")"
  | reToString'(cc(NONE,_)) = "checkConstraint(NONE)" 
  | reToString'(_) = ""

val inside_constraint = ref(false)

fun debugPrint(str) = if !inside_constraint then () else print(str) 

fun translate(e0,id_codes,all_ids) =     
  let fun getCode(name) = 
           (case Symbol.find(id_codes,name) of
               SOME(c) => c
             | _ => let val _ = print("\nFailed to find a code for name: " ^ (Symbol.name name))
                    in
		      raise Basic.Never 
                    end)
      fun getConFreeIds(SOME(con)) = List.filter (fn sym => Basic.isMemberEq(sym,all_ids,Symbol.symEq))
                                                 (constraintFreeIds con)
        | getConFreeIds(NONE) = []
      fun translateTag(t:tag0 as {name=SOME(name),con}) = 
                 let val t:tag = {code=SOME(getCode(name)),con=con,free_ids=getConFreeIds(con)}
                 in
                    t
                 end
        | translateTag(t:tag0 as {name=NONE,con}) = {code=NONE,con=con,free_ids=getConFreeIds(con)}
      fun f(lit0(p,t)) = lit(p,not(null(patBindableIds(p))),translateTag(t))
        | f(any0(t)) = any(translateTag(t))
        | f(null0(t)) = empty(translateTag(t))
        | f(backref0(s)) = backref(getCode(s))
        | f(concat0(e1,e2,t)) = concat(f(e1),f(e2),translateTag(t))
        | f(union0(e1,e2,t)) = union(f(e1),f(e2),translateTag(t))
        | f(range0(e1,e2,t)) = range(e1,e2,translateTag(t))
        | f(star0(e,t)) = star(f(e),translateTag(t))
   in
     f(e0)
   end

fun tagIds({name=SOME(n),...}:tag0,L) = n::L
  | tagIds(_,L) = L

fun getIdsOutsideStars(e0) =  
  let fun f(lit0(p,t),res) = 
             let val ids = (patBindableIds p)
             in
                (case t of
                   {name=SOME(n),...} => ids@(n::res)
                 | _ => ids@res)
             end
       | f(backref0(s),res) = s::res
       | f(concat0(e1,e2,t),res) = f(e2,f(e1,tagIds(t,res)))
       | f(union0(e1,e2,t),res) = f(e2,f(e1,tagIds(t,res)))
       | f(range0(e1,e2,t),res) = tagIds(t,res)
       | f(star0(e,t),res) = res
       | f(any0(t),res) = 
               (case t of
                   {name=SOME(n),...} => tagIds(t,res)
                 | _ => tagIds(t,res))
       | f(null0(t),res) = tagIds(t,res)
   in
     f(e0,[])
   end


fun getAllIds(e0) = 
  let fun f(lit0(p,t),res) = 
             let val ids = (patBindableIds p)
             in
                (case t of
                   {name=SOME(n),...} => ids@(n::res)
                 | _ => ids@res)
             end
       | f(backref0(s),res) = s::res
       | f(concat0(e1,e2,t),res) = f(e2,f(e1,tagIds(t,res)))
       | f(union0(e1,e2,t),res) = f(e2,f(e1,tagIds(t,res)))
       | f(range0(e1,e2,t),res) = tagIds(t,res)
       | f(star0(e,t),res) = f(e,tagIds(t,res))
       | f(any0(t),res) = 
               (case t of
                   {name=SOME(n),...} => tagIds(t,res)
                 | _ => tagIds(t,res))
       | f(null0(t),res) = tagIds(t,res)
   in
     f(e0,[])
   end

fun getIdsInsideStars(e0) =  
  let fun f(e as star0(_)) = getAllIds(e)
        | f(concat0(e1,e2,_)) = (f e1)@(f e2)
        | f(union0(e1,e2,_)) = (f e1)@(f e2)
        | f(_) = []
   in
     f(e0)
   end

fun getAllNames(e:RE0) = 
   let val H = Symbol.makeHTableWithInitialSize(20)
       fun isLit(lit0(_)) = true
         | isLit(_) = false 
       fun loop(lit0(p,t),res) = let val ids = (patBindableIds p)
                                     val _ = List.app (fn id => Symbol.insert(H,id,true)) ids
                                 in
                                    (case t of
                                        {name=SOME(n),...} => let val _ = Symbol.insert(H,n,true)
                                                              in
                                                                 ids@(n::res)
                                                              end
                                      | _ => ids@res)
                                 end
         | loop(backref0(s),res) = s::res
	 | loop(concat0(e1,e2,t),res) = loop(e2,loop(e1,tagIds(t,res)))
	 | loop(range0(e1,e2,t),res) = tagIds(t,res)
	 | loop(union0(e1,e2,t),res) = 
              if (isLit(e1) orelse isLit(e2))
                 then (case t of
                          {name=SOME(n),...} => (Symbol.insert(H,n,true);loop(e2,loop(e1,tagIds(t,res))))
                        | _ => loop(e2,loop(e1,tagIds(t,res))))
              else loop(e2,loop(e1,tagIds(t,res)))
	 | loop(star0(e,t),res) = loop(e,tagIds(t,res))
         | loop(any0(t),res) = 
               (case t of
                   {name=SOME(n),...} => (Symbol.insert(H,n,true);tagIds(t,res))
                 | _ => tagIds(t,res))
         | loop(null0(t),res) = tagIds(t,res)
   in
      (loop(e,[]),List.map (fn (name,_) => name) (Symbol.listItemsi H))
   end

fun getPatIdCodes(e,init_syms) = 
  let val (id_list_0,literal_ids) = getAllNames(e)
      val id_list = Basic.removeDuplicatesEq(init_syms@id_list_0,Symbol.symEq)
      val N = length(id_list)
      val H = Symbol.makeHTableWithInitialSize(50)
      val A = Array.array(N,Names.addition_symbol)
      val lit_codes = Array.array(N,false)
      val counter = ref(0)
      val _ = List.app (fn id => let val i = Basic.returnAndInc(counter)
                                     val _ = Symbol.insert(H,id,i)
                                     val _ = Array.update(A,i,id)
                                 in
                                    ()
                                 end)
                       id_list
      val _ = List.app (fn id => (case Symbol.find(H,id) of
                                     SOME(code) => Array.update(lit_codes,code,true)
                                   | _ => ()))
                       literal_ids
  in
     (id_list,H,A,N,lit_codes)
  end

fun getRange(A,start,count) = 
     let val stop = start + count 
         fun loop(i,res) = if i < stop then loop(i+1,(Unsafe.Array.sub(A,i))::res) else rev(res)
     in
        loop(start,[])
     end

val mem_table: (int,(Symbol.symbol list * Symbol.symbol list * (int Symbol.htable) * (Symbol.symbol Array.array) * int * (bool Array.array) * RE)) 
               HashTable.hash_table = HashTable.mkTable(Basic.hashInt, op=)  (200,Basic.Fail("Hash Error"))

fun match(e0:RE0,re_mem_code:int,
          L:value list,
          init_env: value Symbol.mapping, 
          matchPat:pat * value -> value Symbol.mapping option, 
          evaluateConstraint: (constraint * (Symbol.symbol list * value Symbol.mapping * Symbol.symbol list * value list Symbol.mapping)) -> bool,
          lookUpInOuterEnv: Symbol.symbol -> value option) = 
  let val (init_syms:Symbol.symbol list,
           all_ids:Symbol.symbol list,
           id_codes:(int Symbol.htable),
           code_ids: Symbol.symbol Array.array,
           code_count:int,
           lit_codes: bool Array.array,
           e:RE) = 
                (case (HashTable.find mem_table re_mem_code) of
                    SOME(res) => res
                  | _ => let val init_syms = if (Symbol.domainSize(init_env) < 1) then [] 
                                             else Symbol.listSymbolsInDomain(init_env)
                             val (all_ids,id_codes,code_ids,code_count,lit_codes) = getPatIdCodes(e0,init_syms)
                             val e:RE = translate(e0,id_codes,all_ids)
                             val res = (init_syms,all_ids,id_codes,code_ids,code_count,lit_codes,e)
                             val _ = (HashTable.insert mem_table (re_mem_code,res))
                         in
                            res
                         end)
(** 
     init_syms should really not be memoized. It's conceivable that in subsequent calls it might have
     different values. Then again, it should not be computed by Symbol.listSymbolsInDomain either.
     Pass the patBindableIds of the entire surrounding pattern as an extra argument (of type Symbol.symbol list)
     as an extra argument to the functor, and use that as the fixed value of init_syms. 
**)
      fun getCode(name) = 
           (case Symbol.find(id_codes,name) of
               SOME(c) => c)
      val id_values = Array.array(code_count,NONE)
      val N = List.length(L)
      val A = Array.fromList(L)
      val start_codes = Array.array(code_count,(true,~1))
      val end_codes = Array.array(code_count,~1)      
      fun markStart(code,i) = Array.update(start_codes,code,(false,i))
      fun markKleeneStart(code,i) = if #1(Array.sub(start_codes,code)) then Array.update(start_codes,code,(false,i)) else ()
      fun unmarkKleeneStart(code) = Array.update(start_codes,code,(true,#2(Array.sub(start_codes,code))))
      fun markEnd(code,i) = Array.update(end_codes,code,i)
      fun updateMaps(symbol_map: value Symbol.mapping) = 
               List.app (fn (s) => let (* val _ = print("\nLooking to update symbol: " ^ (Symbol.name s))  *)
                                   in
                                   (case Symbol.lookUp(symbol_map,s) of
                                        SOME(v) => let val code = getCode(s)
                                                   in
                                                      Array.update(id_values,code,SOME(v))
                                                   end
                                      | _ => ())
                                    end)
                        all_ids 
      val _ = updateMaps(init_env)
      fun getBindings(ids) = 
               let val list_value_map = Symbol.empty_mapping
                   val value_map = Symbol.empty_mapping
		   fun getListValues([],dom1,m,dom2,m_list) = (dom1,m,dom2,m_list)
                     | getListValues(id::rest,dom1,m,dom2,m_list) = 
                          let val code = getCode(id)
                              val (s,e) = (#2(Array.sub(start_codes,code)),Array.sub(end_codes,code))
			      val values = getRange(A,s,e-s)
                          in
                             if (s >= 0) andalso (e >= 0) then getListValues(rest,dom1,m,id::dom2,Symbol.enter(m_list,id,values))
                             else (case Array.sub(id_values,code) of
                                      SOME(v) => getListValues(rest,id::dom1,Symbol.enter(m,id,v),dom2,m_list)
                                    | _ => getListValues(rest,dom1,m,dom2,m_list))
                          end
               in
                 getListValues(ids,[],value_map,[],list_value_map)
               end
      fun getBindingsFinal() = 
               let val list_value_map = Symbol.empty_mapping
                   val value_map = Symbol.empty_mapping
		   fun isLitCode(c) = Array.sub(lit_codes,c)
		   fun getListValues([],dom1,m,dom2,m_list) = (dom1,m,dom2,m_list)
                     | getListValues(id::rest,dom1,m,dom2,m_list) = 
                          let val code = getCode(id)
                              val (s,e) = (#2(Array.sub(start_codes,code)),Array.sub(end_codes,code))
			      val len = e-s
                          in
                             if (s >= 0 andalso e >= 0) then 
                                (if (len = 1) andalso isLitCode(code)
                                 then getListValues(rest,id::dom1,Symbol.enter(m,id,Array.sub(A,s)),dom2,m_list) 
                                 else getListValues(rest,dom1,m,id::dom2,Symbol.enter(m_list,id,getRange(A,s,len))))
                             else (case Array.sub(id_values,code) of
                                      SOME(v) => getListValues(rest,id::dom1,Symbol.enter(m,id,v),dom2,m_list)
                                    | _ => getListValues(rest,dom1,m,dom2,m_list))
                          end
               in
                 getListValues(all_ids,[],value_map,[],list_value_map)
               end
      fun checkConstraint(NONE,_) = true
        | checkConstraint(SOME(c),fids) = 
                                  let val bindings as (dom1,m1,dom2,m2) = getBindings(fids)
                                      val _ = inside_constraint := true
                                      val res = evaluateConstraint(c,bindings)
                                      val _ = inside_constraint := false 
                                     in
                                       res
                                     end
      fun doRange([],i) = i
        | doRange(v::more,i) = if valEq(v,Unsafe.Array.sub(A,i)) then doRange(more,i+1) else ~1
      fun printStack(exps) = Basic.printListStr(exps,reToString'," | ")
      fun printSuffix(i) = if (i < N) then Basic.printListStr(map valToString (getRange(A,i,N-i)),fn x => x, ",") else "\"\""
      fun M([]:RE list,i:int) = i >= N
        | M((diff j)::more,i) = if (i = j) then false else M(more,i)
        | M((lit(p,has_pat_ids,tag as {code,con,free_ids,...}))::more,i) = 
             if (i >= N) then false 
             else 
                   (case matchPat(p,Array.sub(A,i)) of
                       SOME(mapping) => let val _ = if has_pat_ids then updateMaps(mapping) else ()
                                        in
                                           (case code of
                                              SOME(c) => let val _ = markStart(c,i) 
                                                             val _ = markEnd(c,i+1)
                                                         in
                                                            M((cc(con,free_ids))::more,i+1)
                                                         end
                                           | _ =>  M((cc(con,free_ids))::more,i+1))
                                         end
                    | _ => (case isValOfPat(p) of
                               SOME(name) => (case lookUpInOuterEnv(name) of 
                                                 SOME(v) => (case getListValues(v) of
                                                                SOME(vals) => let val j = doRange(vals,i)
                                                                              in
                                                                                 if j < 0 then false else M((cc(con,free_ids))::more,j)
                                                                              end 
                                                              | _ => if valEq(v,Array.sub(A,i)) then M((cc(con,free_ids))::more,i+1)
                                                                     else false)
                                               | _ => false)
                             | _ => false))
        | M(range(lo,hi,{code,con,free_ids,...})::more,i) = 
             if (i >= N) then false 
             else 
                 (case code of
                     SOME(c) => let val _ = markStart(c,i) 
                                    val _ = markEnd(c,i+1)
				    val current = getValCode(Array.sub(A,i))
                                in
                                   if (current <= hi andalso current >= lo) then
                                      M((cc(con,free_ids))::more,i+1)
                                   else
                                      false
                                end
                  | _ => let val current = getValCode(Array.sub(A,i)) 				   
                         in
                            if (current <= hi andalso current >= lo) then
                               M((cc(con,free_ids))::more,i+1)
                            else false
                         end)
        | M(mark(re_code)::more,i) = (markEnd(re_code,i);M(more,i))
        | M(cc(con,fids)::more,i) = if checkConstraint(con,fids) then M(more,i) else false
        | M(stack as ((se as star(e,{code=SOME(c),con,free_ids}))::more),i) = 
                let val _ = markKleeneStart(c,i)
  	            val _ = markEnd(c,i)
                    val res = M((cc(con,free_ids))::more,i) orelse M(e::(diff i)::se::more,i)
		    val _ = unmarkKleeneStart(c)
                in
                   res 
                end
        | M(stack as (se as star(e,{code=NONE,con,free_ids,...}))::more,i) = 
                 let  (****
                      val _ = debugPrint("\n\nUNTAGGED STAR Stack: [" ^ (printStack stack) ^ "]")
                      val _ = debugPrint("\nUNTAGGED STAR Value list: " ^ (printSuffix i)) 
                      ****)
                 in
                    M((cc(con,free_ids))::more,i) orelse   M(e::(diff i)::se::more,i)
                 end
        | M((choise as union(e1,e2,{code=NONE,con,free_ids,...}))::more,i) = 
                 M(e1::(cc(con,free_ids))::more,i) orelse M(e2::(cc(con,free_ids))::more,i)
        | M((choise as union(e1,e2,{code=SOME(c),con,free_ids,...}))::more,i) = 
             let val _ = markStart(c,i)
		 val left = M(e1::(mark(c))::(cc(con,free_ids))::more,i)
             in 
               left  orelse M(e2::(mark(c))::(cc(con,free_ids))::more,i)
             end
        | M((e as concat(e1,e2,{code=SOME(c),con,free_ids,...}))::more,i) =
           let val _ = markStart(c,i)
           in
              M(e1::e2::(mark(c))::(cc(con,free_ids))::more,i)
           end
        | M((e as concat(e1,e2,{code=NONE,con,free_ids,...}))::more,i) = M(e1::e2::(cc(con,free_ids))::more,i)
        | M(stack as (any({code,con,free_ids,...})::more),i) = 
             if (i >= N) then false 
             else 
                 (case code of
                     SOME(c) => let val _ = markStart(c,i) 
                                    val _ = markEnd(c,i+1)
                                in
                                   M((cc(con,free_ids))::more,i+1)
                                end
                  | _ =>  M((cc(con,free_ids))::more,i+1))
        | M((backref re_code)::more,i) = 
	     let val s = #2(Array.sub(start_codes,re_code))
                 val e = Array.sub(end_codes,re_code)	
	         val len = e-s
		 val (value_list,len) = 
                          if (e >= 0) then let val length = e-s in (getRange(A,s,length),length) end
                                  else (case Array.sub(id_values,re_code) of
                                          NONE => ([],~1)
                                        | SOME(value) => ([value],1))
             in 
                if len < 0 orelse len > (N - i) then false 
                else let val j = doRange(value_list,i)
                     in
                        if j < 0 then false else M(more,j)
                     end
             end	    
        | M(empty({code,con,free_ids,...})::more,i) = 
                 (case code of
                     SOME(c) => let val _ = markStart(c,i) 
                                    val _ = markEnd(c,i)
                                in
                                   M((cc(con,free_ids))::more,i)
                                end
                  | _ =>  M((cc(con,free_ids))::more,i))
     val t1 = Time.toReal(Time.now())         
     val res = M([e],0)
     val t2 = Time.toReal(Time.now())         
  in
    if res then SOME(getBindingsFinal(),Real.-(t2,t1)) else NONE
  end

end


structure TestRE = 
struct

val empty_mapping_opt: char Symbol.mapping option = SOME(Symbol.empty_mapping)

fun baseMatch(c1,c2) = if c1 = c2 then empty_mapping_opt else NONE

structure RE = MakeRE(type pat = char 
                      type value = char
                      type constraint = (value list Symbol.mapping) -> bool 
                      val patToString = Char.toString
                      val constraintToString = (fn _ => "")
                      val valToString = Char.toString
                      val getValCode = (fn c => Real.fromInt(Char.ord(c)))
		      val valEq = op=
                      val getListValues = (fn _ => NONE)
                      val patBindableIds = (fn _ => [])
                      val isValOfPat = (fn _ => NONE)
		      val constraintFreeIds = (fn _ => []))


open RE

open GeneralRE

fun ls(str) = 
  let val cl = explode(str)
  in
     concatLst(map (fn c => lit0(c,tt)) cl)
  end
  
fun test(e,str,show,msg) = 
  let val cl = explode(str)
      fun evaluateConstraint(c,(dom1,val_m,dom2,list_val_map)) = c(list_val_map)
      val res = match(e,~1,cl,Symbol.empty_mapping,baseMatch, evaluateConstraint,fn _ => NONE)
  in
     (case res of
         SOME((dom1,v_map,dom2,vl_map),time) => 
             let val _ = print("\nThe matching " ^ (if msg = "" then "" else " for ") ^ msg ^ " took " ^ (Real.toString(time)) ^ "\nseconds...\n")
                 val _ = if show then 
                            (List.app (fn (s,cl) => print("\nId " ^ (Symbol.name s) ^ " --> " ^ (implode cl) ^ "\n")) 
                                      (Symbol.listSymbolsAndImages(vl_map)))
                         else 
                            (List.app (fn (s,cl) => let val str = if length(cl) < 1000 then (implode cl) else " --> a list of length " ^ (Int.toString(length(cl)))
                                                    in
                                                       print("\nId " ^ (Symbol.name s) ^ " --> " ^ str ^ "\n")
                                                    end)
                                      (Symbol.listSymbolsAndImages(vl_map)))
            in
                ()
            end
       | _ => print("\n\nMatch failed!\n\n"))
  end

val s5_list = (map (fn _ => #"a") (Basic.fromI2N(1,500)))
val s5 = implode(s5_list)

(************************************* Test 1 *************************************)

val constraint = (fn (list_value_map) => 
                        let val res = (case Symbol.lookUp(list_value_map,Symbol.symbol("x")) of
                                        SOME(char_list) => (length(char_list) > 100)
                                      | _ => false)
                        in
                           res
                        end)

val e = star0(ls("a"),{name=SOME(Symbol.symbol("x")),con=SOME(constraint)})
val e1 = concatLst([e,ls("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")])

(**
val _ = test(e,s5,false," for a* of 5M (functor version)")
**)

(************************************* Test 2 *************************************)

val e = star0(union0(ls("a"),ls("b"),{name=SOME(Symbol.symbol("x")),con=NONE}),tt)

(**
val _ = test(e,s5,false,"the union a + b over 5M a's (functor version)")
**)

(************************************* Test 3 *************************************)

fun anything(name) = star0(any0(tt),{name=SOME(Symbol.symbol(name)),con=NONE})

val e = concatLst([anything("x0"),ls("<header>"),anything("x1"),ls("</header>"),anything("x2"),ls("<body>"),anything("x3"),ls("</body>"),anything("x4")])
val pre = s5_list 
val middle = explode("middle")
val tail = rev(s5_list)
val str =  pre @ (explode("<header>This is my header</header>")) @ middle @ (explode("<body>This is my body!!</body>")) @ tail
(**
val _ = test(e,implode(str),false," the header/body XML stuff (functor version)")
**)

(************************************* Test 5 *************************************)

val any_char = any0(tt)
val e = concatLst([any0({name=SOME(Symbol.symbol("c")),con=NONE}), 
                   any0({name=SOME(Symbol.symbol("d")),con=NONE})])

(**
val _ = test(e,"aa",false,"the 2 a's")
**)

end