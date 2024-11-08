(*======================================================================

Implementation of the functionality specified in base.sig.

=======================================================================*)

structure Basic : BASIC = 
struct

exception Fail of string
exception FailLst of string list

infix !=              

fun a != b = not(a = b)

fun zip(x::xs,y::ys) = (x,y)::zip(xs,ys) 
  | zip _ = [] 

fun unZip [] = ([],[])
  | unZip ((a,b)::rest) = 
       let val (tail1,tail2) = unZip(rest) 
       in
          (a::tail1,b::tail2)
       end

fun bool2Str(b) = if b then "true" else "false"

exception Never

fun never() = raise Never

fun pow(n,k) = 
   let fun f(k,res) = if k = 0 then res else f(Int.-(k,1),Int.*(n,res))
   in
     f(k,1)
   end

fun listEq([],[],_) = true
  | listEq(x::more1,y::more2,eq) = if eq(x,y) then listEq(more1,more2,eq) else false
  | listEq _ = false

fun allEqual(L) = 
 let fun f([]) = true
       | f(x::rest) = List.all (fn y => x = y) rest
 in f L end

fun fromI2N(i,j) = 
     let fun f(k,res) = if k < i then res else f(k-1,k::res)
     in 
        if i > j then [] else f(j,[])
     end
    
fun inc(n) = n := !n + 1

fun incAndReturn(n) = (n := !n + 1;!n)

fun returnAndInc(n) = let val res = !n  
                          val _ = n := !n + 1
                      in res end

fun dec(n) = n := !n - 1

fun foldr(f,init,[]) = init 
  | foldr(f,init,x::xs) = f(x,foldr(f,init,xs)) 

fun filter(l,f) = List.filter f l 

fun filterOut(l,f) = List.filter (fn x => not(f(x))) l

val nth = List.nth

fun exists(l,pred) = List.exists pred l

fun forall(l,pred) = List.all pred l

fun countAll(L,pred) = 
  let fun f([],res) = res
        | f(x::more,res) = if pred(x) then f(more,res+1) else f(more,res)
  in f(L,0) end

fun constructiveExists([],pred) = NONE 
  | constructiveExists(x::rest,pred) = if pred(x) then SOME(x) else constructiveExists(rest,pred)

fun take(L,n) = 
      let fun loop([],_,res) = res
            | loop(x::more,i,res) = if i < n then loop(more,i+1,x::res) else res
      in
         rev(loop(L,0,[]))
      end

fun takeAndSplit(L,n) = 
      let fun loop([],_,res,remainder) = (rev res,remainder)
            | loop(x::more,i,res,remainder) = if i < n then loop(more,i+1,x::res,more) else (rev res,x::more)
      in
         loop(L,0,[],L)
      end

val findInList = constructiveExists   

fun findInListCont(L,pred,success,failure) = 
      let fun loop([]) = failure()
            | loop(x::more) = if pred(x) then (success x) else loop(more)
      in
        loop(L)
      end
       
fun decomposeNth(L,n) = 
      let fun loop(L,L',i,ith) = (case (i,L) of 
                                    (1,x::rest) => loop(rest,L',i-1,SOME(x))
                                  | (_,x::rest) => loop(rest,x::L',i-1,ith)
                                  | (_,[]) => (ith,L'))
      in
         loop(L,[],n,NONE)
      end

fun merge(L1,L2,less) = 
         let fun M(x::xs,y::ys) = if less(y,x) then y::M(x::xs,ys) else x::M(xs,y::ys)
               | M([],ys) = ys
               | M(xs,[]) = xs
         in 
           M(L1,L2)
        end

fun isSorted(L,less) = let val positions = fromI2N(1,length(L)-1)
                       in 
                         List.all (fn i => less(nth(L,i),nth(L,i+1))) positions
                       end

fun mergeSort(L,less) =
      let fun mergepairs(ls as [l], k) = ls
            | mergepairs(l1::l2::ls,k) =
                if k mod 2 = 1 then l1::l2::ls
                else mergepairs(merge(l1,l2,less)::ls, k div 2)
            | mergepairs _ = raise Never
          fun nextrun(run,[])    = (rev run,[])
            | nextrun(run,x::xs) = if less(hd run,x) then nextrun(x::run,xs)
                                   else (rev run,x::xs)
          fun samsorting([], ls, k)    = hd(mergepairs(ls,0))
            | samsorting(x::xs, ls, k) = let 
                val (run,tail) = nextrun([x],xs)
                in samsorting(tail, mergepairs(run::ls,k+1), k+1)
                end
          in 
            case L of [] => [] | _ => samsorting(L, [], 0)
          end

fun mergeSortBuiltIn(L,less) = (ListMergeSort.sort less L)

(** Built-in merge sort but with a complemented comparison predicate: **)

fun mergeSortBuiltInComp(L,less) = 
      let fun less'(x,y) = not(less(x,y))
      in
          ListMergeSort.sort less' L
      end
      
fun decomposeList(lst,f) = 
  let fun loop([],_) = NONE
        | loop(x::more,left) = if f(x) then SOME(rev left,x,more) else loop(more,x::left)
  in
     loop(lst,[])
  end

fun prefix([],_) = true 
  | prefix(a::t1,b::t2) = if (a = b) then prefix(t1,t2) else false 
  | prefix _ = false

fun prefixEq([],_,_) = true 
  | prefixEq(a::t1,b::t2,eq) = if eq(a,b) then prefixEq(t1,t2,eq) else false 
  | prefixEq _ = false

fun nonEmptyCommonprefixEq(L1,L2,eq) = 
       if null(L1) orelse null(L2) then false
       else eq(hd(L1),hd(L2)) 

fun suffix(l1,l2) = prefix(l2,l1)

fun chop_prefix(l,0) = l |
    chop_prefix(a::rest,i) = chop_prefix(rest,i-1) |
    chop_prefix([],i) = []

val id = fn x => x

fun flatten([]) = [] |
    flatten(l::ls) = l @ flatten ls

fun isMember(a,lst) = if null(lst) then false else 
                      if a = hd(lst) then true else isMember(a,tl(lst))
                          
fun isMemberEq(a,l,eq) = 
    let fun check([]) = false 
          | check(x::rest) = eq(a,x) orelse check(rest)
        in
          check(l)
    end

fun removeDuplicatesEq(l,eq) = 
    let fun remove(non_dups,[]) = non_dups
          | remove(non_dups,x::xs) = if isMemberEq(x,non_dups,eq) then
                                        remove(non_dups,xs)
                                     else
                                        remove(x::non_dups,xs)
        in
           remove([],l)
    end

fun hasDuplicates(l,eq) = List.length(removeDuplicatesEq(l,eq)) < List.length(l)

(* The function remove(x,lst) removes all occurences of element x from list lst *)
(* Note that list order is NOT preserved. Only use for set-like lists.          *)
(* The same goes for removeEq.                                                  *)

fun remove(a,l) =
  let fun r([],res) = res
        | r(x::more,res) = if a = x then r(more,res) else r(more,x::res)
  in r(l,[]) end

fun removeAll(L1,L2) = 
       let fun loop([],res) = res
             | loop(x::more,res) = loop(more,remove(x,res))
       in
           loop(L1,L2)
       end


fun removeEq(x,l,eq) = 
    let fun remove([],res) = res
          | remove(y::ys,res) = if eq(x,y) then remove(ys,res) else remove(ys,y::res)
        in
          remove(l,[])
    end

fun removeAllEq(L1,L2,f) = 
       let fun loop([],res) = res
             | loop(x::more,res) = loop(more,removeEq(x,res,f))
       in
           loop(L1,L2)
       end

(* removeAndCheckMemEq also does not preserve order: *)

fun removeAndCheckMemEq(x,l,eq) = 
     let fun remove([],res,flag) = (res,flag)
           | remove(y::ys,res,flag) = if eq(x,y) then remove(ys,res,true) else remove(ys,x::res,flag)
     in
        remove(l,[],false)
     end

(** 
  findAndSplit(L,pred) returns (SOME(x),L'), where x is the first (leftmost) element of L 
  that satisfies pred, and L' is L with all occurrences of x removed - if such x exists in L.
  If L does not contain any elements satisfying pred, then (NONE,L) is returned.
**)

fun findAndSplit(L,pred,equality) = 
  let fun f([],rem) = (NONE,L)
        | f(x::rest,so_far) = if pred(x) then (SOME(x),(rev so_far)@(removeEq(x,rest,equality)))
                              else f(rest,x::so_far)
  in 
      f(L,[])
  end

fun readFileLines(fname) = 
   let val s = TextIO.openIn(fname)
       fun getLines(res) = 
                let val line = TextIO.inputLine(s) 
		in
		   if line = "" then rev(res) else getLines(line::res)
		end
       val res = getLines([])
       val _ = (TextIO.closeIn(s)) handle _ => ()
   in
      res 
   end

fun toLower(str) = String.map Char.toLower str

fun toUpper(str) = String.map Char.toUpper str

fun readLine() = TextIO.inputLine(TextIO.stdIn)

fun printable(c) = (Char.ord(c) > 32) andalso (Char.ord(c) < 128)

fun promptAndReadLine(msg) = (print(msg);TextIO.inputLine(TextIO.stdIn))

fun stripLast(str) = 
   let val sz = String.size(str) 
   in
     if sz < 2 then "" else String.extract(str,0,SOME(sz-1))                         
   end

fun subsetEq([],_,meq) = true |
    subsetEq(a::rest,l,meq) = isMemberEq(a,l,meq) andalso subsetEq(rest,l,meq)

fun maxLst(lst) = let fun f([],m) = m
                        | f(x::rest,m) = f(rest,Int.max(x,m))
                  in
                     f(lst,0)
                  end

fun listReplace([],_,_) = []
  | listReplace(x::rest,i,y) = if i = 0 then y::rest else x::(listReplace(rest,i-1,y))

fun firstNumbersFast(start,n) = 
      let fun f(_,0,res) = res
            | f(start,n,res) = f(start+1,n-1,start::res)
      in
         f(start,n,[])
      end
               
fun isDigit(c) = Char.isDigit(c)

fun doubleMap(f,g,l) = List.map (f o g) l

fun writeString(s,A,i) = 
      let val max = i + String.size(s)
          fun loop(i) = if i < max then 
                           let val _ = Array.update(A,i,String.sub(s,i))
                           in 
                             loop(i+1)
                           end
                        else i
      in 
        loop(i)
      end

fun joinStrings([]) = ""
  | joinStrings(s::more) = s ^ (joinStrings(more))

fun joinStringsNL([]) = ""
  | joinStringsNL(s::more) = s ^ "\n" ^ (joinStrings(more))

fun writeLinesToFile(lines:string list,file_name) = 
     let val stream = TextIO.openOut(file_name)
         val _ = List.app (fn l => TextIO.output(stream,l)) lines
     in
        TextIO.closeOut(stream)
     end

fun findEnding([],content) = (rev(content),[],true)
  | findEnding(#"@"::more,content) = (rev(content),more,false)
  | findEnding(c::more,content) = findEnding(more,c::content)

val slash = Char.chr(92)
val lb = Char.chr(123)
val rb = Char.chr(125)
val smtt = [slash,#"s",#"m",#"t",#"t",lb]

fun f([],so_far) = implode(rev(so_far))
 |  f(chars as #"@"::rest,so_far) = 
       let val (content,true_rest,missing) = findEnding(rest,[])
       in
        if missing then implode((rev(so_far))@chars)
        else 
         f(true_rest,(rev(smtt@content@[rb]))@so_far)
       end       
 |  f(c::rest,so_far) = f(rest,c::so_far)

fun replace(str) = f(explode(str),[])

fun replaceFile(in_file_name,out_file_name) = 
   let val lines = readFileLines(in_file_name)
       val lines' = map replace lines
   in
     writeLinesToFile(lines',out_file_name)
   end

fun arrayToList(A) = Array.foldr op:: [] A

fun makeTailList(A,i) = 
      let val len = Array.length(A)
          fun loop(index,res) = if index >= len then rev(res) else loop(index+1,(Array.sub(A,i))::res)
      in
         loop(i,[])
      end

fun findInArray(pred,A) = 
     let val len = Array.length(A)
         fun loop(i) = if i >= len then NONE
                       else let val x = Array.sub(A,i)
                            in
                               if pred(x) then SOME(i,x) else loop(i+1)
                            end
     in
        loop(0)
     end

fun printListStr(lst,f,str) = 
     let fun p([],res) = String.concat(rev res)
           | p([x],res) = String.concat(rev((f x)::res))
           | p(x::more,res) = p(more,str::(f x)::res)
     in p(lst,[]) end

fun printListStrCommas(lst,f) = printListStr(lst,f,", ") 

fun printSExpListStr(lst,f) = 
     let fun p([],res) = String.concat(rev res)
           | p([x],res) = String.concat(rev((f x)::res))
           | p(x::more,res) = p(more," "::(f x)::res)
     in p(lst,[]) end

fun printLnListStr(lst,f) = 
     let fun p([],res) = String.concat(rev res)
           | p([x],res) = String.concat(rev((f x)::res))
           | p([x,y],res) = String.concat(rev((f y)::" and "::(f x)::res))
           | p([x,y,z],res) = let val L = (f z)::", and "::(f y)::", "::(f x)::[]
                              in
                                String.concat(rev(L@res))
                              end
           | p(x::more,res) = p(more,", "::(f x)::res)
     in p(lst,[]) end

fun printList(lst,f) = print(printListStrCommas(lst,f))

fun printSExpList(lst,f) = print(printSExpListStr(lst,f))

fun printLnList(lst,f) = print(printLnListStr(lst,f))

val concatStrings = String.concat

fun writeStringToCharArray(s,A:CharArray.array,i) = 
      let val max = String.size(s)
          fun loop(j) = if j < max then 
                           let val _ = CharArray.update(A,i+j,String.sub(s,j))
                           in 
                             loop(j+1)
                           end
                        else i+j
      in 
        loop(0)
      end

fun timeIt(f) = let val t1:Real.real = Time.toReal(Time.now())
                    val _ = f()
                    val t2:Real.real = Time.toReal(Time.now())
                in
                   Real.-(t2,t1)
                end
 
fun continue() = (print("\nPress return to continue...");readLine();print "\n")

val new_line = "\n"

val isPrintable = Char.isPrint
val isAlpha = Char.isAlpha
val isDigit = Char.isDigit
val isAlphaNum = Char.isAlphaNum
val isWhiteSpace = Char.isSpace

fun skipWhiteSpace([]) = [] 
  | skipWhiteSpace(clist as (c::rest)) = if isWhiteSpace(c) then skipWhiteSpace(rest) else clist

fun skipAll([],pred) = []
  | skipAll(L as (x::rest),pred) = if (pred x) then skipAll(rest,pred) else L

fun skipAllAndReturnCount(L,pred) = 
   let fun skip([],count) = count 
         | skip(lst as (x::rest),count) = 
                if (pred x) then skip(rest,count+1) else count
   in
     skip(L,0)
   end

fun skipUntilRev(L,pred) = 
     let fun loop([],res) = (res,[])
           | loop(L as (x::more),res) = if pred(x) then (res,L) else loop(more,x::res)
     in
        loop(L,[])
     end

fun skipUntil(L,pred) = 
     let fun loop([],res) = (rev(res),[])
           | loop(L as (x::more),res) = if pred(x) then (rev(res),L) else loop(more,x::res)
     in
        loop(L,[])
     end

fun skipUntilWithExtendedPred(L,pred1,pred_rest) = 
     let fun loop([],res) = (res,[])
           | loop(L as (x::more),res) = if pred1(x) andalso pred_rest(more) then (res,L) else loop(more,x::res)
     in
        loop(L,[])
     end

fun firstPastwhiteSpace(str) = 
      let val len = String.size(str)
          fun f(i) = if i < len andalso isWhiteSpace(String.sub(str,i)) then f(i+1) else 
                     (if i < len then i else ~1)
      in f(0) end

fun firstPast(str,pred) = 
      let val len = String.size(str)
          fun f(i) = if i < len andalso pred(String.sub(str,i)) then f(i+1) else 
                     (if i < len then i else ~1)
      in 
          f(0) 
      end

fun firstPastwhiteSpace(str) = firstPast(str,Char.isSpace)

fun isThereLineThatStartsWith(in_stream,l) = 
  let val n = String.size(l)
      fun loop(lines_read) =  
             let val line = TextIO.inputLine(in_stream)  
                 val index = firstPastwhiteSpace(line)
                 val line' = if index < 0 then "" else String.extract(line,index,NONE)
                 fun isSuffix(str) = (String.isPrefix l str) andalso Int.>=(String.size(str),n + 1) andalso isWhiteSpace(String.sub(str,n))
             in
                if line = "" then (false,lines_read+1) else 
                (if isSuffix(line') then (true,lines_read+1) else loop(lines_read+1))
             end
  in 
    loop(0)
  end

fun findAndSkipLine(in_stream,l) = 
   let fun loop() = let val line =  TextIO.inputLine(in_stream)
                    in
                       if line = "" then []
                       else (if line = l then explode(TextIO.inputAll(in_stream)) else loop())
                    end
   in loop() end

val allAfter = findAndSkipLine

fun spaces(i) = 
   let fun f(i,res) = if Int.<(i,1) then String.concat(res) else f(i-1," "::res)
   in f(i,[])
   end

fun charToWord c = Word.fromInt(Char.ord c)

fun hashChar(c,seed) = Word.<<(seed,0w5) + seed + 0w720 + (charToWord c)

fun hashAccum(str,seed,n) =    (CharVector.foldl hashChar seed str,n+String.size(str))

fun hashAccumInt(i:int,seed,n) = (Word.<<(seed,0w5) + Word.fromInt(i) + 0w720,n+1)

fun hashInt(i:int) = Word.fromInt(i)

fun hashTwoWords(w1,w2) = 
      Word.<<(w1,0w5) + Word.>>(w1,0w2)  + w2

fun hashPair(a,b) = let val (w1,w2) = (Word.fromInt(a),Word.fromInt(b))
                    in
                       hashTwoWords(w1,w2)
                    end

fun hashWordList(L,h) =
       let fun f([],res) = res
             | f(w::more,res) = f(more,hashTwoWords(h(w),res))
       in 
          if null(L) then 0w0 else f(tl L,h(hd L) )
       end

(** The Jenkins hash is not currently used/exported. **)

fun hashWordList_JenkinsHash(L,h) =
       let fun f([],res) = res
             | f(w::more,res) = 
                  let val res1 = res + h(w)
                      val res2 = Word.<<(res1,0w10)
                      val res3 = Word.>>(res2,0w6)
                      val res4 = Word.>>(res2,0w6)
                  in
                     res4
                  end
           val res = f(L,0w0)
           val res1 = res + Word.<<(res,0w3)
           val res2 = Word.xorb(res1,Word.>>(res1,0w11))
           val res3 = res2 + Word.<<(res2,0w15)
       in 
          res3
       end

fun hashIntList(l) = 
     let fun f([],res) = res
           | f(i::more,res) = f(more,Word.<<(res,0w5) + Word.fromInt(i) + 0w720)
     in 
        f(l,0w0)
     end 

fun hashString(str) = CharVector.foldl hashChar 0w0 str

fun removeStringDuplicates(strings) = 
  let val ht: (string,string) HashTable.hash_table = HashTable.mkTable(hashString, op=) (111,Never)
      val _ = List.app (fn str => HashTable.insert ht (str,str)) strings
  in
     HashTable.listItems ht
  end 

fun hashList(l,seed,f) = 
      let fun loop([],seed) = seed
            | loop(x::more,seed) = let val str = f(x)
                                       val w = #1(hashAccum(str,seed,0))
                                   in
                                     loop(more,w)
                                   end
      in loop(l,seed)
      end
                                                  
fun simpleRenamer(str) = 
  let fun legal(c) = Char.isAlphaNum(c) orelse c = #"_"
      fun transform(c) = "n"^(Int.toString(Char.ord(c)))^"n"
      fun processChar(c:char) = if legal(c) then String.str(c) else (transform c)
  in
     String.translate processChar str 
  end

val varRenamer = simpleRenamer
val fsymRenamer = simpleRenamer

fun repeat n f = 
      let fun loop(i) = if i < 1 then () else (f(i);loop(i-1))
      in loop(n) end

val (newline,lparen,rparen,lbrack,rbrack,lbrace,rbrace,
     blank,comma,period,colon,semi_colon,string_quote) = ("\n","(",")","[","]","{","}"," ",",",".",":",";","\"")

fun mark(s) = (print("\n");repeat 3 (fn _ => print(s));print("\n"))

fun failLst(messages) = raise FailLst messages

fun fail(s) = raise Fail s

fun strictZip(x::xs,y::ys) = (x,y)::strictZip(xs,ys) 
  | strictZip([],[]) = []

fun failMsgsToStr([]) = ""
  | failMsgsToStr([msg]) = msg
  | failMsgsToStr([msg1,msg2]) = msg1^"\n\n"^lparen^msg2^rparen
  | failMsgsToStr(msgs) = printListStr(msgs,id,"\n\n")

fun removeFromSortedList(x,L,comp) =
	let fun f([],res) = rev res
	      | f(lst as a::rest,res) = let val r =  comp(a,x)
			                in
				           if r = EQUAL then (rev res)@rest 
      				           else (if r = LESS then f(rest,a::res) else rev(res))
				        end
        in f(L,[])
	end

fun insertIntoSortedList(x,L,comp) =
	let fun f([],res) = (rev res)@[x]
	      | f(lst as a::rest,res) = 
                  let val r =  comp(a,x)
		  in
		    if r = EQUAL then (rev res)@lst else
                    (if r = LESS then f(rest,a::res) else (rev res)@[x]@lst)
                  end
        in 
           f(L,[])
	end
	
(* Below, a is to be removed from b and inserted into *)
(* the sorted list L. 				      *)

fun removeAndInsertInSortedList(a,b,L,comp) = 
  let fun f([],_) = []
        | f(L as x::rest,g_done) = 
	    let val r = comp(a,x)
	    in
	       if r = EQUAL then
		  (if g_done then rest else g(rest,true))
	       else (if r = LESS then 
			(if g_done then L else g(L,true)) 
		        else (if g_done then x::(f(rest,true)) else g(L,false)))
	    end
       and g([],_) = [b]
         | g(L as x::rest,f_done) = 
		let val r = comp(b,x)
		in
		  if r = EQUAL then	
		     (if f_done then L else f(L,true))
		  else (if r = LESS
			 then (if f_done then b::L else b::x::(f(rest,true)))
			 else (if f_done then x::(g(rest,true)) else x::(f(rest,false))))
		end
   in
     f(L,false)
   end
   
fun findInSorted(x,L,comp) = 
  let fun loop([]) = false
        | loop(a::rest) = (case comp(x,a) of
			        EQUAL => true
			      | GREATER => loop(rest)
			      | LESS => false)
  in
     loop(L)
  end

fun oneLine(str) = not(List.exists (fn c => c = #"\n") (explode str))

fun copies(str:string,n:int) = 
  let fun loop(i,res) = if Int.<(i,1) then String.concat(res) else loop(i-1,str::res)
  in loop(n,[]) end

fun boolToString(true) = "true"
  | boolToString(false) = "false"

val first = List.hd
fun second(l) = first(tl l)
fun third(l) = second(tl l)

fun nrev([]) = [] 
  | nrev(x::rest) = nrev(rest)@[x]

fun mapSelect(f,l,pred) =  
  let fun loop([],accum) = rev accum
        | loop(x::more,accum) = 
             let val res_opt = (SOME(f x)) handle _ => NONE
             in
               (case res_opt of
                   SOME(res) => if pred(res) then loop(more,res::accum) else loop(more,accum)
                 | _ => loop(more,accum))
             end
  in loop(l,[])
  end

fun mapWithIndex(f,L) = 
 let fun loop([],_,res) = rev(res)
       | loop(x::more,i,res) = 
             let val y = f(x,i)
             in loop(more,i+1,y::res) end
 in
    loop(L,0,[])
 end
    
fun appWithIndex(f,L) = 
      let fun loop([],_) = ()
            | loop(x::rest,i) = ((f(x,i));loop(rest,i+1))
      in loop(L,1)
      end

fun countParens(line:string) = 
      let val len = String.size(line)
          fun loop(i,lp,rp) = if i < len then 
                                 let val c = String.sub(line,i)
                                 in
                                   if c = #"(" then loop(i+1,lp+1,rp) 
                                   else if c = #")" then loop(i+1,lp,rp+1)
                                   else loop(i+1,lp,rp) 
                                 end
                              else {lparens=lp,rparens=rp}
      in
         loop(0,0,0)
      end

fun getBalancedLine(stream) =  
      let fun joinLines(lines) = List.foldl op^ "" lines
          fun loop(lines,{lparens,rparens}) = 
               let val new_line = TextIO.inputLine stream
               in
                (case new_line of
                    "" => joinLines(lines) 
                  | _ =>
		         let val {lparens=new_lparens,rparens=new_rparens} = countParens(new_line)
                             val lparens' = lparens + new_lparens 
                             val rparens' = rparens + new_rparens
                         in
                            if lparens' = rparens' then joinLines(new_line::lines)
                            else loop(new_line::lines,{lparens=lparens',rparens=rparens'})
                         end)
              end
      in
         loop([],{lparens=0,rparens=0})
      end 

fun stringContains(str,pred) = 
      let val len = String.size(str)
          fun f(i) = if i >= len then false
                     else let val c = String.sub(str,i)
                          in
                             if pred(c) then true else f(i+1)
                          end
      in
        f(0)
      end

fun allButLast(l) = List.take(l,List.length(l)-1)

fun allButLastAndLast(l) = 
  let fun loop([x],prefix) = (rev(prefix),x)
        | loop(x::(rest as _::_),prefix) = loop(rest,x::prefix)
  in
    loop(l,[])
  end

fun lexOrder(L1,L2,compare) = 
      let fun loop([],[]) = EQUAL
            | loop([],_::_) = LESS
            | loop(_::_,[]) = GREATER
            | loop(x1::more1,x2::more2) =
                let val r = compare(x1,x2)
                in
                   if r = EQUAL then loop(more1,more2) else r
                end
      in
        loop(L1,L2)
      end
      
fun escape(str) = 
  let val len = String.size(str)
      fun loop(i,res) = if i < len then
                           let val c = String.sub(str,i)
                           in
                             if c = #"\\" then loop(i+1,("\\\\")::res) else loop(i+1,(Char.toString(c))::res)
                           end
                        else rev(res)
  in
    String.concat(loop(0,[]))
  end
  
fun downcaseChar(c:char) = 
  let val code = Char.ord(c)
  in
     if ((code >= Char.ord(#"A")) andalso (code <= Char.ord(#"Z"))) then 
     	 Char.chr(code+32) else c
  end

fun downcaseString(str:string) = implode(List.map downcaseChar (explode str))

end
