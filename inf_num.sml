(*======================================================================

Implementation of the INF_NUM signature. 

=======================================================================*)

structure InfNum : INF_NUM =
struct

type inf_num = int * int

val max = getOpt(Int.maxInt,1000000000);

val smlPrint = print;

val max_str = Int.toString(max);

val max_len = String.size(max_str);

fun makeInfNum() = (1,1);

fun makeInfNumTagged() = (1,~1);

fun tagged (_,y) = y < 0;

fun tag(x,y) = (x,~y);

fun toString(x,y) = let val x_str = Int.toString(x) 
                    in
                      if y < 2 then x_str else x_str^(Basic.copies(max_str,y-1))
                    end

fun print (x,y) = smlPrint(toString(x,y));

fun fromInt(i) = (i,1);

fun compare((x1,n1),(x2,n2)) = 
      let val (m1,m2) = (abs n1, abs n2)
      in 
        if (m1 = m2) then
           (if Int.<(x1,x2) then General.LESS 
            else if Int.>(x1,x2) then General.GREATER 
                 else General.EQUAL)
        else 
           (if m1 < m2 then General.LESS 
               else General.GREATER)
      end;

fun eq((x1,n1),(x2,n2)) = (x1 = x2) andalso (n1 = n2);

fun top(x,_) = x;

fun fromString(str) = 
      let val len = String.size(str)
          val quot = Int.div(len,max_len)
          val rem  = Int.mod(len,max_len)
      in 
         (getOpt(Int.fromString(String.substring(str,0,rem)),0),quot+1)
      end;

fun incrementLen(n) = if n < 0 then n - 1 else n + 1;

fun increment(x,n) = if x < max then (x+1,n) else (1,incrementLen(n));

end;
