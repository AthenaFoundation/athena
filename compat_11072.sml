structure TextIO =
struct
    open TextIO
    fun inputLine(is) = (case TextIO.inputLine(is) of
                           SOME(l) => l 
                         | _ => "")
end

structure Array =
struct
    open Array

    fun copy {src,si,len,dst,di} =
        let val n = (case len of
                        SOME n => n
                      | NONE => (length src) - si)
            val _ = if si < 0 orelse (length src) < (si+n)
                    then raise Subscript else ()
            val _ = if di < 0 orelse (length dst) < (di+n)
                    then raise Subscript else ()
            fun loop (i,j,0) = ()
              | loop (i,j,cnt) = 
                  (Array.update (dst,j,(Array.sub(src,i)));
                   loop (i+1,j+1,cnt-1))
        in
          loop (si,di,n)
        end	
end
