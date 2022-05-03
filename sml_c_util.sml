(*======================================================================

Some very rudimentary but useful generic code for interfacing SML with C
and/or C++. This code only works with MLton.

=======================================================================*)

structure SML_With_C_Interaction = 

struct

(* Define a useful type appreviation: *)

type pointer = MLton.Pointer.t  

(* Import C's malloc function, with two specialized allocators for integers and chars: *)

val malloc = _import "malloc": int -> pointer;

val mallocInt = _import "mallocInt": int -> pointer;

val mallocChars = _import "mallocChars": int -> pointer;

fun isNullPointer(p:pointer) = (MLton.Pointer.compare(p,MLton.Pointer.null) = EQUAL)

val free = _import "free": pointer -> unit;

(* C-style-string terminator: *)

val null_char = #"\000"

(**
   A function that grabs the raw byte determined by a C pointer and an integer offset.
   It assumes that a byte is 8 bits. Some machines might violate this. Obviously this
   also won't work if the char to be fetched is not ASCII. If an exception is raised,
   the function returns a blank character.
**)

fun getChar(p:pointer,index:int) =
  (Char.chr(Int8.toInt(MLton.Pointer.getInt8(p,index)))) handle _ => Char.chr(32)
    
(* A function that sets the raw byte given a C pointer and an integer offset *)

fun setChar(p:pointer,index:int,c:char) =  
      MLton.Pointer.setInt8(p, index, Int8.fromInt(Char.ord(c)))

(* Get a 32-bit integer. This should work with long's, but check your machine. *)

fun getInt(p:pointer,index:int) = MLton.Pointer.getInt32(p,index)

fun setInt(p:pointer,index:int,i:int) = MLton.Pointer.setInt32(p,index,i)

(* A function that makes a character list from a given C pointer.      *)
(* The list is terminated when the first null character is encountered *)
(* in the C string.                                                    *)

fun makeCharList(p:pointer) = 
  let fun loop(i,res) = 
            let val c = getChar(p,i)
            in
               if c = null_char then rev(res) else loop(i+1,c::res)
            end
  in
    loop(0,[])
  end

(* Like the previous function, except that this one makes a proper SML string. *)

fun makeSmlString(p:pointer) = implode(makeCharList(p))

(* A tail-recursive SML implementation of the C strlen function: *)

fun strLen(p:pointer) = 
      let fun count(i,sum) = if getChar(p,i) = null_char then sum else count(i+1,sum+1)
      in
        count(0,0)
      end

(** 
   A quick way to do functional string reversal: use malloc to allocate  
   the right number of bytes, then set each byte to the right value by   
   walking down the given C buffer for strLen-many bytes.
**)   

fun revString1(buffer:pointer) = 
  let val len = strLen(buffer)
      val result = malloc(len + 1)
      fun fill(i) = if i < len then (setChar(result,len-i-1,getChar(buffer,i));fill(i+1)) 
                    else setChar(result,len,null_char)
      val _ = fill(0)
  in
     result
  end

val e = _export "revString1": (pointer -> pointer) -> unit;

val _ = e revString1;

(* A somewhat less efficient way to reverse: *) 

val e2 = _export "revString2": (pointer -> string) -> unit;

val _ = e2 (fn (p) => implode(rev(makeCharList(p))));

(**
   The 2 functions below are used to properly pass string values     
   from SML to C. The first function simply returns a pointer,       
   whereas the second one expects a C-allocated chunk of memory      
   to be passed to it, and it writes the SML string into that memory.
**)

fun SMLString2CString(str:string) = 
  let val len = String.size(str)
      val result = malloc(len + 1)
      fun loop(i) = if i < len then
                       let val c  = String.sub(str,i)
                       in
	                  (setChar(result,i,c);loop(i+1))
                       end
                   else setChar(result,i,null_char)
      val _ = loop(0)
  in
    result
  end

(**
   Note: The above is not entirely safe in that when one tries to free the    
   malloc-allocated memory for result from within C, sometimes things break.  
   It's much better to allocate the buffer inside C and use copyIntoCBuffer   
   below. The memory can then be easily freed from within C.                 
**)

fun copyIntoCBuffer(str:string,p:pointer) = 
  let val len = String.size(str)
      fun loop(i) = if i < len then
                       let val c  = String.sub(str,i)
                       in
	                  (setChar(p,i,c);loop(i+1))
                       end
                   else setChar(p,i,null_char)
  in
    loop(0)
  end

fun copyIntoCBuffer1(str:string,p:pointer,index:int) = 
  let val len = String.size(str)
      val limit = index + len 
      fun loop(i) = if i < len then
                       let val c  = String.sub(str,i)
                       in
	                  (setChar(p,i+index,c);loop(i+1))
                       end
                   else ();
  in
    (loop(0);limit)
  end

end