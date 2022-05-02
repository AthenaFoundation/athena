(*======================================================================

Code for dealing with Yacc-generated parsing errors.

=======================================================================*)

signature ERRORMSG =
sig
    val any_errors : bool ref
    val file_name : string ref
    val line_num : int ref
    val line_pos : int list ref
    val source_stream : TextIO.instream ref
    val error: string * (int * int) * (int * int) -> unit
    val print_error: string * (int * int) * (int * int) -> unit    
    exception Error
    exception ParseError of (int * int) * string 
    val impossible : string -> 'a   (* raises Error *)
    val reset : unit -> unit
end

structure ErrorMsg : ERRORMSG =

struct

  exception ParseError of (int * int) * string;

  val any_errors = ref false
  val file_name = ref ""
  val line_num = ref 1
  val line_pos = ref [1]
  val source_stream = ref TextIO.stdIn

  fun reset() = (any_errors:=false;
                 file_name:="";
                 line_num:=1;
                 line_pos:=[1];
                 source_stream:=TextIO.stdIn)

  exception Error
 
  fun error(str,left_pos as (l1,p1),right_pos as (l2,p2)) = raise ParseError((l1,p1),str);

  val print_error = error

  fun impossible msg =
      (app print ["Error: Compiler bug: ",msg,"\n"];
       TextIO.flushOut TextIO.stdOut;
       raise Error)

end  (* structure ErrorMsg *)
