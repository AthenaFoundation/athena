(*======================================================================

Some simple utilities. 

=======================================================================*)

structure Util = 

struct

fun makeErrorMessage(str,SOME(pos)) = "\n"^(Position.posToString pos)^": Error, "^str^"."
  | makeErrorMessage(str,NONE) = "\nError, "^str^".";

fun killAthena() = (OS.Process.terminate(OS.Process.success));

fun small(str,n) = let val clist = explode(str) 
                   in
                     not(List.exists (fn c => c = #"\n") clist) andalso
                     (length(clist) < n)
                   end;

fun decide(str,n) = if small(str,n) then str else "\n"^str;

val div_sym_code = ModSymbol.code(Names.mdivision_symbol)
val add_sym_code = ModSymbol.code(Names.maddition_symbol)
val sub_sym_code = ModSymbol.code(Names.msubtraction_symbol)
val less_sym_code = ModSymbol.code(Names.mformal_less_symbol)
val geq_sym_code = ModSymbol.code(Names.mformal_geq_symbol)

fun isNumeric(f) = let val c = ModSymbol.code(f)
                   in c <= geq_sym_code andalso c >= add_sym_code end;

fun notNumeric(f) = (ModSymbol.code(f) > geq_sym_code)

end;
