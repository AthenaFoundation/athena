(*======================================================================

Default values for some global options.

=======================================================================*)

structure Options = 

struct

val first_time = ref(true)

val compilation_on = ref(false)
val expand_proof = ref(false)
val print_var_sorts = ref(true)
val print_qvar_sorts = ref(true)
val conclude_trace = ref (false)
val rewriting_trace = ref(false)
val stack_trace = ref(false)
val detailed_stack_trace = ref(false)
val infix_parsing_option = ref(true)
val sexp_infix_style = ref(false)
val check_fun_defs_option = ref(true)
val demons_active_option = ref(false)
val decompose_assertions_option = ref(true)
val fundef_mlstyle_option = ref(false)
val proof_tracking_option = ref(false)
val fundef_simplifying_option = ref(false)
val silent_mode = ref(false)
val compile_mode_option = ref(true)
val atps_in_chain_option = ref(false)
val option_valued_selectors_option = ref(false)
val auto_assert_dt_axioms = ref(false)
val auto_assert_selector_axioms = ref(true)
val default_table_size = ref(743)

fun setDebugModeFlag("off",_) = 
	(conclude_trace := false;
	 rewriting_trace := false;
         stack_trace := false;	
	 detailed_stack_trace := false;
	 "OK.")
  | setDebugModeFlag("conclude",_) = 
	(conclude_trace := true;
         rewriting_trace := false;
         stack_trace := false;
	 detailed_stack_trace := false;
        "OK.")
  | setDebugModeFlag("rewriting",_) = 
	(conclude_trace := true;
         rewriting_trace := true;
         stack_trace := false;
	 detailed_stack_trace := false;
        "OK.")
  | setDebugModeFlag("simple",_) = 
	(conclude_trace := true;
         rewriting_trace := true;
         stack_trace := true;
	 detailed_stack_trace := false;
        "OK.")
  | setDebugModeFlag("detailed",_) = 
	(conclude_trace := true;
         rewriting_trace := true;
         stack_trace := true;
	 detailed_stack_trace := true;
        "OK.")
  | setDebugModeFlag(_,pos_opt) = 
   	let val str = "The only valid values for the "^Names.debug_mode_flag^" flag are \"off\", "^
	              "\"conclude\", \"rewriting\", \"simple\", and \"detailed\"."
        in
           Util.makeErrorMessage(str,pos_opt)
        end;

fun setPrintVarSortsFlag("on",_) = (print_var_sorts := true; "OK.")
  | setPrintVarSortsFlag("off",_) = (print_var_sorts := false; "OK.")
  | setPrintVarSortsFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.print_var_sorts_flag^" flag are \"on\" and \"off\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

fun setPrintQVarSortsFlag("on",_) = (print_qvar_sorts := true; "OK.")
  | setPrintQVarSortsFlag("off",_) = (print_qvar_sorts := false; "OK.")
  | setPrintQVarSortsFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.print_qvar_sorts_flag^" flag are \"on\" and \"off\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

fun setCheckFunAxiomsFlag("on",_) =   (check_fun_defs_option := true;  "OK.")
  | setCheckFunAxiomsFlag("off",_) =  (check_fun_defs_option := false; "OK.")
  | setCheckFunAxiomsFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.check_fun_defs^" flag are \"on\" and \"off\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

fun setInfixParsingFlag("on",_) =   (infix_parsing_option := true;  "OK.")
  | setInfixParsingFlag("off",_) =  (infix_parsing_option := false; "OK.")
  | setInfixParsingFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.infix_parsing_flag^" flag are \"on\" and \"off\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

fun setDemonsFlag("on",_) =   (demons_active_option := true;  "OK.")
  | setDemonsFlag("off",_) =  (demons_active_option := false; "OK.")
  | setDemonsFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.demons_active_flag^" flag are \"on\" and \"off\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

fun setDecomposeAssertionsFlag("on",_) =   (decompose_assertions_option := true;  "OK.")
  | setDecomposeAssertionsFlag("off",_) =  (decompose_assertions_option := false; "OK.")
  | setDecomposeAssertionsFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.decompose_assertions_flag^" flag are \"on\" and \"off\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

fun setBooleanFlag(option,option_name,str,pos) = 
       (case str of
          "on" => (let val res = if (!silent_mode) then "" else "OK." 
                       val _ = option := true
                   in res end)
        | "off" => (let val res = if (!silent_mode) then "" else "OK." 
                       val _ = option := false
                   in res end)
        | _ => 	(let val res = if (!silent_mode) then "" else "The only valid values for the "^option_name^" flag are \"on\" and \"off\""
                   in  Util.makeErrorMessage(res,SOME(pos)) end))

fun setIntFlag(option,option_name,str,pos) = 
  (case Int.fromString(str) of
      SOME(i) => (option := i; if (!silent_mode) then "" else  "OK")
    | _ => if (!silent_mode) then "" else Util.makeErrorMessage("Invalid value given for flag "^option_name^".\nAn integer value is required",SOME(pos)))

fun setFunctionAppStyleFlag("classic-sexp",_) =   (sexp_infix_style := true;  "OK.")
  | setFunctionAppStyleFlag("comma-separated",_) =  (sexp_infix_style := false; "OK.")
  | setFunctionAppStyleFlag(_,pos) = 
	let val str = "The only valid values for the "^Names.infix_parsing_flag^" flag are \"classic-sexp\" and \"comma-separated\"."
	in      
           Util.makeErrorMessage(str,SOME(pos))
        end

val no_pos_ar_fun_syms = ref(true)

fun noPosArityFunSyms() = !no_pos_ar_fun_syms

val standard_bool_symbol_precedence = 100

val lowest_fsymbol_precedence = 110

fun defaultPrec(arity) = if arity = 1 orelse arity = 2 then lowest_fsymbol_precedence else 0

fun setDefaultPrec(arity,prec_ref) = prec_ref := defaultPrec(arity)

val first_call_stack_chunk_size_limit = ref(5)
val top_call_stack_portion_length = ref(5)

val call_stack_size = ref(2000)

val fundef_explicit_wildcard_patterns_option = ref(1)

val dt_for_dom_default_size = ref(5)

val ground_doms = ref(true)

fun debugPrint(str) = let
                      in
                          if (!first_time) then () else print("\n" ^ str)
                      end

end (* of structure Options *)
