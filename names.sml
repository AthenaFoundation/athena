(*======================================================================

A structure containing the names of all of Athena's predefined values.
Only this file needs to be modified in order to change the name of a
primitive value. Names of the most common theorem provers that Athena
is integrated with (spass, vampire, cvc4, and minisat) are also found
at the bottom on this file.

=======================================================================*)

structure Names = 
struct

(*======================================================================

NOTE 1: The four numeric function symbols +, -, *, and /     
and the four numeric comparison symbols <, <=, >, >=         
as well as the equality symbol and the constants true and false 
MUST appear at the top of this structure, in order to get    
lower hash codes assigned to them in the Symbol structure.   
This is exploited later for more efficient sort inference.   

NOTE 2: Moreover, the order in which the following symbols 
appear in this file is important. All first 17 symbols --    
between + and the constant false -- must appear in the order 
in which they appear in ath-term.sml, in the part that updates
the smt_names array.                                         

=======================================================================*)

fun printCode(m) = print("\nCode for " ^ (ModSymbol.name(m)) ^ ": " ^ (Int.toString(ModSymbol.code(m))) ^ "\n")

val addition_name = "+"
val addition_symbol = Symbol.symbol addition_name
val maddition_symbol = ModSymbol.makeModSymbol([],addition_symbol,addition_symbol)

val subtraction_name = "-"
val subtraction_symbol = Symbol.symbol subtraction_name
val msubtraction_symbol = ModSymbol.makeModSymbol([],subtraction_symbol,subtraction_symbol)

val multiplication_name = "*"
val multiplication_symbol = Symbol.symbol multiplication_name
val mmultiplication_symbol = ModSymbol.makeModSymbol([],multiplication_symbol,multiplication_symbol)

val division_name = "/"
val division_symbol = Symbol.symbol division_name
val mdivision_symbol = ModSymbol.makeModSymbol([],division_symbol,division_symbol)

val modulo_name = "%"
val modulo_symbol = Symbol.symbol modulo_name
val mmodulo_symbol = ModSymbol.makeModSymbol([],modulo_symbol,modulo_symbol)


val formal_less_name = "<"
val formal_less_symbol = Symbol.symbol formal_less_name
val mformal_less_symbol = ModSymbol.makeModSymbol([],formal_less_symbol,formal_less_symbol)


val formal_greater_name = ">"
val formal_greater_symbol = Symbol.symbol formal_greater_name
val mformal_greater_symbol = ModSymbol.makeModSymbol([],formal_greater_symbol,formal_greater_symbol)


val formal_leq_name = "<="
val formal_leq_symbol = Symbol.symbol formal_leq_name
val mformal_leq_symbol = ModSymbol.makeModSymbol([],formal_leq_symbol,formal_leq_symbol)


val formal_geq_name = ">="
val formal_geq_symbol = Symbol.symbol formal_geq_name
val mformal_geq_symbol = ModSymbol.makeModSymbol([],formal_geq_symbol,formal_geq_symbol)


val equal_logical_name = "="
val equal_logical_symbol = Symbol.symbol equal_logical_name
val mequal_logical_symbol = ModSymbol.makeModSymbol([],equal_logical_symbol,equal_logical_symbol)


val ite_name = "ite"
val ite_symbol = Symbol.symbol ite_name
val mite_symbol = ModSymbol.makeModSymbol([],ite_symbol,ite_symbol)
val ite_symbol_code = ModSymbol.code(mite_symbol)

fun msym(s) = ModSymbol.makeModSymbol([],s,s)

val And_name = "And"
val And_symbol = Symbol.symbol And_name
val mAnd_symbol = ModSymbol.makeModSymbol([],And_symbol,And_symbol)

val Or_name = "Or"
val Or_symbol = Symbol.symbol Or_name
val mOr_symbol = ModSymbol.makeModSymbol([],Or_symbol,Or_symbol)

val Not_name = "Not"
val Not_symbol = Symbol.symbol Not_name
val mNot_symbol = msym Not_symbol

val If_name = "If"
val If_symbol = Symbol.symbol If_name
val mIf_symbol = ModSymbol.makeModSymbol([],If_symbol,If_symbol)

val Iff_name = "Iff"
val Iff_symbol = Symbol.symbol Iff_name
val mIff_symbol = ModSymbol.makeModSymbol([],Iff_symbol,Iff_symbol)

val fun_name = "Fun";
val fun_name_sym = Symbol.symbol fun_name
val fun_name_msym = ModSymbol.makeModSymbol([],fun_name_sym,fun_name_sym)

val app_fsym_name = "app"
val app_fsym_name_sym = Symbol.symbol app_fsym_name
val app_fsym_mname = ModSymbol.makeModSymbol([],app_fsym_name_sym,app_fsym_name_sym)


val true_logical_name = "true"
val true_logical_symbol = Symbol.symbol true_logical_name
val mtrue_logical_symbol = ModSymbol.makeModSymbol([],true_logical_symbol,true_logical_symbol)


val false_logical_name = "false"
val false_logical_symbol = Symbol.symbol false_logical_name
val mfalse_logical_symbol = ModSymbol.makeModSymbol([],false_logical_symbol,false_logical_symbol)

val check_name = "check"
val match_name = "match"
val else_name =  "else"
val lambda_name =  "lambda"
val method_name =  "method"

val logical_and_name = "&&"
val logical_and_symbol = Symbol.symbol logical_and_name

val logical_or_name = "||"
val logical_or_symbol = Symbol.symbol logical_or_name

val metaIdPrefix = "'"
val metaIdPrefix_char = #"'"

structure S = Symbol

val fresh_var_name_prefix  = "v"
val fresh_var_name_prefix_symbol  = Symbol.symbol fresh_var_name_prefix

val ATP_conversion_prefix = ref("N_")

val variable_prefix = "?"
val variable_prefix_symbol =  Symbol.symbol variable_prefix

val sort_variable_letter_prefix = "T"
val sort_variable_letter_prefix_as_char = #"T"

val sort_variable_prefix = "'"
val sort_variable_prefix_as_char = #"'"

val is_assertion_name = "assertion?"
val is_assertion_symbol = Symbol.symbol is_assertion_name

val is_constructor_name = "constructor?"
val is_constructor_symbol = Symbol.symbol is_constructor_name

val check_fun_def_name = "check-fun-def"
val check_fun_def_symbol = Symbol.symbol check_fun_def_name

val is_free_constructor_name = "free-constructor?"
val is_free_constructor_symbol = Symbol.symbol is_free_constructor_name

val freshSymbolFun_name = "make-fresh-constants"
val freshSymbolFun_symbol = Symbol.symbol freshSymbolFun_name

val hasMonoSortFun_name = "has-mono-sort?"
val hasMonoSortFun_symbol = Symbol.symbol hasMonoSortFun_name

val applyExtractedSortSubFun_name = "apply-extracted-sort-sub"
val applyExtractedSortSubFun_symbol = Symbol.symbol applyExtractedSortSubFun_name

val fsymsInFunDefTableFun_name = "defined-fsyms"
val fsymsInFunDefTableFun_symbol = Symbol.symbol fsymsInFunDefTableFun_name

val getAlphaCertFun_name = "get-alpha-cert"
val getAlphaCertFun_symbol = Symbol.symbol getAlphaCertFun_name

val subtermsFun_name = "subterms"
val subtermsFun_symbol = Symbol.symbol subtermsFun_name

val sentSubtermsFun_name = "sent-subterms"
val sentSubtermsFun_symbol = Symbol.symbol sentSubtermsFun_name

val sortVarsFun_name = "sort-vars"
val sortVarsFun_symbol = Symbol.symbol sortVarsFun_name

val monoInstanceFun_name = "make-monomorphic-instance"
val monoInstanceFun_symbol = Symbol.symbol monoInstanceFun_name

val holdsFun_name = "holds?"
val holdsFun_symbol = Symbol.symbol holdsFun_name
val consFun_name = "add"
val consFun_symbol = Symbol.symbol consFun_name
val fresh_var_name = "fresh-var"
val fresh_var_symbol = Symbol.symbol fresh_var_name

val dependenciesFun_name = "dependencies"
val dependenciesFun_symbol = Symbol.symbol dependenciesFun_name

val dependenciesTranFun_name = "dependencies*"
val dependenciesTranFun_symbol = Symbol.symbol dependenciesTranFun_name

val abToStringFun_name = "ab->string"
val abToStringFun_symbol = Symbol.symbol abToStringFun_name

val symCodeFun_name = "symbol-code"
val symCodeFun_symbol = Symbol.symbol symCodeFun_name

val fresh_var_with_prefix_name = "fresh-var-with-prefix"
val fresh_var_with_prefix_symbol = Symbol.symbol fresh_var_with_prefix_name

val num_plus_name = "plus"
val num_plus_symbol = Symbol.symbol num_plus_name
val num_minus_name = "minus"
val num_minus_symbol = Symbol.symbol num_minus_name
val num_times_name = "times"
val num_times_symbol = Symbol.symbol num_times_name
val num_div_name = "div"
val num_div_symbol = Symbol.symbol num_div_name
val num_mod_name = "mod"
val num_mod_symbol = Symbol.symbol num_mod_name
val num_equal_name = "num-equal?"
val num_equal_symbol = Symbol.symbol num_equal_name
val num_less_name = "less?"
val num_less_symbol = Symbol.symbol num_less_name

val smt_default_selector_fun_sym_prefix = "_sel_"
val smt_default_selector_fun_sym_prefix_char_list = explode(smt_default_selector_fun_sym_prefix)

val numEqualFun_name = "num-equal?"
val numEqualFun_symbol = Symbol.symbol numEqualFun_name
val carFun_name = "head"
val carFun_symbol = Symbol.symbol carFun_name
val getSymDef_name = "get-sym-def"
val arityOf_name = "arity-of"
val arityOf_symbol = Symbol.symbol arityOf_name
val getSelectorsFun_name = "selector-names"
val getSelectorsFun_symbol = Symbol.symbol getSelectorsFun_name
val getSymDef_symbol = Symbol.symbol getSymDef_name
val cdrFun_name = "tail"
val cdrFun_symbol = Symbol.symbol cdrFun_name
val not_name = "not"
val not_symbol = Symbol.symbol not_name
val mnot_symbol = msym not_symbol
val alternate_not_name = "~"
val alternate_not_symbol = Symbol.symbol alternate_not_name
val and_name = "and"
val and_symbol = Symbol.symbol and_name
val mand_symbol = msym and_symbol
val alternate_and_name = "&"
val alternate_and_symbol = Symbol.symbol alternate_and_name
val or_name = "or"
val or_symbol = Symbol.symbol or_name
val mor_symbol = msym or_symbol
val alternate_or_name = "|"
val alternate_or_symbol = Symbol.symbol alternate_or_name
val if_name = "if"
val if_symbol = Symbol.symbol if_name
val mif_symbol = msym if_symbol

val alternate_if_name = "==>"
val alternate_if_symbol = Symbol.symbol alternate_if_name

val iff_name = "iff"
val iff_symbol = Symbol.symbol iff_name
val miff_symbol = msym iff_symbol
val alternate_iff_name = "<==>"
val alternate_iff_symbol = Symbol.symbol alternate_iff_name

val forall_name = "forall"
val forall_symbol = Symbol.symbol forall_name
val mforall_symbol = msym forall_symbol
val exists_name = "exists"
val exists_symbol = Symbol.symbol exists_name
val mexists_symbol = msym exists_symbol
val exists_unique_name = "exists-unique"
val exists_unique_symbol = Symbol.symbol exists_unique_name
val mexists_unique_symbol = msym exists_unique_symbol

val force_name = "force"
val force_symbol = Symbol.symbol force_name
val mforce_symbol = msym force_symbol
val private_force_symbol = Symbol.makePrivateSymbol(force_name)
val mprivate_force_symbol = msym private_force_symbol

val funSymFun_name = "fun-sym"
val funSymFun_symbol = Symbol.symbol funSymFun_name
val nullFun_name = "null?"
val nullFun_symbol = Symbol.symbol nullFun_name
val eq_name = "equal?"
val eq_symbol = Symbol.symbol eq_name

val struc_eq_name = "struc-equal?"
val struc_eq_symbol = Symbol.symbol struc_eq_name

val plus_symbol = Symbol.symbol "plus"
val less_symbol = Symbol.symbol "less?"
val greater_symbol = Symbol.symbol "greater?"
val minus_symbol = Symbol.symbol "minus"
val timpes_symbol = Symbol.symbol "times"
val div_symbol = Symbol.symbol "div"
val mod_symbol = Symbol.symbol "mod"


val write_name = "write"
val write_symbol = Symbol.symbol write_name

val wild_card = "_"
val wild_card_symbol = Symbol.symbol wild_card


val writeVal_name = "write-val"
val writeVal_symbol = Symbol.symbol writeVal_name


val valToString_name = "val->string"

val valToStringUnlim_name = "val->string-all"
val valToStringUnlim_symbol = Symbol.symbol valToStringUnlim_name

val valToString_symbol = Symbol.symbol valToString_name

val valToString_name' = "val->string'"
val valToString_symbol' = Symbol.symbol valToString_name'

val transOntologyFun_name = "translate-ontology"
val transOntologyFun_symbol = Symbol.symbol transOntologyFun_name

val clientConnect_name = "client"
val clientConnect_symbol = Symbol.symbol clientConnect_name

val getABFun_name = "get-ab"
val getABFun_symbol =  Symbol.symbol getABFun_name
val renameFun_name = "rename"
val renameFun_symbol = Symbol.symbol renameFun_name
val print_name = "print"
val print_symbol = Symbol.symbol print_name
val makeAthenaListFun_name = "make-athena-list"
val makeAthenaListFun_symbol = Symbol.symbol makeAthenaListFun_name

val makeTermFun_name = "make-term"
val makeTermFun_symbol = Symbol.symbol makeTermFun_name
val concatFun_name = "join"
val concatFun_symbol = Symbol.symbol concatFun_name
val mconcatFun_symbol = ModSymbol.makeModSymbol([],concatFun_symbol,concatFun_symbol)

val compareFun_name = "compare"
val compareFun_symbol = Symbol.symbol compareFun_name

val isStructureWithoptionValuedSelectorsFun_name = "struc-with-option-valued-selectors?"
val isStructureWithoptionValuedSelectorsFun_symbol = Symbol.symbol isStructureWithoptionValuedSelectorsFun_name
val structureConstructorsFun_name = "constructors-of"
val structureConstructorsFun_symbol = Symbol.symbol structureConstructorsFun_name
val revFun_name = "rev"
val revFun_symbol = Symbol.symbol revFun_name
val haltFun_name = "halt"
val haltFun_symbol = Symbol.symbol haltFun_name

val currentModPathFun_name = "mod-path"
val currentModPathFun_symbol = Symbol.symbol currentModPathFun_name

val isPrintableFun_name = "printable?"
val isPrintableFun_symbol = Symbol.symbol isPrintableFun_name
val last_proof_name = "last-proof"
val last_proof_symbol = Symbol.symbol last_proof_name
val last_value_name = "last-val"
val last_value_symbol = Symbol.symbol last_value_name
val sort_of_name = "sort-of"
val sort_of_symbol = Symbol.symbol sort_of_name

val sort_of_var_in_term_name = "sort-of-var-in-term"
val sort_of_var_in_term_symbol = Symbol.symbol sort_of_var_in_term_name

val catchFun_name = "catch"
val catchFun_symbol = Symbol.symbol catchFun_name

val posOfFun_name = "pos-of"
val posOfFun_symbol = Symbol.symbol posOfFun_name

val proofErrorMethod_name = "proof-error"
val proofErrorMethod_symbol = Symbol.symbol proofErrorMethod_name

val compErrorFun_name = "error"
val compErrorFun_symbol = Symbol.symbol compErrorFun_name

val catchMethod_name = "dcatch"
val catchMethod_symbol = Symbol.symbol catchMethod_name

val sort_of_var_in_prop_name = "sort-of-var-in-prop"
val sort_of_var_in_prop_symbol = Symbol.symbol sort_of_var_in_prop_name

val makeVectorFun_name = "make-vector"
val makeVectorFun_symbol = Symbol.symbol  makeVectorFun_name

val vectorSetFun_name = "vector-set!"
val vectorSetFun_symbol = Symbol.symbol vectorSetFun_name

val vectorSubFun_name = "vector-sub"
val vectorSubFun_symbol =  Symbol.symbol  vectorSubFun_name

val sizeFun_name = "size"
val sizeFun_symbol = Symbol.symbol sizeFun_name

val vector_len_name = "vector-size"
val vector_len_symbol = Symbol.symbol vector_len_name

val isNumeralFun_name = "numeral?"
val isNumeralFun_symbol = Symbol.symbol isNumeralFun_name

val constructor_inj_name = "constructor-injectivity"
val constructor_inj_symbol = Symbol.symbol constructor_inj_name
val constructor_excl_name = "constructor-exclusiveness"
val constructor_excl_symbol = Symbol.symbol constructor_excl_name
val constructor_exhaust_name = "constructor-exhaustiveness"
val constructor_exhaust_symbol = Symbol.symbol constructor_exhaust_name
val is_atom_name = "atom?"
val is_atom_symbol = Symbol.symbol is_atom_name
val is_dir_name = "dir?"
val is_dir_symbol = Symbol.symbol is_dir_name
val lineCount_name = "line-count"
val lineCount_symbol = Symbol.symbol lineCount_name 
val children_name = "children"
val children_symbol = Symbol.symbol children_name
val root_name = "root"
val root_symbol = Symbol.symbol root_name
val readFile_name = "read-file"
val readFile_symbol = Symbol.symbol readFile_name

val readFileLines_name = "read-file-lines"
val readFileLines_symbol = Symbol.symbol readFileLines_name

val listAllDirEntries_name = "list-all-dir-entries"
val listAllDirEntries_symbol = Symbol.symbol listAllDirEntries_name

val listAllDirEntriesRecursively_name = "list-all-dir-entries-recursively"
val listAllDirEntriesRecursively_symbol = Symbol.symbol listAllDirEntriesRecursively_name

val writeFile_name = "write-file"
val writeFile_symbol = Symbol.symbol writeFile_name
val readOneChar_name = "read"
val readOneChar_symbol = Symbol.symbol readOneChar_name
val replaceVar_name = "replace-var"
val replaceVar_symbol = Symbol.symbol replaceVar_name
val varsFun_name = "vars"
val varsFun_symbol = Symbol.symbol varsFun_name
val freeVarsFun_name = "free-vars"
val freeVarsFun_symbol = Symbol.symbol freeVarsFun_name 
val alEqFun_name = "alpha-equiv"
val alEqFun_symbol = Symbol.symbol alEqFun_name
val metaIdToStringFun_name = "id->string"
val metaIdToStringFun_symbol = Symbol.symbol metaIdToStringFun_name 
val stringToMetaIdFun_name = "string->id"
val stringToMetaIdFun_symbol = Symbol.symbol stringToMetaIdFun_name

val execCommandFun_name = "exec-command"
val execCommandFun_symbol = Symbol.symbol execCommandFun_name

val deleteFileFun_name = "delete-file"
val deleteFileFun_symbol = Symbol.symbol deleteFileFun_name

val deleteFile1Fun_name = "delete-file-verbose"
val deleteFile1Fun_symbol = Symbol.symbol deleteFile1Fun_name

val stringToSymbolFun_name = "string->symbol"
val stringToSymbolFun_symbol = Symbol.symbol stringToSymbolFun_name 

val metaIdPlusFun_name = "mid-plus"
val metaIdPlusFun_symbol = Symbol.symbol metaIdPlusFun_name

val sqrtFun_name = "sqrt"
val sqrtFun_symbol = Symbol.symbol sqrtFun_name

val log10Fun_name = "log10"
val log10Fun_symbol = Symbol.symbol log10Fun_name

val lnFun_name = "ln"
val lnFun_symbol = Symbol.symbol lnFun_name

val plusFun_name = "plus"
val plusFun_symbol = Symbol.symbol "plus"
val minusFun_name = "minus"
val minusFun_symbol = Symbol.symbol minusFun_name
val timesFun_name = "times"
val timesFun_symbol = Symbol.symbol timesFun_name
val divFun_name = "div"
val divFun_symbol = Symbol.symbol divFun_name
val modFun_name = "mod"
val modFun_symbol = Symbol.symbol modFun_name
val lessFun_name = "less?"
val lessFun_symbol = Symbol.symbol lessFun_name
val greaterFun_name = "greater?"
val greaterFun_symbol = Symbol.symbol greaterFun_name


val metaIdMinusFun_name = "mid-minus"
val metaIdMinusFun_symbol = Symbol.symbol metaIdMinusFun_name


val metaIdTimesFun_name = "mid-times"
val metaIdTimesFun_symbol = Symbol.symbol metaIdTimesFun_name

val metaIdDivFun_name = "mid-div"
val metaIdDivFun_symbol = Symbol.symbol metaIdDivFun_name

val metaIdLessFun_name = "mid-less"
val metaIdLessFun_symbol = Symbol.symbol metaIdLessFun_name

val metaIdGreaterFun_name = "mid-greater"
val metaIdGreaterFun_symbol = Symbol.symbol metaIdGreaterFun_name

val stringToNumFun_name = "string->num"
val stringToNumFun_symbol = Symbol.symbol stringToNumFun_name

val getDebugModeFun_name = "get-debug-mode"
val getDebugModeFun_symbol = Symbol.symbol getDebugModeFun_name

val setDebugModeFun_name = "set-debug-mode"
val setDebugModeFun_symbol = Symbol.symbol setDebugModeFun_name

val getTraceLevelFun_name = "get-trace-level"
val getTraceLevelFun_symbol = Symbol.symbol getTraceLevelFun_name

val indentPrintFun_name = "indent-print"
val indentPrintFun_symbol = Symbol.symbol indentPrintFun_name

val fetchFun_name = "fetch"
val fetchFun_symbol = Symbol.symbol fetchFun_name
val fetchAllFun_name = "fetch-all"
val fetchAllFun_symbol = Symbol.symbol fetchAllFun_name

val subComposeFun_name = "compose-subs"
val subComposeFun_symbol  = Symbol.symbol subComposeFun_name

val isSubFun_name = "substitution?"
val isSubFun_symbol = Symbol.symbol isSubFun_name

val isTermFun_name = "term?"
val isTermFun_symbol = Symbol.symbol isTermFun_name

val isTermConFun_name = "symbol?"
val isTermConFun_symbol = Symbol.symbol isTermConFun_name

val isUnitFun_name = "unit?"
val isUnitFun_symbol = Symbol.symbol isUnitFun_name

val isCellFun_name = "cell?"
val isCellFun_symbol = Symbol.symbol isCellFun_name

val isFunctionFun_name = "proc?"
val isFunctionFun_symbol = Symbol.symbol isFunctionFun_name

val isMethodFun_name = "method?"
val isMethodFun_symbol = Symbol.symbol isMethodFun_name

val procNameFun_name = "proc-name"
val procNameFun_symbol = Symbol.symbol procNameFun_name

val isPropFun_name = "sentence?"
val isPropFun_symbol = Symbol.symbol isPropFun_name

val propFun_name = "prop"
val propFun_symbol = Symbol.symbol propFun_name

val isMetaIdFun_name = "meta-id?"
val isMetaIdFun_symbol = Symbol.symbol isMetaIdFun_name

val isCharFun_name = "char?"
val isCharFun_symbol = Symbol.symbol isCharFun_name

val isListFun_name = "list?"
val isListFun_symbol = Symbol.symbol isListFun_name

val varToStringFun_name = "var->string"
val varToStringFun_symbol = Symbol.symbol varToStringFun_name

val makeCharFun_name = "char"
val makeCharFun_symbol = Symbol.symbol makeCharFun_name

val charOrdFun_name = "char-ord"
val charOrdFun_symbol = Symbol.symbol charOrdFun_name

val compareCharsFun_name = "compare-chars"
val compareCharsFun_symbol = Symbol.symbol compareCharsFun_name

val compareStringsFun_name = "compare-strings"
val compareStringsFun_symbol = Symbol.symbol compareStringsFun_name

val getSigFun_name = "get-signature"
val getSigFun_symbol = Symbol.symbol getSigFun_name

val getAllStructures_name = "all-structures"
val getAllStructures_symbol = Symbol.symbol getAllStructures_name

val symbolToStringFun_name = "symbol->string"
val symbolToStringFun_symbol = Symbol.symbol symbolToStringFun_name

val stringToVarFun_name = "string->var"
val stringToVarFun_symbol = Symbol.symbol stringToVarFun_name

val unifyFun_name = "unify"
val unifyFun_symbol = Symbol.symbol unifyFun_name

val matchFun_name = "match-terms"
val matchFun_symbol = Symbol.symbol matchFun_name

val isSortInstanceFun_name = "sort-instance?"
val isSortInstanceFun_symbol = Symbol.symbol isSortInstanceFun_name

val sortInstancePrimMethod_name = "sort-instance"
val sortInstancePrimMethod_symbol = Symbol.symbol sortInstancePrimMethod_name

val getRewritesFun_name = "get-all-rewrites"
val getRewritesFun_symbol = Symbol.symbol getRewritesFun_name 

val rewriteSearchFun_name = "sml-rewrite-search"
val rewriteSearchFun_symbol = Symbol.symbol rewriteSearchFun_name

val extendSubFun_name = "extend-sub"
val extendSubFun_symbol = Symbol.symbol extendSubFun_name

val suppFun_name = "supp"
val suppFun_symbol = Symbol.symbol suppFun_name

val ranVarFun_name = "range-vars"
val ranVarFun_symbol = Symbol.symbol ranVarFun_name

val empty_sub_name = "empty-sub"
val empty_sub_symbol = Symbol.symbol empty_sub_name

val expandNextProofFun_name = "expand-next-proof"
val expandNextProofFun_symbol = Symbol.symbol expandNextProofFun_name

val option_structure_name = "Option"
val option_structure_symbol = Symbol.symbol option_structure_name
val moption_structure_symbol = ModSymbol.makeModSymbol([],option_structure_symbol,option_structure_symbol)

val mpPrimMethod_name = "mp"
val mpPrimMethod_symbol = Symbol.symbol mpPrimMethod_name

val pfPrimMethod_name = "prove-from"
val pfPrimMethod_symbol = Symbol.symbol pfPrimMethod_name

val spfPrimMethod_name = "sprove-from"
val spfPrimMethod_symbol = Symbol.symbol spfPrimMethod_name

val uspfPrimMethod_name = "usprove-from"
val uspfPrimMethod_symbol = Symbol.symbol uspfPrimMethod_name

val vpfPrimMethod_name = "vprove-from"
val vpfPrimMethod_symbol = Symbol.symbol vpfPrimMethod_name

val mvpfPrimMethod_name = "mono-vprove-from"
val mvpfPrimMethod_symbol = Symbol.symbol mvpfPrimMethod_name

val uvpfPrimMethod_name = "uvprove-from"
val uvpfPrimMethod_symbol = Symbol.symbol uvpfPrimMethod_name


val paradoxPrimFun_name = "get-model"
val paradoxPrimFun_symbol = Symbol.symbol paradoxPrimFun_name

val getMultisortedModelPrimFun_name = "get-multi-sorted-model"
val getMultisortedModelPrimFun_symbol = Symbol.symbol getMultisortedModelPrimFun_name

val gpfPrimMethod_name = "gprove-from"
val gpfPrimMethod_symbol = Symbol.symbol gpfPrimMethod_name

val lookUpEnvBindingFun_name = "look-up-top-value"
val lookUpEnvBindingFun_symbol = Symbol.symbol lookUpEnvBindingFun_name
val mlookUpEnvBindingFun_symbol = ModSymbol.makeModSymbol([],lookUpEnvBindingFun_symbol,lookUpEnvBindingFun_symbol)

val makePathFun_name = "make-path"
val makePathFun_symbol = Symbol.symbol makePathFun_name

val root_dir_name = "ROOT_DIR"
val root_dir_symbol = Symbol.symbol root_dir_name

val athena_home_name = "ATHENA_HOME"
val athena_home_symbol = Symbol.symbol athena_home_name


val dnPrimMethod_name = "dn"
val dnPrimMethod_symbol = Symbol.symbol dnPrimMethod_name

val fail_method_name = "fail"
val fail_method_symbol = Symbol.symbol fail_method_name 

val renameSortVarsFun_name = "rename-sort-vars"
val renameSortVarsFun_symbol = Symbol.symbol renameSortVarsFun_name
val renameSortVarsLstFun_name = "rename-sort-vars*"
val renameSortVarsLstFun_symbol = Symbol.symbol renameSortVarsLstFun_name

val abTagFun_name = "ab-tag"
val abTagFun_symbol = Symbol.symbol abTagFun_name

val matchPropsFun_name = "match-props"
val matchPropsFun_symbol = Symbol.symbol matchPropsFun_name

val matchProps3Fun_name = "match-props-3"
val matchProps3Fun_symbol = Symbol.symbol matchProps3Fun_name

val bothPrimMethod_name = "both"
val bothPrimMethod_symbol = Symbol.symbol bothPrimMethod_name

val conjIntroPrimMethod_name = "and-intro"
val conjIntroPrimMethod_symbol = Symbol.symbol conjIntroPrimMethod_name

val absurdPrimMethod_name = "absurd"
val absurdPrimMethod_symbol = Symbol.symbol absurdPrimMethod_name

val claimPrimMethod_name = "claim"
val claimPrimMethod_symbol = Symbol.symbol claimPrimMethod_name

val leftAndPrimMethod_name = "left-and"
val leftAndPrimMethod_symbol = Symbol.symbol leftAndPrimMethod_name

val rightAndPrimMethod_name = "right-and"
val rightAndPrimMethod_symbol = Symbol.symbol rightAndPrimMethod_name

val equivPrimMethod_name = "equiv"
val equivPrimMethod_symbol = Symbol.symbol equivPrimMethod_name


val leftIffPrimMethod_name = "left-iff"
val leftIffPrimMethod_symbol = Symbol.symbol leftIffPrimMethod_name

val rightIffPrimMethod_name = "right-iff"
val rightIffPrimMethod_symbol = Symbol.symbol rightIffPrimMethod_name

val cdPrimMethod_name = "cases"
val cdPrimMethod_symbol = Symbol.symbol cdPrimMethod_name

val leftEitherPrimMethod_name = "left-either"
val leftEitherPrimMethod_symbol = Symbol.symbol leftEitherPrimMethod_name

val rightEitherPrimMethod_name = "right-either"
val rightEitherPrimMethod_symbol = Symbol.symbol rightEitherPrimMethod_name

val eitherPrimMethod_name = "either"
val eitherPrimMethod_symbol = Symbol.symbol eitherPrimMethod_name

val uspecPrimMethod_name = "uspec"
val uspecPrimMethod_symbol = Symbol.symbol uspecPrimMethod_name

val egenPrimMethod_name = "egen"
val egenPrimMethod_symbol = Symbol.symbol egenPrimMethod_name

val egenUniquePrimMethod_name = "egen-unique"
val egenUniquePrimMethod_symbol = Symbol.symbol egenUniquePrimMethod_name

val eqReflexPrimMethod_name = "reflex"
val eqReflexPrimMethod_symbol = Symbol.symbol eqReflexPrimMethod_name

val floorFun_name = "floor"
val floorFun_symbol = Symbol.symbol floorFun_name

val ceilFun_name = "ceil"
val ceilFun_symbol = Symbol.symbol ceilFun_name

val eqTranPrimMethod_name = "tran"
val eqTranPrimMethod_symbol = Symbol.symbol eqTranPrimMethod_name

val eqSymPrimMethod_name = "sym"
val eqSymPrimMethod_symbol =  Symbol.symbol eqSymPrimMethod_name

val true_intro_PrimMethod_name = "true-intro"
val true_intro_PrimMethod_symbol = Symbol.symbol true_intro_PrimMethod_name

val rcongPrimMethod_name = "rcong"
val rcongPrimMethod_symbol = Symbol.symbol rcongPrimMethod_name

val fcongPrimMethod_name = "fcong"
val fcongPrimMethod_symbol = Symbol.symbol fcongPrimMethod_name

val appMethod_method_name = "app-method"
val appMethod_method_symbol = Symbol.symbol appMethod_method_name 

val thread_method_name = "thread-methods"
val thread_method_symbol = Symbol.symbol thread_method_name

val appProc_proc_name = "app-proc"
val appProc_proc_symbol = Symbol.symbol appProc_proc_name 

val top_level_name = "standard input"



val pos_int_sort_symbol = Symbol.symbol "PosInt"
val neg_int_sort_symbol = Symbol.symbol "NegInt"
val non_neg_int_sort_symbol = Symbol.symbol "NonNegInt"
val int_sort_name =  "Int"
val int_sort_symbol = Symbol.symbol int_sort_name
val mint_sort_symbol =  ModSymbol.makeModSymbol([],int_sort_symbol,int_sort_symbol)
val real_sort_name = "Real"
val real_sort_symbol = Symbol.symbol real_sort_name
val mreal_sort_symbol =  ModSymbol.makeModSymbol([],real_sort_symbol,real_sort_symbol)
val boolean_sort_name =   "Boolean"
val boolean_sort_symbol =  Symbol.symbol boolean_sort_name
val mboolean_sort_symbol =  ModSymbol.makeModSymbol([],boolean_sort_symbol,boolean_sort_symbol)

val ide_sort_name = "Ide"
val ide_sort_symbol = Symbol.symbol ide_sort_name
val mide_sort_symbol =  ModSymbol.makeModSymbol([],ide_sort_symbol,ide_sort_symbol)

val smtSolveFun_name = "smt-solve"
val smtSolveFun_symbol = Symbol.symbol smtSolveFun_name

val yicesSolveFun_name = "yices-solve"
val yicesSolveFun_symbol = Symbol.symbol yicesSolveFun_name

val cvcSolveFun_name = "cvc-solve"
val cvcSolveFun_symbol = Symbol.symbol cvcSolveFun_name

val yicesSolveFun_name' = "yices-solve-2"
val yicesSolveFun_symbol' = Symbol.symbol yicesSolveFun_name'

val smt_poly_con_name_prefix = "p"
val smt_var_prefix = "v"
val smt_fsym_prefix = "f"

val unifiable_sort_fun_name = "unifiable-sorts?"
val unifiable_sort_fun_symbol = Symbol.symbol unifiable_sort_fun_name

val nnf_fun_name = "nnf"
val nnf_fun_symbol = Symbol.symbol nnf_fun_name

val print_var_sorts_flag = "print-var-sorts"
val print_var_sorts_flag_symbol = Symbol.symbol print_var_sorts_flag
val print_qvar_sorts_flag = "print-qvar-sorts"
val print_qvar_sorts_flag_symbol = Symbol.symbol print_qvar_sorts_flag

val debug_mode_flag = "debug-mode"
val debug_mode_flag_symbol = Symbol.symbol debug_mode_flag
     
val infix_parsing_flag = "infix-parsing"
val infix_parsing_flag_symbol = Symbol.symbol infix_parsing_flag 

val auto_assert_dt_axioms_flag = "auto-assert-dt-axioms"
val auto_assert_dt_axioms_flag_symbol = Symbol.symbol auto_assert_dt_axioms_flag

val auto_assert_selector_axioms_flag = "auto-assert-selector-axioms"
val auto_assert_selector_axioms_flag_symbol = Symbol.symbol auto_assert_selector_axioms_flag

val ATPs_in_chain_flag = "atps-with-chain"
val ATPs_in_chain_flag_symbol = Symbol.symbol ATPs_in_chain_flag

val option_valued_selectors_flag = "option-valued-selectors"
val option_valued_selectors_flag_symbol =  Symbol.symbol option_valued_selectors_flag

val demons_active_flag = "demons"
val demons_active_flag_symbol = Symbol.symbol demons_active_flag

val silent_mode_flag_name = "silent-mode"
val silent_mode_flag_symbol = Symbol.symbol silent_mode_flag_name

val check_fun_defs = "check-function-axioms"
val check_fun_defs_symbol = Symbol.symbol check_fun_defs

val infix_app_style_flag = "infix-app-style"
val infix_app_style_flag_symbol = Symbol.symbol infix_app_style_flag

val fundef_mlstyle_flag = "mlstyle-fundef"
val fundef_mlstyle_flag_symbol = Symbol.symbol fundef_mlstyle_flag

val proof_tracking_flag = "proof-tracking"
val proof_tracking_flag_symbol = Symbol.symbol proof_tracking_flag

val simplify_fun_def_flag = "simplify-fun-defs"
val simplify_fun_def_flag_symbol = Symbol.symbol simplify_fun_def_flag

val explicit_wildcard_patterns_flag = "explicit-wildcard-patterns"
val explicit_wildcard_patterns_flag_symbol = Symbol.symbol explicit_wildcard_patterns_flag

val compile_mode_flag = "incremental-compile-mode"
val compile_mode_flag_symbol = Symbol.symbol compile_mode_flag

val dom_as_dt_default_size_flag = "dom-dt-default-size"
val dom_as_dt_default_size_flag_symbol = Symbol.symbol dom_as_dt_default_size_flag

val call_stack_size_limit_flag = "call-stack-size-limit"
val call_stack_size_limit_flag_symbol = Symbol.symbol call_stack_size_limit_flag

val init_call_stack_chunk_size_flag = "init-call-stack-chunk-size"
val init_call_stack_chunk_size_flag_symbol =  Symbol.symbol init_call_stack_chunk_size_flag

val top_call_stack_portion_size_flag = "top-call-stack-portion-size"
val top_call_stack_portion_size_flag_symbol = Symbol.symbol top_call_stack_portion_size_flag

val HT_dispatch_name = "hashing-dispatch-procedure"
val HT_dispatch_symbol = Symbol.symbol HT_dispatch_name

val TermHT_dispatch_name = "term-hashing-dispatch-procedure"
val TermHT_dispatch_symbol = Symbol.symbol TermHT_dispatch_name


val makeHTFun_name = "make-hash-table"
val makeHTFun_symbol = Symbol.symbol makeHTFun_name

val HT_lookup_name = "look-up"
val HT_lookup_symbol = Symbol.symbol HT_lookup_name

val TermHT_lookup_name = "look-up-term"
val TermHT_lookup_symbol = Symbol.symbol TermHT_lookup_name

val HT_enter_name = "enter"
val HT_enter_symbol = Symbol.symbol HT_enter_name

val HT_remove_name = "remove"
val HT_remove_symbol = Symbol.symbol HT_remove_name

val HT_clear_name = "clear"
val HT_clear_symbol = Symbol.symbol HT_clear_name

val TermHT_enter_name = "enter-term"
val TermHT_enter_symbol = Symbol.symbol TermHT_enter_name

val TermHT_remove_name = "term-table-remove" 
val TermHT_remove_symbol = Symbol.symbol TermHT_remove_name

val TermHT_clear_name = "term-table-clear" 
val TermHT_clear_symbol = Symbol.symbol TermHT_clear_name

val HT_show_name = "show"
val HT_show_symbol = Symbol.symbol HT_show_name

val TermHT_show_name = "term-show"
val TermHT_show_symbol = Symbol.symbol HT_show_name 

val HT_size_name = "size"
val HT_size_symbol = Symbol.symbol HT_size_name

val TermHT_size_name = "term-size"
val TermHT_size_symbol = Symbol.symbol TermHT_size_name

val getPatternsFun_name = "get-all-remaining-patterns"
val getPatternsFun_symbol = Symbol.symbol getPatternsFun_name

val makeTermHTFun_name = "make-term-hash-table"
val makeTermHTFun_symbol = Symbol.symbol makeTermHTFun_name

val unparseFun_name = "unparse"
val unparseFun_symbol = S.symbol unparseFun_name

val unparsePlainFun_name = "unparse-plain"
val unparsePlainFun_symbol = S.symbol unparsePlainFun_name

val satFun_name = "sat-solve"
val satFun_symbol = S.symbol satFun_name 

val cnfFun_name = "cnf-core"
val cnfFun_symbol = S.symbol cnfFun_name 

val isSatFun_name = "sat?"
val isSatFun_symbol = S.symbol isSatFun_name 

val fastSatFun_name = "fsat"
val fastSatFun_symbol = S.symbol fastSatFun_name

val random_int_name = "random-int"
val random_int_symbol = Symbol.symbol random_int_name

val epfPrimMethod_name = "eprove-from"
val epfPrimMethod_symbol = S.symbol epfPrimMethod_name
    
val timeFun_name = "time"
val timeFun_symbol = Symbol.symbol timeFun_name

val timeoutFun_name = "time-out"
val timeoutFun_symbol = Symbol.symbol timeoutFun_name

val timeoutMethod_name = "dtime-out"
val timeoutMethod_symbol = Symbol.symbol timeoutMethod_name

val lenFun_name = "length"
val lenFun_symbol = Symbol.symbol lenFun_name

val getPrecedence_name = "get-precedence" 
val getPrecedence_symbol = Symbol.symbol getPrecedence_name

val getAssoc_name = "get-assoc" 
val getAssoc_symbol = Symbol.symbol getAssoc_name

val infix_op_name = "BOP"

val max_int_name = "max-int"
val max_int_symbol = Symbol.symbol max_int_name

val getFlagFun_name = "get-flag"
val getFlagFun_symbol = Symbol.symbol getFlagFun_name

val getBoolFlagFun_name = "get-boolean-flag"
val getBoolFlagFun_symbol = Symbol.symbol getBoolFlagFun_name

val makeServerFun_name = "make-server"
val makeServerFun_symbol = Symbol.symbol makeServerFun_name 

val evalFun_name = "evaluate"
val evalFun_symbol = Symbol.symbol evalFun_name

val unparseFun_name = "unparse"
val unparseFun_symbol = Symbol.symbol unparseFun_name

val processInputFun_name = "process-input-from-string"
val processInputFun_symbol = Symbol.symbol processInputFun_name

val allFunSymsFun_name = "get-fsyms"
val allFunSymsFun_symbol = Symbol.symbol allFunSymsFun_name

val standardEvalProcNameTailCharacter = #"`"
val standardReduceProcNameTailCharacter = #"R"
val standardReduceProcNameTailString = Char.toString(standardReduceProcNameTailCharacter)

val standardDeductiveEvalNamePrefix = "d"
val standardDeductiveEvalNamePrefix_char = #"d"

val defEqnsFun_name = "defining-axioms"
val defEqnsFun_symbol = Symbol.symbol defEqnsFun_name

fun isSortVar(str) = let val str_lst = explode str
    	   	 in 
                    not(null(str_lst)) andalso  hd(str_lst) = sort_variable_prefix_as_char
                 end


val makeMapFun_name = "make-empty-map"
val makeMapFun_symbol = Symbol.symbol makeMapFun_name 

val empty_mapping_name = "generic-empty-mapping"
val empty_mapping_symbol = Symbol.symbol empty_mapping_name

val makeMapFromListFun_name = "make-map"
val makeMapFromListFun_symbol = Symbol.symbol makeMapFromListFun_name

val mapSizeFun_name = "map-size"
val mapSizeFun_symbol = Symbol.symbol mapSizeFun_name

val mapKeysFun_name = "map-keys"
val mapKeysFun_symbol = Symbol.symbol mapKeysFun_name

val mapValuesFun_name = "map-values"
val mapValuesFun_symbol = Symbol.symbol mapValuesFun_name

val mapKeyValuesFun_name = "map-key-values"
val mapKeyValuesFun_symbol = Symbol.symbol mapKeyValuesFun_name

val mapToValuesFun_name = "map-to-values"
val mapToValuesFun_symbol = Symbol.symbol mapToValuesFun_name

val mapApplyFun_name = "map-apply"
val mapApplyFun_symbol = Symbol.symbol mapApplyFun_name

val mapToKeyValuesFun_name = "map-to-key-values"
val mapToKeyValuesFun_symbol = Symbol.symbol mapToKeyValuesFun_name

val applyToKeyValuesFun_name = "apply-to-key-values"
val applyToKeyValuesFun_symbol = Symbol.symbol applyToKeyValuesFun_name

val mapFoldlFun_name = "map-foldl"
val mapFoldlFun_symbol = Symbol.symbol mapFoldlFun_name


val makeTableFun_name = "table"
val makeTableFun_symbol = Symbol.symbol makeTableFun_name 

val addTableFun_name = "table-add"
val addTableFun_symbol = Symbol.symbol addTableFun_name

val map_key_val_separator = ":="

val addMapFun_name = "map-add"
val addMapFun_symbol = Symbol.symbol addMapFun_name

val removeMapFun_name = "map-remove"
val removeMapFun_symbol = Symbol.symbol removeMapFun_name


val removeTableFun_name = "table-remove"
val removeTableFun_symbol = Symbol.symbol removeTableFun_name

val findTableFun_name = "table-lookup"
val findTableFun_symbol = Symbol.symbol findTableFun_name

val findMapFun_name = "map-lookup"
val findMapFun_symbol = Symbol.symbol findMapFun_name

val tableSizeFun_name = "table-size"
val tableSizeFun_symbol = Symbol.symbol tableSizeFun_name

val tableClearFun_name = "table-clear"
val tableClearFun_symbol = Symbol.symbol tableClearFun_name

val tableToStringFun_name = "table->string"
val tableToStringFun_symbol = Symbol.symbol tableToStringFun_name

val tableToListFun_name = "table->list"
val tableToListFun_symbol = Symbol.symbol tableToListFun_name

val moduleSizeFun_name = "module-size"
val moduleSizeFun_symbol = Symbol.symbol moduleSizeFun_name
val mmoduleSizeFun_symbol = ModSymbol.makeModSymbol([],moduleSizeFun_symbol,moduleSizeFun_symbol)

val moduleSizeFun1_name = "module-size1"
val moduleSizeFun1_symbol = Symbol.symbol moduleSizeFun1_name
val mmoduleSizeFun1_symbol = ModSymbol.makeModSymbol([],moduleSizeFun1_symbol,moduleSizeFun1_symbol)

val submodulesFun_name = "sub-modules"
val submodulesFun_symbol = Symbol.symbol submodulesFun_name

val moduleAbFun_name = "module-ab"
val moduleAbFun_symbol = Symbol.symbol moduleAbFun_name

val built_in_merge_sort_name = "sort"
val built_in_merge_sort_symbol = Symbol.symbol built_in_merge_sort_name

val built_in_merge_sort_name' = "sort'"
val built_in_merge_sort_symbol' = Symbol.symbol built_in_merge_sort_name'

val moduleAppFun_name = "apply-module"
val moduleAppFun_symbol = Symbol.symbol moduleAppFun_name
val mmoduleAppFun_symbol = ModSymbol.makeModSymbol([],moduleAppFun_symbol,moduleAppFun_symbol)

val moduleToStringFun_name = "module->string"
val moduleToStringFun_symbol = Symbol.symbol moduleToStringFun_name
val mmoduleToStringFun_symbol = ModSymbol.makeModSymbol([],moduleToStringFun_symbol,moduleToStringFun_symbol)

val moduleToHtFun_name = "module->table"
val moduleToHtFun_symbol = Symbol.symbol moduleToHtFun_name
val mmoduleToHtFun_symbol = ModSymbol.makeModSymbol([],moduleToHtFun_symbol,moduleToHtFun_symbol)

val moduleDomFun_name = "module-domain"
val moduleDomFun_symbol = Symbol.symbol moduleDomFun_name
val mmoduleDomFun_symbol = ModSymbol.makeModSymbol([],moduleDomFun_symbol,moduleDomFun_symbol)

val module_fun_msymbols = [mmoduleSizeFun_symbol,mmoduleAppFun_symbol,mmoduleToStringFun_symbol,mmoduleDomFun_symbol]

val top_module_name = "Top"
val top_module_symbol = Symbol.symbol top_module_name

val built_in_file_names = ["rewriting.ath","util.ath","list.ath","msr.ath","property-management.ath","options.ath","fundef.ath","property-management.ath"]

val SMT_mono_sort_instantiation_of_poly_sort_char_separator = #"%"
val SMT_mono_sort_instantiation_of_poly_sort_char_separator_as_string = "%"
val CVC_mono_sort_instantiation_of_poly_sort_char_separator = #"~"
val CVC_mono_sort_instantiation_of_poly_sort_char_separator_as_string = "~"


val MOR_name = "MOR"
val MOR_symbol = Symbol.symbol MOR_name 
val mMOR_symbol = ModSymbol.makeModSymbol([],MOR_symbol,MOR_symbol)

val assertPrologFun_name = "prolog-assert"
val assertPrologFun_symbol =  Symbol.symbol assertPrologFun_name

val retractPrologFun_name = "prolog-retract"
val retractPrologFun_symbol =  Symbol.symbol retractPrologFun_name

val loadPrologFun_name = "prolog-load"
val loadPrologFun_symbol =  Symbol.symbol loadPrologFun_name

val queryPrologFun_name = "prolog-query"
val queryPrologFun_symbol = Symbol.symbol queryPrologFun_name

val double_colon_cons_name = "::"
val double_colon_cons_symbol = Symbol.symbol double_colon_cons_name
val mdouble_colon_cons_symbol = ModSymbol.makeModSymbol([],double_colon_cons_symbol,double_colon_cons_symbol)

val escapeStringFun_name = "escape-string"
val escapeStringFun_symbol = Symbol.symbol escapeStringFun_name

fun getSafeName(str) = "("^lookUpEnvBindingFun_name^" "^"\""^(Symbol.makePrivateString(str))^"\""^")"

val spass_windows_binary = (case Paths.findFileWithPossibleSuffix("SPASS",".exe") of
              	                  SOME(str) => str
				  | _ => "SPASS")

val spass_binary = if (Paths.is_unix) then Paths.findIterated(["spass","SPASS"],"./SPASS") else spass_windows_binary

val vampire_linux_binary = Paths.findIterated(["vampire_z3_rel_static_sledge_5980"],"./vampire_z3_rel_static_sledge_5980")
			     
val vampire_binary = (case Paths.findFileWithPossibleSuffix("vampire",".exe") of
                                   SOME(str) => str
                                 | _ => vampire_linux_binary)

val cvc4_binary = "cvc4"

val minisat_binary = (case Paths.findFileWithPossibleSuffix("minisat",".exe") of
                             SOME(str) => str
                          | _ => "minisat")

end

