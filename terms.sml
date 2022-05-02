(*======================================================================

Auxiliary code for dealing with the various types of Athena terms (e.g.,
conversions from one type to another).

=======================================================================*)

structure Terms =
struct

structure ATV = AthTermVar
structure AT = AthTerm
structure MS = ModSymbol

fun areVars([]) = true
  | areVars(t::more) = case AthTerm.isVarOpt(t) of NONE => false | _ => areVars(more)

val (SymTermToFTerm,SymTermsToFTerms) = 
    let fun convert(terms) = 
          let  val vars = SymTerm.getVarsLst(terms)
	       val new_vars = map (fn (_) => FTerm.makeFreshVar()) vars 
	       val empty_mapping = Symbol.empty_mapping
	       val mapping = Symbol.enterLst(empty_mapping,Basic.zip(vars,new_vars))
               fun doIt(t) = 
                   case SymTerm.isVar(t) of 
                      SOME(v) => (case Symbol.lookUp(mapping,v) of
			 	        SOME(v') => v' 
                                      | _ => raise Basic.Never)
                    | NONE => (case SymTerm.isApp(t) of
                                  SOME(fsym,args) =>    
                                    let val arg_results = map doIt args
                                        in
                                          FTerm.makeApp(fsym,arg_results)
                                    end
                                | _ => raise Basic.Never)
               in
                  map doIt terms 
          end
        in
          (fn (t) => convert([t]),fn (terms) => convert(terms))
    end

val (SymTermToFTermWithSub,SymTermsToFTermsWithSub) = 
    let fun convert(terms) = 
          let  val vars = SymTerm.getVarsLst(terms)
	       val new_vars = map (fn (_) => FTerm.makeFreshVar()) vars 
	       val empty_mapping = Symbol.empty_mapping
	       val mapping = Symbol.enterLst(empty_mapping,Basic.zip(vars,new_vars))
               fun doIt(t) = 
                   case SymTerm.isVar(t) of 
                      SOME(v) => (case Symbol.lookUp(mapping,v) of
			 	        SOME(v') => v' 
                                      | _ => raise Basic.Never)
                    | NONE => (case SymTerm.isApp(t) of
                                  SOME(fsym,args) =>    
                                    let val arg_results = map doIt args
                                        in
                                          FTerm.makeApp(fsym,arg_results)
                                    end
                                | _ => raise Basic.Never)
               in
                  (map doIt terms,mapping)
          end
        in
          (fn (t) => convert([t]),fn (terms) => convert(terms))
    end

fun carbonSymTermToFTerm(t) = 
          let  val vars = SymTerm.getVars(t)
	       val new_vars = map (fn (sym_var) => let val str = Symbol.name(sym_var)
                                                       val str' = String.substring(str,2,String.size(str)-2)
                                                   in
                                                      FTerm.makeVar(InfNum.tag(InfNum.fromString(str')))
                                                   end) vars
	       val empty_mapping = Symbol.empty_mapping
	       val mapping = Symbol.enterLst(empty_mapping,Basic.zip(vars,new_vars))
               fun doIt(t) = 
                   case SymTerm.isVar(t) of 
                      SOME(v) => (case Symbol.lookUp(mapping,v) of
			 	        SOME(v') => v' 
                                      | _ => raise Basic.Never)
                    | NONE => (case SymTerm.isApp(t) of
                                  SOME(fsym,args) =>    
                                    let val arg_results = map doIt args
                                        in
                                          FTerm.makeApp(fsym,arg_results)
                                    end
                                | _ => raise Basic.Never)
          in 
            doIt(t)
          end
     
fun printSymTerm(t) = 
    (case SymTerm.isVar t of 
        SOME(sym) => Symbol.name(sym)
      | _ => (case SymTerm.isApp t of
                 SOME(f,[]) => MS.name(f)
               | SOME(f,args) => MS.name(f)^"("^printSymTerms(args)
               | _ => ""))
and
   printSymTerms([]) = ""
 | printSymTerms([t]) = printSymTerm(t)^")"
 | printSymTerms(t::more) = printSymTerm(t)^","^printSymTerms(more)

fun printSymTermSExp(t) = 
    (case SymTerm.isVar t of 
        SOME(sym) => (Symbol.name(sym))
      | _ => (case SymTerm.isApp t of
                 SOME(f,[]) => MS.name(f)
               | SOME(f,args) => "("^MS.name(f)^" "^printSymTermsSExp(args)
               | _ => ""))
and
   printSymTermsSExp([]) = ""
 | printSymTermsSExp([t]) = printSymTermSExp(t)^")"
 | printSymTermsSExp(t::more) = printSymTermSExp(t)^" "^printSymTermsSExp(more)

fun putBogusTags(t:SymTerm.term,tag) = 
(* Takes a symterm t and a bogus tag and makes a tagged symterm out of t *)
(* by attaching the bogus tag to each node. *)
      case SymTerm.isConstant(t) of
         SOME(c) => SymTerm.makeTaggedConstant(c,tag)
       | _ => (case SymTerm.isVar(t) of
                  SOME(v) => SymTerm.makeTaggedVar(v,tag)
                | _ => (case SymTerm.isApp(t) of 
                           SOME(f,args) => SymTerm.makeTaggedApp(f,tag,
                                                                 map (fn t => putBogusTags(t,tag)) args)
                         | _ => raise Basic.Never))

fun replaceSymTermConstants(t,f) = 
(* This function takes a SymTerm t and a function f from symbols to symterm option *)
(* and replaces every constant c in t such that f(c) != NONE by the corresponding symterm. *)
   case SymTerm.isConstant(t) of 
      SOME(c) => (case f(c) of
		     SOME(t') => t'
                   | _ => t)
    | _ => (case SymTerm.isApp(t) of
               SOME(root_sym,terms) => SymTerm.makeApp(root_sym,
                                                       map (fn t => replaceSymTermConstants(t,f)) terms)
             | _ => t)

fun replaceTaggedSymTermConstants(t,f,bogus_tag) = 
   case SymTerm.isTaggedConstant(t) of 
      SOME(c,tag) => (case f(c) of
		         SOME(t') => putBogusTags(t',bogus_tag)
                       | _ => t)
    | _ => (case SymTerm.isTaggedApp(t) of
               SOME(root_sym,tag,args) => SymTerm.makeTaggedApp(root_sym,tag,
                                          map (fn t => replaceTaggedSymTermConstants(t,f,bogus_tag)) args)
             | _ => t)

fun msym(s) = ModSymbol.makeModSymbol([],s,s)

fun taggedSymConstantsToVars(t,vars) = 
      let val mvars = map msym vars 
          fun f(t) = (case SymTerm.isTaggedConstant(t) of
                         SOME(fsym,tag) => if Basic.isMemberEq(fsym,mvars,MS.modSymEq) then
                                              SymTerm.makeTaggedVar(MS.lastName(fsym),tag)
                                       else t
                       | _ => (case SymTerm.isTaggedApp(t) of
                                  SOME(fsym,tag,args) => SymTerm.makeTaggedApp(fsym,tag,
                                                         (map f args))
                                | _ => t))
      in 
         f(t)
      end

fun subToString(sub:AthTerm.sub) =
     let val supp_vars = AthTerm.supp(sub)
         val sortVarPrinter = FTerm.varToString
         val terms = AthTerm.applySubLst(sub,(map AthTerm.makeVar supp_vars))
         val pairs = ListPair.zip(supp_vars,terms)
         fun printPairs([]) = ""
           | printPairs([(v,t)]) = ATV.toString(v,sortVarPrinter)^" --> "^AT.toString(t,sortVarPrinter)^"}"
           | printPairs((v,t)::more) =  ATV.toString(v,sortVarPrinter)^" --> "^
					AT.toString(t,sortVarPrinter)^"\n"^printPairs(more)
        val init = if length(supp_vars) < 2 then "" else "\n"
     in
        if null(supp_vars) then "{}" else
           init^"{"^printPairs(pairs)
     end

fun printSub(sub:AthTerm.sub) = print(subToString(sub))
fun printAthTermVar(v) = ATV.toString(v,FTerm.varToString)
fun printFTermSExp(t) = FTerm.toString(t,FTerm.varToString)
fun printAthTermSExp(t) = AT.toString(t,FTerm.varToString)

exception SymTermParsingError of string

(***
Note: The parseSymTerm function should be extended to make sure that it can properly 
parse module-based term constants such as A.B.foo: 
***)

fun parseSymTerm(str,isVar) = 
  let datatype token = ID of string | LPAREN | RPAREN
      fun tokenize(str:string):token list =
           let val clist = explode str
	       val (lp,rp) = (#"(",#")")
	       fun stopper(c) = c = lp orelse c = rp orelse Basic.isWhiteSpace(c)
	       fun getWord([],res) = (implode (rev res),[])
		 | getWord(c::rest,res) = if not(stopper(c)) then getWord(rest,c::res)
					  else (implode (rev res),c::rest)
	       fun f([],res) = rev res
		 | f(chars,res) = (case Basic.skipWhiteSpace(chars) of
				      [] => rev res 
				    | c::rest => if c = lp then f(rest,LPAREN::res)
						 else if c = rp then f(rest,RPAREN::res)
					              else let val (w,rem) = getWord(c::rest,[])
							   in
							      f(rem,(ID w)::res)
							   end)
	   in
              f(clist,[])
	   end
      fun error(msg) = raise SymTermParsingError(msg)
      fun p(ID(str)::rest) = if isVar(str) then (SymTerm.makeVar(Symbol.symbol(str)),rest)
                             else (SymTerm.makeConstant(msym (Symbol.symbol str)),rest)
        | p(LAREN::ID(str)::rest) = let val (terms,rem) = pLst(rest,[])
			     	    in
				     (case rem of
					 RPAREN::rem' => if isVar(str) then error("Invalid variable occurrence.")
							 else (SymTerm.makeApp(msym (Symbol.symbol str),terms),rem')
				       | _ => error("Right parenthesis missing."))
				    end
       | p(_) = error("Left parenthesis or identifier expected.")
     and okAhead(ID(_)::_) = true
       | okAhead(LPAREN::_) = true
       | okAhead(_) = false
     and pLst([],res) = (rev res,[])
       | pLst(toks,res) = if okAhead(toks) then 
			     (case p(toks) of
			         (t,rest) => if okAhead(rest) then pLst(rest,t::res) else (rev (t::res),rest))
                          else (rev res,toks)
  in
      SOME(#1(p(tokenize(str)))) handle _ => NONE
  end

fun isSymTermLegalSort(t:SymTerm.term) = 
   let fun isLegalVar(sym) = hd(explode(Symbol.name(sym))) = Names.sort_variable_prefix_as_char
   in 
      SymTerm.isLegal(t,Data.sortConstructorArity,isLegalVar)
   end

fun stringsToAthVar([str]) = 
      let fun pred(#":") = true
            | pred(_) = false
          val tokens = String.tokens pred str 
      in
         (case tokens of 
             [str1] => if AbstractSyntax.canBeId(str1) then SOME(ATV.athTermVar(str1)) else NONE
           | [str1,str2] => if AbstractSyntax.canBeId(str1) then 
                               (case parseSymTerm(str2,Names.isSortVar) of 
                                   SOME(sterm) => if isSymTermLegalSort(sterm) then 
                                                     SOME(ATV.athTermVarWithSort(str1,Basic.first(SymTermToFTerm(sterm))))
                                                  else NONE
                                 | _ => NONE)
                            else NONE
           | _ => NONE)
      end
  | stringsToAthVar([str1,str2]) = 
      if AbstractSyntax.canBeId(str1) then 
         (case parseSymTerm(str2,Names.isSortVar) of 
             SOME(sterm) => if isSymTermLegalSort(sterm) then  
                               SOME(ATV.athTermVarWithSort(str1,Basic.first(SymTermToFTerm(sterm))))
                            else NONE
           | _ => NONE)
      else NONE 
  | stringsToAthVar(_) = NONE

end 

