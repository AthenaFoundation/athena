(*======================================================================

This file defines Athena's abstract syntax and implements related functionality
(such as code for computing free identifier occurrences). The main datatypes are
expression, deduction, phrase, and pattern. Values of these types are tagged
with position information (line, column number, and file name).

=======================================================================*)

structure AbstractSyntax = 

struct

structure S = Symbol
structure MS = ModSymbol

structure N = Names

val dummy_sym = S.symbol ")!dum_sym" 

val posToString = Position.posToString

type position = Position.PosType 

type pos = position

type symbol = Symbol.symbol

type mod_symbol = ModSymbol.mod_symbol

val dum_pos = Position.dummy_pos

exception SyntaxError of string * (position option)

fun commaHere(pos) = raise SyntaxError("A comma was expected here", SOME pos)

exception LexError of string * (position option)

type absyn_term = position SymTerm.tagged_term

type param = {name:symbol, pos:position}

fun getParams1(plist) = 
     let fun f([]:param list,names,res) = rev(res)
           | f((p as {name,pos})::more,names,res) = 
               if Basic.isMemberEq(name,names,Symbol.symEq) then
                  raise SyntaxError("Duplicate entry found in identifier list: "^Symbol.name(name),SOME pos)
               else 
                  f(more,name::names,p::res)
     in
        f(plist,[],[])
     end                                                       

type absyn_structure_constructor = {name:symbol,pos:position,selectors:param option list,
			            argument_types:absyn_term list}

type absyn_structure_profile = {name:symbol,pos:position,obtype_params:param list}

type absyn_structure = {name:symbol,pos:position,obtype_params:param list,free:bool,
                        constructors:absyn_structure_constructor list}

fun makeFree(ab_struc:absyn_structure as {name,pos,obtype_params,constructors,...}) = 
      {name=name,pos=pos,obtype_params=obtype_params,constructors=constructors,free=true}

fun makeNonFree(ab_struc:absyn_structure as {name,pos,obtype_params,constructors,...}) = 
      {name=name,pos=pos,obtype_params=obtype_params,constructors=constructors,free=false}

type absyn_domain = {name:symbol,arity:int,sort_predicate: mod_symbol option, pos:position} 

datatype prop_con = notCon | andCon | orCon | ifCon | iffCon 
                  | forallCon | existsCon | existsUniqueCon

datatype quant_con = universal | existential | unique_existential

fun quantConToString(universal) = N.forall_name
  | quantConToString(existential) = N.exists_name
  | quantConToString(unique_existential) = N.exists_unique_name


val not_con_passoc = {prec=ref(50),assoc=ref (NONE:bool option)}
val and_con_passoc = {prec=ref(30),assoc=ref (SOME false)}
val or_con_passoc = {prec=ref(20),assoc= ref (SOME false)}
val if_con_passoc = {prec=ref(10),assoc= ref (SOME false)}
val iff_con_passoc = {prec=ref(10),assoc= ref (SOME false)}

fun getPropConArityAndPrec(pc) = 
     (case pc of
         notCon => (1,#prec(not_con_passoc))
       | andCon => (2,#prec(and_con_passoc))
       | orCon => (2,#prec(or_con_passoc))
       | ifCon => (2,#prec(if_con_passoc))
       | iffCon => (2,#prec(iff_con_passoc)))

fun set_PC_Assoc(notCon,b:bool) = #assoc(not_con_passoc) := SOME(b)
  | set_PC_Assoc(andCon,b) = #assoc(and_con_passoc) := SOME(b)
  | set_PC_Assoc(orCon,b) = #assoc(or_con_passoc) := SOME(b)
  | set_PC_Assoc(ifCon,b) = #assoc(if_con_passoc) := SOME(b)
  | set_PC_Assoc(iffCon,b) = #assoc(iff_con_passoc) := SOME(b)


fun isQuantPropCon(forallCon) = true 
  | isQuantPropCon(existsCon) = true 
  | isQuantPropCon(existsUniqueCon) = true 
  | isQuantPropCon(_) = false

fun propConToSymbol(notCon) = N.not_symbol
  | propConToSymbol(andCon) = N.and_symbol
  | propConToSymbol(orCon) = N.or_symbol
  | propConToSymbol(ifCon) = N.if_symbol
  | propConToSymbol(iffCon) = N.iff_symbol
  | propConToSymbol(forallCon) = N.forall_symbol
  | propConToSymbol(existsCon) = N.exists_symbol
  | propConToSymbol(existsUniqueCon) = N.exists_unique_symbol

fun propConToString(notCon) = N.not_name
  | propConToString(andCon) = N.and_name
  | propConToString(orCon) = N.or_name
  | propConToString(ifCon) = N.if_name
  | propConToString(iffCon) = N.iff_name
  | propConToString(forallCon) = N.forall_name
  | propConToString(existsCon) = N.exists_name
  | propConToString(existsUniqueCon) = N.exists_unique_name

fun hashPropCon(pc) = Basic.hashInt(S.code(propConToSymbol(pc)))

fun isPropCon(name) = 
      S.symEq(name,N.not_symbol) orelse
      S.symEq(name,N.and_symbol) orelse
      S.symEq(name,N.or_symbol) orelse
      S.symEq(name,N.if_symbol) orelse
      S.symEq(name,N.iff_symbol) orelse
      S.symEq(name,N.forall_symbol) orelse
      S.symEq(name,N.exists_symbol) orelse
      S.symEq(name,N.exists_unique_symbol)

(* version for module symbols: *)

fun isPropConMS(name) = 
      ModSymbol.modSymEq(name,N.mnot_symbol) orelse
      ModSymbol.modSymEq(name,N.mand_symbol) orelse
      ModSymbol.modSymEq(name,N.mor_symbol) orelse
      ModSymbol.modSymEq(name,N.mif_symbol) orelse
      ModSymbol.modSymEq(name,N.miff_symbol) orelse
      ModSymbol.modSymEq(name,N.mforall_symbol) orelse
      ModSymbol.modSymEq(name,N.mexists_symbol) orelse
      ModSymbol.modSymEq(name,N.mexists_unique_symbol)

fun isQuantName(name) =
             S.symEq(name,N.forall_symbol) orelse
             S.symEq(name,N.exists_symbol) orelse
             S.symEq(name,N.exists_unique_symbol)

fun isPropConOpt(id) = 
  if (S.symEq(id,N.not_symbol) orelse S.symEq(id,N.alternate_not_symbol)) then SOME(notCon)
  else 
     if (S.symEq(id,N.and_symbol) orelse S.symEq(id,N.alternate_and_symbol)) then SOME(andCon)
     else
         if (S.symEq(id,N.or_symbol) orelse S.symEq(id,N.alternate_or_symbol)) then SOME(orCon)
         else
            if (S.symEq(id,N.if_symbol) orelse S.symEq(id,N.alternate_if_symbol)) then SOME(ifCon)
            else
               if (S.symEq(id,N.iff_symbol) orelse S.symEq(id,N.alternate_iff_symbol)) then SOME(iffCon)
               else
                  if S.symEq(id,N.forall_symbol) then SOME(forallCon)
                  else
                     if S.symEq(id,N.exists_symbol) then SOME(existsCon)
                     else
                        if S.symEq(id,N.exists_unique_symbol) then SOME(existsUniqueCon)
                        else NONE

fun propConToString(con) = Symbol.name(propConToSymbol(con))

fun makeFreshIds(syms) = 
     let fun f([],_,res) = res
           | f(sym::more,i,res) = f(more,i+1,Symbol.symbol("!"^Int.toString(i))::res)
     in
        f(syms,1,[])
     end    

datatype ath_number = int_num of int * string ref | real_num of real * string  ref            

fun getRealMagnitude(int_num(i,_)) = Real.fromInt(i)
  | getRealMagnitude(real_num(r,_)) = r

fun compareNumbers(int_num(i,_),int_num(j,_)) = String.compare(Int.toString(i),Int.toString(j))
  | compareNumbers(real_num(i,_),real_num(j,_)) = String.compare(Real.toString(i),Real.toString(j))
  | compareNumbers(int_num(i,_),real_num(j,_)) = String.compare(Int.toString(i),Real.toString(j))
  | compareNumbers(real_num(i,_),int_num(j,_)) = String.compare(Real.toString(i),Int.toString(j))

fun hashANum(int_num(i,_)) = Basic.hashInt(i)
  | hashANum(real_num(r,_)) = Basic.hashString(Real.toString(r))

fun convertRealStr(str) = 
  let val tokens = String.tokens (fn c => c = #".") str
  in
    case tokens of
      [int,dec] =>
        let val dec_len = String.size dec
            val count = let fun f(i,count) = if i >= 0 andalso String.sub(dec,i) = #"0" then f(i-1,count+1) else count
                        in f(dec_len-1,0) end
            val dec' = if count >= dec_len then "" else String.substring(dec,0,dec_len - count)
            val new_dec = if dec' = "" then "0" else dec'
        in int^"."^new_dec end
    | _ => str
  end

fun athenaNumberToString(int_num(i,box),SML_negative_number_format) = 
     let val box_cont = !box
     in
      if box_cont = "" then
         let val res = if i < 0 then
                          (if SML_negative_number_format then "~"^(Int.toString (Int.abs i))
                           else  "("^Names.subtraction_name^" "^(Int.toString (Int.abs i))^")")
                       else Int.toString(i)
             val _ = box := res
         in res end
      else box_cont
     end
  | athenaNumberToString(real_num(r,box),SML_negative_number_format) = 
     let val box_cont = !box
     in
      if (box_cont = "" orelse SML_negative_number_format) then
         let val res = if r < 0.0 then
                          (if SML_negative_number_format then "~"^(convertRealStr (Real.fmt (StringCvt.FIX NONE) (Real.abs r)))
                           else "("^(Names.subtraction_name)^" "^(convertRealStr (Real.fmt (StringCvt.FIX NONE) (Real.abs r)))^")")
                       else convertRealStr (Real.fmt (StringCvt.FIX NONE) r)
             val _ = box := res
         in res end
      else let val _ = () 
           in
             box_cont 
           end
     end	 

fun athNumberToString(x) = athenaNumberToString(x,false)

fun athNumEquality(int_num(i,_),int_num(j,_)) = i = j
  | athNumEquality(real_num(r1,_),real_num(r2,_)) = Real.==(r1,r2)
  | athNumEquality(int_num(i,_),real_num(r,_)) = Real.==(Real.fromInt(i),r)
  | athNumEquality(real_num(r,_),int_num(i,_)) = Real.==(Real.fromInt(i),r)

fun literalAthNumEquality(a1,a2) = (athNumberToString(a1) = athNumberToString(a2))

val re_code_cell = ref(0)

fun getRECode() = Basic.returnAndInc(re_code_cell)

datatype expression = idExp of {msym:MS.mod_symbol, mods:S.symbol list,sym: S.symbol, no_mods:bool,pos:position}
		    | taggedConSym of {name:mod_symbol, sort_as_tagged_symterm: absyn_term, 
				       sort_as_fterm:FTerm.term option,pos:position}
                    | opExp of {op_exp: expression, pos: position}
                    | numExp of {number:ath_number,pos:position} 
                    | quotedIdeExp of {name:string,pos:position} 
                    | unitExp of {pos:position}
                    | charExp of {code:int,pos:position} 
                    | logicalAndExp of {args:phrase list,pos:position}
                    | logicalOrExp of {args:phrase list,pos:position}
                    | whileExp of {test:phrase,body:phrase,pos:position} 
                    | beginExp of {members:phrase list,pos:position} 
                    | stringExp of {str:int list,pos:position ,mem_index:int}
                    | termVarExp of {term_var:AthTermVar.ath_term_var,user_sort:absyn_term option,pos:position} 
                    | propConExp of {con:prop_con,pos:position}
                    | checkExp of {clauses:check_clause list,pos:position}
                    | functionExp of {params:possibly_wildcard_param list, body:expression, pos:position}                                     
                    | appExp of {proc:phrase, args: phrase list, pos:position,alt_exp: expression option ref}
                    | UAppExp of {proc:phrase, arg: phrase, pos:position}
                    | BAppExp of {proc:phrase, arg1: phrase, arg2:phrase, pos:position}
                    | listExp of {members:phrase list,pos:position}                     
                    | methodExp of {params:possibly_wildcard_param list, body:deduction, 
				    pos:position, name:string ref} 
                    | matchExp of {discriminant:phrase,clauses:match_clause list, pos:position} 
                    | tryExp of {choices:expression list,pos:position} 
                    | letExp of {bindings:binding list, body: expression, pos:position} 
                    | letRecExp of {bindings:binding list, body: expression, pos:position} 
                    | cellExp of {contents:phrase,pos:position}
                    | refExp of {cell_exp:expression,pos:position} 
                    | setCellExp of {cell_exp:expression,set_phrase:phrase,pos:position}
                    | vectorInitExp of {length_exp:expression,init_val:phrase,pos:position}
                    | vectorSetExp of {vector_exp:expression,index_exp:expression,new_val:phrase,pos:position}
                    | vectorSubExp of {vector_exp:expression,index_exp:expression,pos:position}
and  deduction =  
                  assumeDed of {assumption: phrase,body:deduction,pos:position} 
                | byCasesDed of {disj:phrase,from_exps:expression list option,
                                arms:case_clause list,pos:position}
                | infixAssumeDed of {bindings: binding list, body:deduction, pos:position}
                | assumeLetDed of {bindings: binding list, body:deduction, pos:position} 
                | absurdDed of {hyp:phrase,body:deduction,pos:position} 
                | absurdLetDed of {named_hyp:binding, body:deduction, pos:position} 
                | methodAppDed of {method:expression, args: phrase list, pos:position}
                | UMethAppDed of {method:expression, arg: phrase, pos:position}
                | BMethAppDed of {method:expression, arg1: phrase, arg2: phrase, pos:position}
                | matchDed of {discriminant:phrase,clauses:dmatch_clause list, pos:position}
                | inductionDed of {prop:phrase,clauses:dmatch_clause list, 
                                   pos:position}
                | structureCasesDed of {prop:phrase,term:expression option,clauses:dmatch_clause list, pos:position}
                | tryDed of {choices:deduction list,pos:position} 
                | letDed of {bindings:binding list, body: deduction, pos:position} 
                | letRecDed of {bindings:binding list, body: deduction, pos:position} 
                | beginDed of {members:deduction list,pos:position} 
                | checkDed of {clauses:dcheck_clause list,pos:position}
                | byDed of {wanted_res:expression,conc_name:param option,body:deduction,pos:position}
                | fromDed of {conclusion:expression,premises:expression,pos:position}
                | genOverDed of {eigenvar_exp:expression,body:deduction,pos:position}
                | pickAnyDed of {eigenvars: possibly_typed_param list,body:deduction,pos:position}
                | withWitnessDed of {eigenvar_exp:expression,ex_gen:phrase,body:deduction,pos:position} 
                | pickWitnessDed of {ex_gen:phrase,var_id:symbol,inst_id:symbol option,body:deduction,pos:position}
                | pickWitnessesDed of {ex_gen:phrase,var_ids:symbol list,
		  		       inst_id:symbol option,body:deduction,pos:position}

and phrase = exp of expression | ded of deduction

and condition = boolCond of phrase  | elseCond

and pattern =  idPat of possibly_typed_param
             | anyPat of {pos:position}
             | funSymPat of {name:mod_symbol,sort_opt: FTerm.term option, sort_as_exp: expression option, arity:int,pos:position}
             | propConPat of {pcon:prop_con,pos:position}
             | numPat of {ath_num:ath_number,pos:position}
             | constantTermVarPat of {term_var:AthTermVar.ath_term_var,pos:position}
             | constantMetaIdPat of {name:symbol,pos:position}
             | constantStringPat of {str:int list,pos:position} 
             | constantCharPat of {ch:int,pos:position}
             | listPats of {member_pats:pattern list,pos:position}  (* These are [pi_1 ... pi_n] *)
             | listPat of {head_pat:pattern,tail_pat:pattern,pos:position}
             | cellPat of {pat:pattern,pos:position}
             | splitPat of {pats:pattern list,pos:position, re_form: (pattern,expression) GeneralRE.RE0,code:int}
             | reStarPat of {pat:pattern,pos:position,re_form: (pattern,expression) GeneralRE.RE0,code:int}
             | rePlusPat of {pat:pattern,pos:position,re_form: (pattern,expression) GeneralRE.RE0,code:int}
             | reRepPat of {pat:pattern,times:int,pos:position,re_form: (pattern,expression) GeneralRE.RE0,code:int}
             | reLitPat of {pat:pattern,pos:position}
             | reRangePat of {from_pat:pattern,to_pat:pattern,lo:real,hi:real,pos:position}
             | reOptPat of {pat:pattern,pos:position,re_form: (pattern,expression) GeneralRE.RE0,code:int}
             | valOfPat of {id:param,lex_ad: (int * int) option, pos:position}
             | valOfPat1 of {id:param,num:ath_number,pos:position}
             | unitValPat of {pos:position}
             | namedPat of {name:symbol,pat:pattern,pos:position}
             | someCharPat of {id:possibly_wildcard_param,pos:position}
             | someVarPat of {id:possibly_wildcard_param,pos:position}
             | someQuantPat of {id:possibly_wildcard_param,pos:position}
             | somePropConPat of {id:possibly_wildcard_param,pos:position}
             | someTermPat of {id:possibly_wildcard_param,pos:position}
             | someAtomPat of {id:possibly_wildcard_param,pos:position}
	     | somePropPat of {id:possibly_wildcard_param,pos:position}
             | someFunctionPat of {id:possibly_wildcard_param,pos:position}
             | someMethodPat of {id:possibly_wildcard_param,pos:position}
             | someSymbolPat of {id:possibly_wildcard_param,pos:position}
             | someSubPat of {id:possibly_wildcard_param,pos:position}
             | someTablePat of {id:possibly_wildcard_param,pos:position}
             | someMapPat of {id:possibly_wildcard_param,pos:position}
             | someListPat of {id:possibly_wildcard_param,pos:position}
             | someVectorPat of {id:possibly_wildcard_param,pos:position}
             | someCellPat of {id:possibly_wildcard_param,pos:position}
             | compoundPat of {head_pat:pattern,rest_pats:pattern list,pos:position}
             | wherePat of {pat:pattern,guard:expression,pos:position}
             | disjPat of {pats:pattern list,pos:position}

and possibly_wildcard_param = someParam of possibly_typed_param | wildCard of position 

withtype binding = {bpat:pattern,def:phrase,pos:position}

     and optBinding = {param:possibly_wildcard_param option,def:phrase,pos:position}

     and match_clause = {pat:pattern,exp:expression} 
         
     and dmatch_clause = {pat:pattern,ded:deduction}

     and case_clause = {case_name:param option,alt:expression,proof:deduction}

     and check_clause = {test:condition,result:expression}

     and dcheck_clause = {test:condition,result:deduction}

     and possibly_typed_param = {name:symbol,pos:position,sort_as_sym_term:absyn_term option,op_tag: (int * int) option,
	     		         sort_as_fterm:FTerm.term option,sort_as_exp: expression option}

type absyn_fsym = {name:symbol,pos:position,obtype_params:param list,input_transformer: expression list option,
                   argument_types:absyn_term list,range_type:absyn_term,
                   prec: int option,assoc: bool option,overload_sym: param option}


fun isValOfPat(valOfPat({id={name,...},...})) = SOME(name)
  | isValOfPat(_) = NONE

fun makeBinarySplitPats(pats as p1::p2::rest,pos,code_value) = 
     let fun f(pats as p1::p2::rest) = splitPat({pats=[p1,f(p2::rest)],pos=pos,re_form=GeneralRE.any0(GeneralRE.trivial_tag),code=(~1)})
           | f([p]) = p 
      in
         (case (f pats) of
              splitPat({pats,pos,re_form,...}) => splitPat({pats=pats,pos=pos,re_form=re_form,code=code_value})
            | p => p)
      end       

fun makePTP(sym) = let val res:possibly_typed_param = {name=sym,pos=dum_pos,sort_as_sym_term=NONE,
                                                       sort_as_fterm=NONE,sort_as_exp=NONE,op_tag=NONE}
                   in
                      res
                   end

fun makePTPWithPos(sym,p) = 
   let val res:possibly_typed_param = {name=sym,pos=p,sort_as_sym_term=NONE,sort_as_fterm=NONE,sort_as_exp=NONE,op_tag=NONE}
   in res end

fun inapplicable(phrase) = 
  (case phrase of
      exp(taggedConSym(_)) => true
    | exp(numExp(_)) => true
    | exp(termVarExp({user_sort,...})) =>
           (case user_sort of 
               NONE => true
             | SOME(sort) => (case SymTerm.isTaggedApp(sort) of
                                 SOME(f,_,args) => not(MS.modSymEq(f,Names.fun_name_msym))
				| _ => true))
    | exp(quotedIdeExp(_)) => true
    | exp(unitExp(_)) => true
    | exp(charExp(_)) => true
    | exp(stringExp(_)) => true
    | exp(listExp(_)) => true
    | exp(cellExp(_)) => true
    | _ => false)

fun makePosLessIdPat(sym) = idPat({name=sym,pos=dum_pos,op_tag=NONE,sort_as_sym_term=NONE,sort_as_fterm=NONE,sort_as_exp=NONE})

fun posOfPWP(someParam({pos,...})) = pos
  | posOfPWP(wildCard(pos)) = pos

fun pwpToString(someParam({name,...})) = Symbol.name(name)
  | pwpToString(wildCard(_)) = Names.wild_card

fun pwpToSym(someParam({name,sort_as_fterm,...})) = name
  | pwpToSym(wildCard(_)) = Names.wild_card_symbol

fun pwpToSymAndSortOpt(someParam({name,sort_as_fterm,...})) = (name,sort_as_fterm)
  | pwpToSymAndSortOpt(wildCard(_)) = (Names.wild_card_symbol,NONE)


fun getPWParamNames(pwp_list) = 
 let fun f([]:possibly_wildcard_param list,res) = rev res
      | f((wildCard(_))::more,res) = f(more,res)
      | f(someParam({name,pos,...})::more,res) = 
		if Basic.isMemberEq(name,res,Symbol.symEq) then
		raise SyntaxError("Duplicate entry found in identifier list: "^Symbol.name(name),SOME pos)
		else f(more,name::res)
 in
   f(pwp_list,[])
 end

fun getParamNames(plist) = 
     let fun f([]:param list,res) = rev(res)
           | f({name,pos}::more,res) = if Basic.isMemberEq(name,res,Symbol.symEq) then
                                          raise SyntaxError("Duplicate entry found in identifier list: "^
                                                            Symbol.name(name),SOME pos)
                                       else 
                                          f(more,name::res)
     in
        f(plist,[])
     end
     
fun getParams(plist) = 
     let fun f([]:param list,names,res) = rev(res)
           | f((p as {name,pos})::more,names,res) = 
               if Basic.isMemberEq(name,names,Symbol.symEq) then
                  raise SyntaxError("Duplicate entry found in identifier list: "^Symbol.name(name),SOME pos)
               else 
                  f(more,name::names,p::res)
     in
        f(plist,[],[])
     end                                                       

fun checkForDuplicateParams(possibly_typed_params) = 
  let fun f([]:possibly_typed_param list, res) = rev res
        | f((p as {name,pos,...})::more,res) = 
			if Basic.isMemberEq(name,res,Symbol.symEq) then
                           raise SyntaxError("Duplicate entry found in identifier list: "^
                                              Symbol.name(name),SOME pos)
                        else f(more,name::res)
  in
    (f(possibly_typed_params,[]);possibly_typed_params)
  end

fun getBindings(obl) = 
  let fun f([],res) = rev res
       | f(({param=popt,def,pos}::rest):optBinding list,res) = 
		(case popt of
		   SOME(pwp) => let val pat = (case pwp of 
                                                 someParam(ptp) => idPat(ptp)
                                               | wildCard(pos) => anyPat({pos=pos}))
                                    val b:binding = {bpat=pat,def=def,pos=pos}
				in f(rest,b::res) end
		 | _ => let val b = {bpat=anyPat({pos=pos}),def=def,pos=pos} in f(rest,b::res) end)
  in
     f(obl,[])
  end
     
fun msym(s) = ModSymbol.makeModSymbol([],s,s)

val mSym = msym

fun msyms(sym_set) = let val syms = Symbol.listSymbols(sym_set)
                         val msyms = map msym syms
                     in
                        ModSymbol.symListToSet(msyms)
                     end



fun makeIdExp(str,pos) = 
    let val s = Symbol.makePrivateSymbol(str)
    in
        idExp({msym=msym(s),mods=[],sym=s,no_mods=true,pos=pos})
    end

fun makeIdExpSimple(str,pos) = 
    let val s = Symbol.symbol(str)
    in
        idExp({msym=msym(s),mods=[],sym=s,no_mods=true,pos=pos})
    end


fun makeIdExpSimple'(sym,pos) = 
    let val s = sym
    in
        idExp({msym=msym(s),mods=[],sym=s,no_mods=true,pos=pos})
    end

fun makeMapExp(bindings,map_pos) = 
    let val proc = makeIdExp(N.addMapFun_name,map_pos)
        val empty_mapping = makeIdExp(N.empty_mapping_name,map_pos)
    in
        appExp({proc=exp(proc),args=[exp(empty_mapping),exp(listExp({members=bindings,pos=map_pos}))],pos=map_pos,alt_exp=ref(NONE)})
    end

fun makeAbSynConjunction(exps) = 
      appExp({proc=exp(idExp({msym=N.mand_symbol,mods=[],sym=N.and_symbol,no_mods=true,pos=dum_pos})),args=(map exp exps),alt_exp=ref(NONE),pos=dum_pos})

type absyn_symbol_definition = {name:symbol,pos:position,condition:expression,abbreviated:bool}

fun isDeduction(ded(_)) = true
  | isDeduction(_) = false

fun isNamedDeduction(ded(byDed({conc_name=SOME({name,...}),...}))) = (true,SOME name)
  | isNamedDeduction(ded(byDed({wanted_res=idExp({msym,...}),...}))) = (true,SOME(MS.nameAsSymbol(msym)))
  | isNamedDeduction(ded(inductionDed({prop=exp(idExp({msym,...})),...}))) = (true,SOME(MS.nameAsSymbol(msym)))
  | isNamedDeduction(ded(structureCasesDed({prop=exp(idExp({msym,...})),...}))) = (true,SOME(MS.nameAsSymbol(msym)))

  | isNamedDeduction(ded(_)) = (true,NONE)
  | isNamedDeduction(_) = (false,NONE)

fun isExpression(exp(_)) = true
  | isExpression(_) = false 

val isTermApp = 
  let fun f([],arg_terms) = SOME(rev(arg_terms))
        | f(exp(e)::more,arg_terms) = (case isTermApp(e) of
                                          SOME(t) => f(more,t::arg_terms)
                                        | _ => NONE)
        | f(_,_) = NONE  
      and isTermApp(idExp({msym,...})) = SOME(SymTerm.makeConstant(msym))
        | isTermApp(numExp({number,pos,...})) = SOME(SymTerm.makeConstant(msym(S.symbol(athNumberToString(number)))))       
        | isTermApp(appExp({proc=exp(idExp({msym,...})),args as _::_,pos,...})) = 
               (case f(args,[]) of
                   SOME(terms) => SOME(SymTerm.makeApp(msym,terms))
                 | _ => NONE)
        | isTermApp(appExp({proc=exp(opExp({op_exp=idExp({msym,...}),...})),args as _::_,pos,...})) = 
             (case f(args,[]) of
                  SOME(terms) => SOME(SymTerm.makeApp(msym,terms))
                | _ => NONE)
        | isTermApp(_) = NONE
  in 
     isTermApp
  end

val isSExpApp = 
  let fun f([]) = true 
        | f(exp(e)::more) = isTermApp(e) andalso f(more)
        | f(_) = false
      and isTermApp(idExp(_)) = true
        | isTermApp(taggedConSym(_)) = true 
        | isTermApp(unitExp(_)) = true
        | isTermApp(charExp(_)) = true
        | isTermApp(logicalAndExp(_)) = true
        | isTermApp(logicalOrExp(_)) = true
        | isTermApp(numExp({number,pos,...})) = true
        | isTermApp(stringExp(_)) = true
        | isTermApp(termVarExp(_)) = true
        | isTermApp(propConExp(_)) = true
        | isTermApp(quotedIdeExp({name,pos,...})) = true
        | isTermApp(appExp({proc,args as _::_,pos,...})) = f(proc::args)
        | isTermApp(_) = false 
  in 
     isTermApp
  end

val isTermAppWithQuotedSymbolsAsVars = 
  let fun f([],arg_terms) = SOME(rev(arg_terms))
        | f(exp(e)::more,arg_terms) = (case isTermApp(e) of
                                          SOME(t) => f(more,t::arg_terms)
                                        | _ => NONE)
        | f(_,_) = NONE  
      and isTermApp(idExp({msym,...})) = SOME(SymTerm.makeConstant(msym))
        | isTermApp(numExp({number,pos,...})) = SOME(SymTerm.makeConstant(msym(S.symbol(athNumberToString(number)))))
        | isTermApp(quotedIdeExp({name,pos,...})) = SOME(SymTerm.makeVar(Symbol.symbol(name)))
        | isTermApp(appExp({proc=exp(idExp({msym,...})),args as _::_,pos,...})) = 
               (case f(args,[]) of
                   SOME(terms) => SOME(SymTerm.makeApp(msym,terms))
                 | _ => NONE)
        | isTermApp(appExp({proc=exp(opExp({op_exp=idExp({msym,...}),...})),args as _::_,pos,...})) = 
             (case f(args,[]) of
                  SOME(terms) => SOME(SymTerm.makeApp(msym,terms))
                | _ => NONE)
        | isTermApp(_) = NONE
  in 
     isTermApp
  end

fun posOfPat(idPat({pos,...})) = pos 
  | posOfPat(anyPat({pos})) = pos 
  | posOfPat(funSymPat({pos,...})) = pos
  | posOfPat(propConPat({pos,...})) = pos
  | posOfPat(numPat({pos,...})) = pos
  | posOfPat(constantTermVarPat({pos,...})) = pos
  | posOfPat(constantMetaIdPat({pos,...})) = pos
  | posOfPat(constantStringPat({pos,...})) = pos
  | posOfPat(constantCharPat({pos,...})) = pos
  | posOfPat(listPat({pos,...})) = pos
  | posOfPat(cellPat({pos,...})) = pos
  | posOfPat(listPats({pos,...})) = pos
  | posOfPat(splitPat({pos,...})) = pos
  | posOfPat(reStarPat({pos,...})) = pos
  | posOfPat(rePlusPat({pos,...})) = pos
  | posOfPat(reRangePat({pos,...})) = pos
  | posOfPat(reRepPat({pos,...})) = pos
  | posOfPat(reLitPat({pos,...})) = pos
  | posOfPat(reOptPat({pos,...})) = pos
  | posOfPat(valOfPat({pos,...})) = pos  
  | posOfPat(valOfPat1({pos,...})) = pos  
  | posOfPat(someVarPat({pos,...})) = pos
  | posOfPat(unitValPat({pos,...})) = pos 
  | posOfPat(namedPat({pos,...})) = pos
  | posOfPat(someQuantPat({pos,...})) = pos
  | posOfPat(somePropConPat({pos,...})) = pos
  | posOfPat(someTermPat({pos,...})) = pos
  | posOfPat(someAtomPat({pos,...})) = pos
  | posOfPat(somePropPat({pos,...})) = pos
  | posOfPat(someFunctionPat({pos,...})) = pos
  | posOfPat(someMethodPat({pos,...})) = pos
  | posOfPat(someSymbolPat({pos,...})) = pos
  | posOfPat(someSubPat({pos,...})) = pos
  | posOfPat(someListPat({pos,...})) = pos
  | posOfPat(someTablePat({pos,...})) = pos
  | posOfPat(someMapPat({pos,...})) = pos
  | posOfPat(someVectorPat({pos,...})) = pos
  | posOfPat(someCharPat({pos,...})) = pos
  | posOfPat(someCellPat({pos,...})) = pos
  | posOfPat(compoundPat({pos,...})) = pos 
  | posOfPat(disjPat({pos,...})) = pos 
  | posOfPat(wherePat({pos,...})) = pos

fun possiblyTypedParamToString(ptp:possibly_typed_param as {name,pos,sort_as_sym_term=SOME(t),...}) = 
      (Symbol.name(name))^":"^(SymTerm.taggedTermToString(t))
  | possiblyTypedParamToString(ptp:possibly_typed_param as {name,pos,sort_as_fterm=SOME(sort),...}) = 
      (Symbol.name(name))^":"^(FTerm.toStringDefault(sort))
  | possiblyTypedParamToString(ptp:possibly_typed_param as {name,pos,op_tag=SOME(i,j),...}) = 
      (Symbol.name(name))^(if j < 0 then (if i < 0 then "" else ":(OP "^(Int.toString(i))^")")
                           else ":(OP "^(Int.toString(i))^" "^(Int.toString(j))^")")
  | possiblyTypedParamToString(ptp:possibly_typed_param as {name,...}) = (Symbol.name(name))
      

fun printInductivePattern(idPat(ptp)) = possiblyTypedParamToString(ptp)
  | printInductivePattern(anyPat(_)) = Names.wild_card
  | printInductivePattern(funSymPat({name,...})) = MS.name(name)
  | printInductivePattern(numPat({ath_num,...})) = athNumberToString(ath_num)
  | printInductivePattern(compoundPat({head_pat=funSymPat({name,...}),rest_pats,...})) = 
           "("^MS.name(name)^" "^printLst(rest_pats)^")"
  | printInductivePattern(_) = ""
and
    printLst([]) = ""
  | printLst([pat]) = printInductivePattern(pat)
  | printLst(pat1::pat2::more) = printInductivePattern(pat1)^" "^printLst(pat2::more)


(* This will return false (i.e., clauses will NOT be ok) iff an else condition   *)
(* appears in a non-trailing position.   *)

fun okClauses([]) = true
  | okClauses({test=elseCond,result}::more) = if not(null(more)) then false else okClauses(more)
  | okClauses(_::more) = okClauses(more)

fun checkClauses(clauses,pos) =  if not(okClauses(clauses)) then 
                                    raise SyntaxError("Ill-formed check expression---else clause "^
                                                       "in non-trailing position",SOME(pos))
                                 else ()

datatype directive = loadFile of expression * pos
                   | addPath of expression * pos
                   | loadOnly of phrase list * pos 
                   | openModule of (mod_symbol * pos) list 
                   | overload of (phrase * phrase * pos * pos * pos) list * pos * {inverted:bool}
                   | expandInput of phrase list * phrase * pos 
                   | transformOutput of (phrase * phrase * {first_arg_pos:pos,second_arg_pos:pos,overall_pos:pos})
                   | setPrecedence of (mod_symbol * pos) list * expression 
                   | setAssoc of (mod_symbol * pos) list * bool (* true: left-associative, false: right-associative *)
                   | useTermParser of {tp_name:param,file:string}
                   | usePropParser of {pp_name:param,file:string}
                   | expandNextProof of pos 
                   | exitAthena of pos 
                   | printStackTrace of pos 
                   | clear_assum_base 
                   | sortDefinition of symbol * phrase * bool 
                   | definition of symbol * phrase * bool 
                   | definitionLst of (pattern list) * (symbol option) * phrase * pos * bool 
                   | definitions of (possibly_typed_param * expression) list * bool 
                   | funSymDefinition of symbol * param list * expression
                   | assert of expression list 
                   | assertClose of expression list 
                   | assertCloseAsgn of (param * expression) list 
                   | assertAsgn of param * expression 
                   | retract of expression list 
                   | ruleDefinition of  symbol * expression
                   | findModel of expression * pos
                   | addDemon of expression * pos
                   | addDemons of expression list * pos
                   | setFlag of param * (string * pos)

fun makeFunDefinition({fun_name as {name,sort_as_sym_term,sort_as_fterm,sort_as_exp,op_tag,...}:possibly_typed_param,
                       fun_params,fun_body,pos,file}) = 
     let val arity = List.length(fun_params)
         val fun_body_exp = functionExp({params=fun_params,body=fun_body,pos=pos})
     in
      (case op_tag of
          NONE => ({name=name,
	           pos=(#pos(fun_name)),
		   sort_as_sym_term=sort_as_sym_term,
		   sort_as_fterm=sort_as_fterm,               
                   sort_as_exp=sort_as_exp,
		   op_tag=SOME(arity,~1)},
		   fun_body_exp)
       | _ => ({name=name,pos=(#pos(fun_name)),sort_as_sym_term=sort_as_sym_term,sort_as_fterm=sort_as_fterm,               
                   sort_as_exp=sort_as_exp,op_tag=op_tag},fun_body_exp))
     end

fun ptpToExp({name,pos,...}:possibly_typed_param) = makeIdExpSimple'(name,pos)

fun wildParamToExp(someParam(ptp)) = ptpToExp(ptp)

fun makeMemoizedFunDefinition({fun_name as {name,sort_as_sym_term,sort_as_fterm,sort_as_exp,op_tag,...}:possibly_typed_param,
                               fun_params,fun_body,pos,file}) = 
     let val arity = List.length(fun_params)
         val fun_name_sym = name
	 val fun_params = map (fn wildCard(_) => someParam(makePTP(Symbol.freshSymbol(NONE)))
                                | p => p)
                              fun_params 
         fun makeList(params) = if arity < 2 then wildParamToExp(hd(fun_params)) else listExp({members=(map (fn p => exp(wildParamToExp(p)))  fun_params),pos=dum_pos})
	 val param_list = makeList(fun_params)
         val fun_body_exp = 
              let val ht = Symbol.symbol("H")  
	          val make_table_call = appExp({proc=exp(makeIdExpSimple'(Symbol.makePrivateSymbol(Names.makeTableFun_name),dum_pos)),
		      		      	        alt_exp=ref(NONE),
                                                args=[exp(numExp({number=int_num(50,ref("")),pos=dum_pos}))],pos=dum_pos})
                  val b:binding = {bpat=idPat(makePTP(ht)),def=exp(make_table_call),pos=dum_pos}
		  val try_1 = appExp({proc=exp(makeIdExpSimple'(Symbol.makePrivateSymbol(Names.findTableFun_name),dum_pos)),
		      	              alt_exp=ref(NONE),
                                      args=[exp(makeIdExpSimple'(ht,dum_pos)),exp(param_list)],pos=dum_pos})
                  val res_sym = Symbol.symbol("res")				       
                  val res_binding:binding = {bpat=idPat(makePTP(res_sym)),pos=dum_pos,
                                             def=exp(fun_body)}
                  val add_binding:binding = {bpat=anyPat({pos=dum_pos}),
                                             def=exp(appExp({proc=exp(makeIdExpSimple'
							     (Symbol.makePrivateSymbol(Names.addTableFun_name),dum_pos)),
					                     alt_exp=ref(NONE),
                                                              args=[exp(makeIdExpSimple'(ht,dum_pos)),
                                                                    exp(listExp({members=[exp(param_list),
	    	   	 	 			                                 exp(makeIdExpSimple'(Symbol.makePrivateSymbol("-->"),dum_pos)),
                                                                                         exp(makeIdExpSimple'(res_sym,dum_pos))],
								                pos=dum_pos}))],
                                                          pos=dum_pos})),
                                             pos=dum_pos}					
                  val try_2 = letExp({bindings=[res_binding,add_binding],pos=dum_pos,
                                      body=makeIdExpSimple'(res_sym,dum_pos)})
	          val big_lambda = functionExp({params=fun_params,body=tryExp({choices=[try_1,try_2],pos=dum_pos}),pos=dum_pos})
		  val big_letrec_binding:binding = {bpat=idPat(makePTP(fun_name_sym)),def=exp(big_lambda),pos=dum_pos}
		  val big_letrec = letRecExp({bindings=[big_letrec_binding],body=makeIdExpSimple'(fun_name_sym,dum_pos),pos=dum_pos})
		  val big_let = letExp({bindings=[b],body=big_letrec,pos=dum_pos})
              in
                 exp(big_let)
              end
    in 
      fun_body_exp
    end

fun desugarWithKeys(params,dict_exp,body,with_pos) = 
    let fun makeAppExp(rec_exp,field_name,pos) = 
                  appExp({proc=exp(makeIdExp(N.mapApplyFun_name,pos)),
                          args=[exp(rec_exp),exp(quotedIdeExp({name=(S.name(field_name)),pos=pos}))],
			  pos=with_pos,alt_exp=ref(NONE)})
        val rec_sym = Symbol.freshSymbol(NONE)
	val rec_exp = makeIdExpSimple'(rec_sym,with_pos)
        val binding1:binding = {bpat=idPat(makePTPWithPos(rec_sym,with_pos)),def=exp(dict_exp),pos=with_pos}
        val bindings = map (fn p:param as {name,pos=id_pos} => let val b:binding = {bpat=idPat(makePTPWithPos(name,id_pos)),def=exp(makeAppExp(rec_exp,name,id_pos)),pos=id_pos}
                                                               in b end)
                           params
    in
      letExp({bindings=(binding1::bindings),body=body,pos=with_pos})
    end

fun makeMethodDefinition({meth_name:possibly_typed_param,meth_params,meth_body,pos,file}) = 
     let val meth_body_exp = methodExp({params=meth_params,body=meth_body,pos=pos,
                                        name=ref(S.name(#name(meth_name)))})
         in
           (meth_name,meth_body_exp)
     end
    
datatype user_input = structureInput of absyn_structure
                    | structuresInput of absyn_structure list
                    | domainInput of absyn_domain
                    | domainsInput of absyn_domain list 
                    | moduleInput of module_entry
                    | moduleExtension of module_entry 
                    | subSortDeclaration of mod_symbol * pos * mod_symbol * pos 
                    | subSortsDeclaration of ((mod_symbol * pos) list) * (mod_symbol * pos)
                    | functionSymbolInput of absyn_fsym  list 
                    | constantSymbolInput of absyn_fsym list 
                    | phraseInput of phrase 
                    | symbolDefinitionInput of absyn_symbol_definition
                    | direcInput of directive 

withtype module_entry = {module_name: param, module_contents: user_input list, module_file: string ref}

fun printMetaId(str) = N.metaIdPrefix^str
         
fun makeUnProp([],p) = p
  | makeUnProp(v::more,p) = 
       makeUnProp(more,appExp({proc=exp(idExp({msym=N.mforall_symbol,mods=[],no_mods=true,sym=N.forall_symbol,pos=dum_pos})),
                               args=[exp(termVarExp({term_var=v,user_sort=NONE,pos=dum_pos})),exp(p)],
                               alt_exp=ref(NONE),pos=dum_pos}))

fun makeRelSymCondition({rel_name,arg_vars,condition}) = 
   let val new_sym_prop = appExp({proc=exp(idExp({msym=mSym rel_name,mods=[],no_mods=true,sym=rel_name,pos=dum_pos})),alt_exp=ref(NONE),
                                  args=(List.map (fn v => exp(termVarExp({term_var=v,user_sort=NONE,pos=dum_pos})))
                                                  arg_vars),
                                  pos=dum_pos})
       val cond_prop = appExp({proc=exp(idExp({msym=N.miff_symbol,mods=[],no_mods=true,sym=N.iff_symbol,pos=dum_pos})),alt_exp=ref(NONE),
                               args=[exp(new_sym_prop),exp(condition)],pos=dum_pos})
       in
          makeUnProp(rev(arg_vars),cond_prop)
   end

fun makeFunSymCondition({fun_name,arg_vars,the_var,def_description}) = 
     let val fmods = []
         val equality_prop = appExp({proc=exp(idExp({msym=N.mequal_logical_symbol,no_mods=true,mods=[],sym=N.equal_logical_symbol,pos=dum_pos})),
                                    alt_exp=ref(NONE),
                                     args=[exp(appExp({proc=exp(idExp({msym=mSym fun_name,mods=fmods,no_mods=true,sym=fun_name,pos=dum_pos})),
                                                       args=(List.map (fn v => 
                                                                       exp(termVarExp({term_var=v,
								       user_sort=NONE,pos=dum_pos})))
                                                             arg_vars),alt_exp=ref(NONE),pos=dum_pos})),
                                           exp(termVarExp({term_var=the_var,user_sort=NONE,pos=dum_pos}))],
                                     pos=dum_pos})
         val cond_prop = appExp({proc=exp(idExp({msym=N.miff_symbol,mods=[],no_mods=true,sym=N.iff_symbol,pos=dum_pos})),
                                 alt_exp=ref(NONE),
                                 args=[exp(equality_prop),exp(def_description)],
                                 pos=dum_pos})
         in
           makeUnProp(the_var::rev(arg_vars),cond_prop)
     end

fun makeFunOrRelSymCondition({fun_or_rel_name,arg_vars,term_or_condition}) = 
let fun isPropExp(appExp({proc=exp(idExp({msym,...})),args,...})) = isPropConMS(msym)
      | isPropExp(_) = false
    in
      if isPropExp(term_or_condition) then
         makeRelSymCondition({rel_name=fun_or_rel_name,arg_vars=arg_vars,condition=term_or_condition})
      else
         let val fresh_the_var = AthTermVar.fresh() 
             val new_def_description = appExp({proc=exp(idExp({msym=N.mequal_logical_symbol,mods=[],no_mods=true,sym=N.equal_logical_symbol,
                                               pos=dum_pos})),alt_exp=ref(NONE),
                                               args=[exp(termVarExp({term_var=fresh_the_var,user_sort=NONE,
							pos=dum_pos})),
                                                     exp(term_or_condition)],pos=dum_pos})
             in
               makeFunSymCondition({fun_name=fun_or_rel_name,arg_vars=arg_vars,the_var=fresh_the_var,
                                    def_description=new_def_description})
         end
end
        
fun makeConstantSymCondition({constant_name,the_var,def_description}) = 
     let val (mods,sym) = MS.split(constant_name)
         val equality_prop = appExp({proc=exp(idExp({msym=N.mequal_logical_symbol,mods=[],no_mods=true,sym=N.equal_logical_symbol,pos=dum_pos})),
                                     args=[exp(idExp({msym=constant_name,mods=mods,no_mods=null(mods),sym=sym,pos=dum_pos})),
                                           exp(termVarExp({term_var=the_var,user_sort=NONE,pos=dum_pos}))],
                                     alt_exp=ref(NONE),pos=dum_pos})
         val cond_prop = appExp({proc=exp(idExp({msym=N.miff_symbol,mods=[],no_mods=true,sym=N.iff_symbol,pos=dum_pos})),
                                 args=[exp(equality_prop),exp(def_description)],
                                 alt_exp=ref(NONE),pos=dum_pos})
         in
           appExp({proc=exp(idExp({msym=N.mforall_symbol,mods=[],no_mods=true,sym=N.forall_symbol,pos=dum_pos})),
                   args=[exp(termVarExp({term_var=the_var,user_sort=NONE,pos=dum_pos})),exp(cond_prop)],
                   alt_exp=ref(NONE),pos=dum_pos})
     end

fun isSomeQuantPat(someQuantPat(_)) = true
  | isSomeQuantPat(_) = false

fun isSomeNamedQuantPat(someQuantPat({id=someParam(_),...})) = true 
  | isSomeNamedQuantPat(someQuantPat({id=wildCard(_),...})) = false
  | isSomeNamedQuantPat(namedPat(_)) = true 
  | isSomeNamedQuantPat(_) = false

fun isListPat(someListPat(_)) = true
  | isListPat(listPat(_)) = true
  | isListPat(listPats(_)) = true
  | isListPat(splitPat(_)) = true
  | isListPat(reStarPat(_)) = true
  | isListPat(rePlusPat(_)) = true
  | isListPat(reRepPat(_)) = true
  | isListPat(constantStringPat(_)) = true 
  | isListPat(wherePat({pat,...})) = isListPat(pat)
  | isListPat(namedPat({pat,...})) = isListPat(pat)
  | isListPat(_) = false


fun isListPatRelaxed(someListPat(_)) = true
  | isListPatRelaxed(listPat(_)) = true
  | isListPatRelaxed(listPats(_)) = true
  | isListPatRelaxed(splitPat(_)) = true
  | isListPatRelaxed(reStarPat(_)) = true
  | isListPatRelaxed(rePlusPat(_)) = true
  | isListPatRelaxed(reRepPat(_)) = true
  | isListPatRelaxed(constantStringPat(_)) = true 
  | isListPatRelaxed(wherePat({pat,...})) = isListPatRelaxed(pat)
  | isListPatRelaxed(namedPat({pat,...})) = isListPatRelaxed(pat)
  | isListPatRelaxed(disjPat({pats,...})) = Basic.exists(pats,isListPatRelaxed)
  | isListPatRelaxed(_) = false

val tt0 = GeneralRE.trivial_tag

fun concatLst([e]) = e
  | concatLst(e1::rest) = GeneralRE.concat0(e1,concatLst(rest),tt0)
  | concatLst([]) = GeneralRE.null0(tt0)

fun concatLst'([]) = GeneralRE.null0(tt0)
  | concatLst'(e1::rest) = GeneralRE.concat0(e1,concatLst'(rest),tt0)

fun unionLst([e]) = e
  | unionLst(e1::rest) = GeneralRE.union0(e1,unionLst(rest),tt0)

val (lparen,rparen,lbrack,rbrack,space) = (Basic.lparen,Basic.rparen,Basic.lbrack,Basic.rbrack,Basic.blank)

fun unparseExp(idExp({msym,...})) = MS.name(msym)
  | unparseExp(taggedConSym({name,sort_as_tagged_symterm,sort_as_fterm,...})) = 
       (case sort_as_fterm of
           NONE => MS.name(name) ^ ":" ^ (SymTerm.toString(SymTerm.stripTags(sort_as_tagged_symterm),printSymTermVar)) ^ " [NO FSORT]"
         | SOME(sort) => "[FSORT: " ^ (FTerm.toStringDefault(sort)) ^ "]")
  | unparseExp(opExp({op_exp,...})) = lparen^Names.infix_op_name^space^(unparseExp op_exp)^rparen
  | unparseExp(numExp({number,...})) = athNumberToString(number)
  | unparseExp(letExp({bindings,body,pos,...})) = lparen^"let "^lparen^(unparseBindings bindings)^rparen^space^(unparseExp body)^rparen
  | unparseExp(letRecExp({bindings,body,pos,...})) = lparen^"letrec "^lparen^(unparseBindings bindings)^rparen^space^(unparseExp body)^rparen
  | unparseExp(quotedIdeExp({name,...})) = (Names.metaIdPrefix)^name
  | unparseExp(unitExp(_)) = "()"
  | unparseExp(charExp({code,...})) = Char.toString(Char.chr(code))
  | unparseExp(logicalAndExp({args,...})) = lparen^(Names.logical_and_name)^(Basic.printSExpListStr(args,unparsePhrase))^rparen
  | unparseExp(logicalOrExp({args,...})) = lparen^(Names.logical_or_name)^(Basic.printSExpListStr(args,unparsePhrase))^rparen
  | unparseExp(stringExp({str,...})) = (Basic.string_quote)^(implode (map Char.chr str))^(Basic.string_quote)
  | unparseExp(termVarExp({term_var,user_sort=NONE,...})) = (Names.variable_prefix)^(AthTermVar.name(term_var))
  | unparseExp(termVarExp({term_var,user_sort=SOME(sort),...})) = (Names.variable_prefix)^(AthTermVar.name(term_var))^":"^
                                                                  (SymTerm.toString(SymTerm.stripTags(sort),printSymTermVar))
  | unparseExp(propConExp({con,...})) = propConToString(con)
  | unparseExp(checkExp({clauses,...})) = lparen^(Names.check_name)^space^(unparseCheckClauses clauses)^rparen
  | unparseExp(matchExp({discriminant,clauses,...})) = 
      lparen^"match "^(unparsePhrase discriminant)^space^"\n"^(unparseMatchClauses clauses)^rparen
  | unparseExp(functionExp({params,body,...})) = lparen^(Names.lambda_name)^space^lparen^(unparsePWCParams params)^rparen^space^
                                                 (unparseExp body)^rparen
  | unparseExp(methodExp({params,body,...})) = lparen^(Names.method_name)^space^lparen^(unparsePWCParams params)^rparen^space^
                                                 (unparseDed body)^rparen
  | unparseExp(appExp({proc,args,...})) = 
      (lparen^(unparsePhrase proc)^space^(Basic.printSExpListStr(args,unparsePhrase))^rparen)
  | unparseExp(BAppExp({proc,arg1,arg2,pos,...})) = 
       lparen^(unparsePhrase proc)^space^(Basic.printSExpListStr([arg1,arg2],unparsePhrase))^rparen
  | unparseExp(UAppExp({proc,arg,pos,...})) = 
       lparen^(unparsePhrase proc)^space^(Basic.printSExpListStr([arg],unparsePhrase))^rparen
  | unparseExp(listExp({members,...})) = lbrack^(Basic.printSExpListStr(members,unparsePhrase))^rbrack
  | unparseExp(beginExp({members,...})) = lparen^"seq "^(Basic.printSExpListStr(members,unparsePhrase))^rparen
  | unparseExp(cellExp({contents,...})) = lparen^"cell "^(unparsePhrase contents)^rparen 
  | unparseExp(refExp({cell_exp,...})) = lparen^"ref "^(unparseExp cell_exp)^rparen
  | unparseExp(tryExp({choices,...})) = lparen^"try "^(Basic.printSExpListStr(choices,unparseExp))^rparen
  | unparseExp(setCellExp({cell_exp,set_phrase,...})) = lparen^"set! "^(unparseExp cell_exp)^space^(unparsePhrase set_phrase)^rparen 
  | unparseExp(_) = "(Don't know how to unparse this yet.)"
and unparseExpAndStop(e') = "" 
and printSymTermVar(sym) = (Names.sort_variable_prefix)^(Symbol.name sym)
and unparsePTParam({name,sort_as_sym_term,sort_as_exp,...}:possibly_typed_param) = 
      (case (sort_as_sym_term,sort_as_exp) of
         (SOME(sort),_) => SymTerm.toString(SymTerm.stripTags(sort),printSymTermVar)
       | (_,SOME(e)) => S.name(name)^":"^(unparseExp(e))
       | _ => S.name(name))
and unparsePWCParam(pwcp:possibly_wildcard_param) = 
     (case pwcp of 
         someParam(ptp) => unparsePTParam(ptp)
       | wildCard(_) => Names.wild_card)
and unparsePWCParams(pwcparams) = Basic.printSExpListStr(pwcparams,unparsePWCParam)
and unparseParam({name,...}:param) = S.name(name)
and unparseParams(params:param list) = Basic.printSExpListStr(params,unparseParam)
and unparseMatchClause({pat,exp=e}) = space^space^lparen^(printPat pat)^space^(unparseExp e)^rparen 
and unparseMatchClauses(clauses) = Basic.printSExpListStr(clauses,unparseMatchClause)
and unparseCheckClause({test=boolCond(phr),result,...}:check_clause) = lparen^(unparsePhrase phr)^space^(unparseExp(result))^rparen
  | unparseCheckClause({test=elseCond,result,...}:check_clause) = lparen^(Names.else_name)^space^(unparseExp(result))^rparen
and unparseCheckClauses(clauses) = Basic.printSExpListStr(clauses,unparseCheckClause)
and unparseBinding({bpat,def,...}) = lparen^(printPat bpat)^space^(unparsePhrase def)^rparen
and unparseBindingInfix({bpat,def,...}) = (printPat bpat)^ " := " ^(unparsePhrase def)
and unparseBindings(bindings) = Basic.printSExpListStr(bindings,unparseBinding)
and unparseBindingsInfix(bindings) = Basic.printListStr(bindings,unparseBindingInfix,"; ")
and unparseDed(methodAppDed({method,args,pos})) = "(!"^(unparseExp method)^space^(Basic.printSExpListStr(args,unparsePhrase))^")"
  | unparseDed(UMethAppDed({method, arg, pos})) = "(!"^(unparseExp method)^space^(Basic.printSExpListStr([arg],unparsePhrase))^")"
  | unparseDed(BMethAppDed({method, arg1, arg2, pos})) = "(!"^(unparseExp method)^space^(Basic.printSExpListStr([arg1,arg2],unparsePhrase))^")"
  | unparseDed(letDed({bindings,body,pos,...})) = "let {"^(unparseBindingsInfix bindings)^"}"^space^(unparseDed body)
  | unparseDed(beginDed({members,pos,...})) = "{"^(Basic.printListStr(members, unparseDed, ";\n"))^"}"
  | unparseDed(matchDed(_)) = "Match ded!"
  | unparseDed(letRecDed(_)) = "Letrec ded!"
  | unparseDed(checkDed(_)) = "Check ded!"
  | unparseDed(assumeDed(_)) = "Assume ded!"
  | unparseDed(infixAssumeDed(_)) = "Infix Assume ded!"
  | unparseDed(assumeLetDed(_)) = "Assume-Let ded!"
  | unparseDed(absurdDed(_)) = "Absurd ded!"
  | unparseDed(tryDed(_)) = "Try ded!"
  | unparseDed(absurdLetDed(_)) = "Absurd-Let ded!"
  | unparseDed(inductionDed(_)) = "Induction ded!"
  | unparseDed(structureCasesDed(_)) = "Structure-Cases ded!"
  | unparseDed(byDed(_)) = "By ded!"
  | unparseDed(fromDed(_)) = "From ded!"
  | unparseDed(genOverDed(_)) = "Gen-over ded!"
  | unparseDed(pickAnyDed(_)) = "Pick-any ded!"
  | unparseDed(withWitnessDed(_)) = "With-witness ded!"
  | unparseDed(pickWitnessDed(_)) = "Pick-witness ded!"
  | unparseDed(pickWitnessesDed(_)) = "Pick-witnesses ded!"
and unparsePhrase(exp(e)) = unparseExp(e)
  | unparsePhrase(ded(d)) = unparseDed(d)
and
  printPat(idPat(ptp)) = possiblyTypedParamToString(ptp)
  | printPat(anyPat(_)) = Names.wild_card
  | printPat(funSymPat({name,sort_opt=SOME(sort),...})) = (MS.name(name))^":"^(FTerm.toStringDefault(sort))
  | printPat(funSymPat({name,sort_opt=NONE,...})) = MS.name(name)
  | printPat(propConPat({pcon,...})) = propConToString(pcon)
  | printPat(numPat({ath_num,...})) = athNumberToString(ath_num)
  | printPat(constantTermVarPat({term_var,...})) = AthTermVar.toString(term_var,FTerm.varToString)
  | printPat(constantMetaIdPat({name,...})) = printMetaId(Symbol.name(name))
  | printPat(constantStringPat({str,...})) = "\"" ^ (implode(map Char.chr str)) ^ "\""
  | printPat(constantCharPat({ch,...})) = "`" ^ (implode([Char.chr(ch)]))
  | printPat(listPats({member_pats,...})) = "["^Basic.printSExpListStr(member_pats,printPat)^"]"
  | printPat(listPat({head_pat,tail_pat,...})) = "(list-of "^printPat(head_pat)^" "^printPat(tail_pat)^")"
  | printPat(cellPat({pat,...})) = "(cell-of "^printPat(pat)^")"
  | printPat(splitPat({pats,...})) = "(split "^(Basic.printSExpListStr(pats,printPat))^")"
  | printPat(reStarPat({pat,...})) = "(re-* "^(Basic.printSExpListStr([pat],printPat))^")"
  | printPat(rePlusPat({pat,...})) = "(re-+ "^(Basic.printSExpListStr([pat],printPat))^")"
  | printPat(reRangePat({from_pat,to_pat,...})) = "(re-range "^(Basic.printSExpListStr([from_pat],printPat))^" "^(Basic.printSExpListStr([to_pat],printPat))^")"
  | printPat(reRepPat({pat,times,...})) = "(re-rep "^(Basic.printSExpListStr([pat],printPat))^(Int.toString times)^")"
  | printPat(reLitPat({pat,...})) = "(re-lit "^(Basic.printSExpListStr([pat],printPat))^")"
  | printPat(reOptPat({pat,...})) = "(re-? "^(Basic.printSExpListStr([pat],printPat))^")"
  | printPat(valOfPat({id={name,...},...})) = "(val-of "^Symbol.name(name)^")"
  | printPat(valOfPat1({id={name,...},...})) = "(val-of "^Symbol.name(name)^")"
  | printPat(unitValPat(_)) = "()"
  | printPat(namedPat({name,pat,...})) = "("^"bind "^Symbol.name(name)^" "^printPat(pat)^")"
  | printPat(wherePat({pat,guard,...})) = "("^printPat(pat)^" where "^(unparseExp(guard))^")"
  | printPat(disjPat({pats,...})) = "("^(Names.logical_or_name)^" "^Basic.printSExpListStr(pats,printPat)^")"
  | printPat(compoundPat({head_pat,rest_pats,...})) = "("^printPat(head_pat)^" "^
                                                      Basic.printSExpListStr(rest_pats,printPat)^")"
  | printPat(someVarPat({id=pwp,...})) = "(some-var "^pwpToString(pwp)^")"
  | printPat(someQuantPat({id=pwp,...})) = "(some-quant "^pwpToString(pwp)^")"
  | printPat(somePropConPat({id=pwp,...})) = "(some-prop-con "^pwpToString(pwp)^")"
  | printPat(someTermPat({id=pwp,...})) = "(some-term "^pwpToString(pwp)^")"
  | printPat(someAtomPat({id=pwp,...})) = "(some-atom "^pwpToString(pwp)^")"
  | printPat(somePropPat({id=pwp,...})) = "(some-prop "^pwpToString(pwp)^")"
  | printPat(someFunctionPat({id=pwp,...})) = "(some-proc "^pwpToString(pwp)^")"
  | printPat(someMethodPat({id=pwp,...})) = "(some-method "^pwpToString(pwp)^")"
  | printPat(someSymbolPat({id=pwp,...})) = "(some-symbol "^pwpToString(pwp)^")"
  | printPat(someSubPat({id=pwp,...})) = "(some-sub "^pwpToString(pwp)^")"
  | printPat(someListPat({id=pwp,...})) = "(some-list "^pwpToString(pwp)^")"
  | printPat(someVectorPat({id=pwp,...})) = "(some-vector "^pwpToString(pwp)^")"
  | printPat(someCharPat({id=pwp,...})) = "(some-char "^pwpToString(pwp)^")"
  | printPat(someTablePat({id=pwp,...})) = "(some-table "^pwpToString(pwp)^")"
  | printPat(someMapPat({id=pwp,...})) = "(some-map "^pwpToString(pwp)^")"
  | printPat(someCellPat({id=pwp,...})) = "(some-cell "^pwpToString(pwp)^")"

fun isSomeTypePat(p) = 
  let fun f(someVarPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someQuantPat({id=someParam({name,...}),...})) = SOME(name)
        | f(somePropConPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someTermPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someAtomPat({id=someParam({name,...}),...})) = SOME(name)
        | f(somePropPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someFunctionPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someMethodPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someSymbolPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someSubPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someListPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someVectorPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someCharPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someCellPat({id=someParam({name,...}),...})) = SOME(name)
        | f(someTablePat({id=someParam({name,...}),...})) = SOME(name)
        | f(someMapPat({id=someParam({name,...}),...})) = SOME(name)
        | f(_) = NONE
  in
     f(p)
  end
  
fun patBindableIds(pat) = 
  let fun f(idPat({name,...})) = Symbol.singleton(name)
        | f(listPats({member_pats,...})) = fLst(member_pats)
        | f(listPat({head_pat,tail_pat,...})) = Symbol.union(f(head_pat),f(tail_pat))
        | f(cellPat({pat,...})) = f(pat)
        | f(splitPat({pats,...})) = fLst(pats)
        | f(reStarPat({pat,...})) = f(pat)
        | f(rePlusPat({pat,...})) = f(pat)
        | f(reRangePat({from_pat,to_pat,...})) = fLst([from_pat,to_pat])
        | f(reRepPat({pat,...})) = f(pat)
        | f(reLitPat({pat,...})) = f(pat)
        | f(reOptPat({pat,...})) = f(pat)
        | f(namedPat({name,pat,...})) = Symbol.add(name,f(pat))
        | f(someVarPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someQuantPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(somePropConPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someTermPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someAtomPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(somePropPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someFunctionPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someMethodPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someSymbolPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someSubPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someListPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someVectorPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someCharPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someCellPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someTablePat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(someMapPat({id=someParam({name,...}),...})) = Symbol.singleton(name)
        | f(compoundPat({head_pat,rest_pats,...})) = Symbol.union(f(head_pat),fLst(rest_pats))
        | f(disjPat({pats,...})) = fLst(pats)
        | f(wherePat({pat,guard,...})) = f(pat)
        | f(_) = Symbol.empty_set
      and fLst1([],res) = res
        | fLst1(p::more,res) = fLst1(more,Symbol.union(f(p),res))
      and fLst(pl) = fLst1(pl,Symbol.empty_set)
  in
    f(pat)
  end

fun getPatCode(constantCharPat({ch,...})) = Real.fromInt(ch)
  | getPatCode(numPat({ath_num,...})) = getRealMagnitude(ath_num)
  | getPatCode(_) = ~1.0

fun getPatCodes(pats) = 
      (case pats of
         (constantCharPat({ch=c1,...}),constantCharPat({ch=c2,...})) => (Real.fromInt(c1),Real.fromInt(c2))
       | (constantCharPat({ch=c1,...}),numPat({ath_num=a1,...})) => (Real.fromInt(c1),getRealMagnitude(a1))
       | (numPat({ath_num=a1,...}),constantCharPat({ch=c1,...})) => (getRealMagnitude(a1),Real.fromInt(c1))
       | (numPat({ath_num=a1,...}),numPat({ath_num=a2,...})) => (getRealMagnitude(a1),getRealMagnitude(a2))
       | _ => (2.0,1.0))

fun patToRegEx(p) = 
  let val any_char = GeneralRE.any0(tt0)
      val any_string = GeneralRE.star0(any_char,tt0)
      val ht = Symbol.makeHTable()
      fun f(idPat({name=sym,...}),string_level) = 
	    (case Symbol.find(ht,sym) of
                 SOME(_) => GeneralRE.backref0(sym)
               | _ => let val _ = Symbol.insert(ht,sym,true)
                          val e = if string_level then any_string else any_char
	                  val e' = GeneralRE.swapTags(e,{name=SOME(sym),con=NONE})
                      in
                         e'                                                
                      end)
        | f(anyPat({pos,...}),string_level) = if string_level then any_string else any_char 
        | f(reStarPat({pat,pos,...}),string_level) = GeneralRE.star0(f(pat,string_level),tt0)
        | f(reOptPat({pat,pos,...}),string_level) = unionLst([GeneralRE.null0(tt0),f(pat,string_level)])
        | f(rePlusPat({pat,pos,...}),string_level) = let val e = f(pat,string_level)
                                                     in
                                                        concatLst([e,GeneralRE.star0(e,tt0)])
                                                     end
        | f(splitPat({pats,pos,...}),string_level) = concatLst(map (fn p => f(p,string_level)) pats)
        | f(reRangePat({from_pat,to_pat,pos,lo,hi,...}),string_level) = GeneralRE.range0(lo,hi,tt0)
        | f(reRepPat({pat,times,pos,...}),string_level) = concatLst(map (fn p => f(p,string_level))
                                                                        (map (fn _ => pat) (Basic.fromI2N(1,times))))
	| f(listPat({head_pat,tail_pat,...}),string_level) = 
              GeneralRE.concat0(GeneralRE.lit0(head_pat,tt0),f(tail_pat,string_level),tt0)
	| f(listPats({member_pats,...}),_) = concatLst'(map (fn x => f(x,false)) member_pats)
	| f(constantStringPat({str,pos,...}),string_level) = concatLst(map (fn c => GeneralRE.lit0(constantCharPat({ch=c,pos=pos}),tt0)) str)
	| f(namedPat({pat,name=sym,...}),string_level) = 
             let val e = f(pat,string_level)
	         val _ = Symbol.insert(ht,sym,true)
                 val {con as con_opt,...}: expression GeneralRE.tag0 = GeneralRE.tagOf(e)
	     in
                GeneralRE.swapTags(e,{name=SOME(sym),con=con_opt})
             end
        | f(wherePat({guard,pat,...}),string_level) = 
               let val e = f(pat,string_level)
	           val {name as name_opt,...}: expression GeneralRE.tag0 = GeneralRE.tagOf(e)
               in
                  GeneralRE.swapTags(e,{name=name_opt,con=SOME(guard)})
               end
        | f(disjPat({pats,...}),string_level) = 
               let val exps = map (fn p => f(p,string_level)) pats
               in
                  unionLst(exps)
               end
        | f(reLitPat({pat,...}),_) = 
            let val res = GeneralRE.lit0(pat,tt0)      
                val ids = patBindableIds(pat) 
                val _ = List.app (fn id => Symbol.insert(ht,id,true)) (Symbol.listSymbols ids)
            in
               res 
            end
        | f(p,_) = let val res = GeneralRE.lit0(p,tt0)      
 	               val ids = patBindableIds(p) 
                       val _ = List.app (fn id => Symbol.insert(ht,id,true)) (Symbol.listSymbols ids)
                   in
                      res
                   end
      val res: (pattern,expression) GeneralRE.RE0 = f(p,true)
  in
    res 
  end

fun applyToRE(f_exp,f_pat,e:(pattern,expression) GeneralRE.RE0) = 
  let fun f(GeneralRE.lit0(p,t)) = GeneralRE.lit0(f_pat(p),applyToTag(t))
        | f(GeneralRE.null0(t)) = GeneralRE.null0(applyToTag(t))
        | f(GeneralRE.range0(l,h,t)) = GeneralRE.range0(l,h,applyToTag(t))
        | f(GeneralRE.any0(t)) = GeneralRE.any0(applyToTag(t))
        | f(e as GeneralRE.backref0(_)) = e
        | f(GeneralRE.concat0(e1,e2,t)) = GeneralRE.concat0(f(e1),f(e2),applyToTag(t))
        | f(GeneralRE.union0(e1,e2,t)) = GeneralRE.union0(f(e1),f(e2),applyToTag(t))
        | f(GeneralRE.star0(e,t)) = GeneralRE.star0(f(e),applyToTag(t))
  and applyToTag(t:expression GeneralRE.tag0 as {name,con=SOME(e)}) = {name=name,con=SOME(f_exp(e))}
    | applyToTag(t) = t
  in
     f(e)
  end

fun isQuantPat(propConPat({pcon=forallCon,...})) = true
  | isQuantPat(propConPat({pcon=existsCon,...})) = true
  | isQuantPat(propConPat({pcon=existsUniqueCon,...})) = true
  | isQuantPat(someQuantPat(_)) = true
  | isQuantPat(namedPat({pat,...})) = isQuantPat(pat)
  | isQuantPat(_) = false


fun quantVarListPat(compoundPat({head_pat,rest_pats as vars_pat::[body_pat],...})) = 
         isQuantPat(head_pat) andalso isListPat(vars_pat)
  | quantVarListPat(_) = false

(* NOTE: printPat must always be kept in sync with the concrete syntax of patterns   *)
(* as specified in athena.lex.                                                       *)

fun isInductivePattern(idPat(_)) = true
  | isInductivePattern(funSymPat(_)) = true
  | isInductivePattern(anyPat(_)) = true
  | isInductivePattern(namedPat({pat,...})) = isInductivePattern(pat)
  | isInductivePattern(numPat(_)) = true
  | isInductivePattern(constantMetaIdPat(_)) = true
  | isInductivePattern(compoundPat({head_pat=funSymPat(_),rest_pats,...})) = 
        List.all isInductivePattern rest_pats
  | isInductivePattern(_) = false

fun isMultipleDTPattern(idPat(_)) = true
  | isMultipleDTPattern(funSymPat(_)) = true
  | isMultipleDTPattern(anyPat(_)) = true
  | isMultipleDTPattern(namedPat({pat,...})) = isMultipleDTPattern(pat)
  | isMultipleDTPattern(numPat(_)) = true
  | isMultipleDTPattern(constantMetaIdPat(_)) = true
  | isMultipleDTPattern(compoundPat({head_pat,rest_pats,...})) = 
        (List.all isMultipleDTPattern (head_pat::rest_pats))
  | isMultipleDTPattern(_) = false

fun posOfExp(idExp({pos,...})) = pos  
  | posOfExp(taggedConSym({pos,...})) = pos 
  | posOfExp(numExp({pos,...})) = pos
  | posOfExp(opExp({pos,...})) = pos 
  | posOfExp(quotedIdeExp({pos,...})) = pos
  | posOfExp(unitExp({pos,...})) = pos
  | posOfExp(charExp({pos,...})) = pos
  | posOfExp(logicalAndExp({pos,...})) = pos
  | posOfExp(logicalOrExp({pos,...})) = pos
  | posOfExp(stringExp({pos,...})) = pos
  | posOfExp(termVarExp({pos,...})) = pos
  | posOfExp(propConExp({pos,...})) = pos
  | posOfExp(checkExp({pos,...})) = pos
  | posOfExp(tryExp({pos,...})) = pos
  | posOfExp(whileExp({pos,...})) = pos
  | posOfExp(beginExp({pos,...})) = pos
  | posOfExp(functionExp({pos,...})) = pos
  | posOfExp(UAppExp({pos,...})) = pos
  | posOfExp(BAppExp({pos,...})) = pos
  | posOfExp(appExp({pos,...})) = pos
  | posOfExp(listExp({pos,...})) = pos
  | posOfExp(methodExp({pos,...})) = pos
  | posOfExp(matchExp({pos,...})) = pos
  | posOfExp(letExp({pos,...})) = pos
  | posOfExp(letRecExp({pos,...}))  = pos
  | posOfExp(setCellExp({pos,...})) = pos
  | posOfExp(refExp({pos,...})) = pos
  | posOfExp(cellExp({pos,...})) = pos
  | posOfExp(vectorInitExp({pos,...})) = pos 
  | posOfExp(vectorSetExp({pos,...})) = pos 
  | posOfExp(vectorSubExp({pos,...})) = pos 
and
    posOfDed(assumeDed({pos,...})) = pos
  | posOfDed(infixAssumeDed({pos,...})) = pos
  | posOfDed(byCasesDed({pos,...})) = pos
  | posOfDed(assumeLetDed({pos,...})) = pos
  | posOfDed(absurdDed({pos,...})) = pos
  | posOfDed(absurdLetDed({pos,...})) = pos
  | posOfDed(methodAppDed({pos,...})) = pos
  | posOfDed(BMethAppDed({pos,...})) = pos
  | posOfDed(UMethAppDed({pos,...})) = pos
  | posOfDed(matchDed({pos,...})) = pos
  | posOfDed(inductionDed({pos,...})) = pos
  | posOfDed(structureCasesDed({pos,...})) = pos
  | posOfDed(byDed({pos,...})) = pos
  | posOfDed(fromDed({pos,...})) = pos
  | posOfDed(tryDed({pos,...})) = pos
  | posOfDed(letDed({pos,...})) = pos
  | posOfDed(letRecDed({pos,...})) = pos
  | posOfDed(beginDed({pos,...})) = pos
  | posOfDed(checkDed({pos,...})) = pos
  | posOfDed(pickAnyDed({pos,...})) = pos
  | posOfDed(genOverDed({pos,...})) = pos
  | posOfDed(withWitnessDed({pos,...})) = pos
  | posOfDed(pickWitnessDed({pos,...})) = pos
  | posOfDed(pickWitnessesDed({pos,...})) = pos
and
    posOfPhrase(exp(e)) = posOfExp(e) 
  | posOfPhrase(ded(d)) = posOfDed(d)

fun isInitIdeChar(ch) = let val c = Char.ord(ch) 
                        in
                          Basic.isMember(c,[35,37,38,92,94,95,60,61,62]) orelse
                          ((c >= 42) andalso (c <= 58)) orelse ((c >= 64) andalso (c <= 90))
                          orelse ((c >= 97) andalso (c <= 126))
                        end
			
fun isInternalIdeChar(ch) = 
     let val c = Char.ord(ch)
     in
        (c = 33) orelse ((c >= 35) andalso (c <= 40)) orelse ((c >= 42) andalso (c <= 58)) orelse
        ((c >= 60) andalso (c <= 92)) orelse (c = 94) orelse ((c >= 95) andalso (c <= 126))
     end                       

fun canBeId(str) = 
     case explode(str) of
        [] => false
      | c::rest => isInitIdeChar(c) andalso List.all isInternalIdeChar rest 

fun patOps(pat) = 
  let fun f(idPat({name,op_tag as NONE,...}),map) = 
              (case S.lookUp(map,name) of
                  SOME(i,j) => map
                | _ => S.enter(map,name,(~1,~1)))
        | f(idPat({name,op_tag as SOME(i,j),...}),map) = S.enter(map,name,(i,j))
        | f(listPats({member_pats,...}),map) = fLst(member_pats,map)
        | f(listPat({head_pat,tail_pat,...}),map) = fLst([head_pat,tail_pat],map)
        | f(cellPat({pat,...}),map) = f(pat,map)
        | f(splitPat({pats,...}),map) = fLst(pats,map)
        | f(reStarPat({pat,...}),map) = f(pat,map)
        | f(rePlusPat({pat,...}),map) = f(pat,map)
        | f(reRangePat({from_pat,to_pat,...}),map) = fLst([from_pat,to_pat],map)
        | f(reRepPat({pat,...}),map) = f(pat,map)
        | f(reLitPat({pat,...}),map) = f(pat,map)
        | f(reOptPat({pat,...}),map) = f(pat,map)
        | f(namedPat({name,pat,...}),map) = S.enter(f(pat,map),name,(~1,~1))
        | f(someVarPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someQuantPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(somePropConPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someTermPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someAtomPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(somePropPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someFunctionPat({id=someParam({name,op_tag as SOME(i,j),...}),...}),map) = S.enter(map,name,(i,j))
        | f(someFunctionPat({id=someParam({name,op_tag as NONE,...}),...}),map) = 
               (case S.lookUp(map,name) of
                   SOME(i,j) => map
                  | _ => S.enter(map,name,(~1,~1)))
        | f(someMethodPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someSymbolPat({id=someParam({name,op_tag as SOME(i,j),...}),...}),map) = S.enter(map,name,(i,j))
        | f(someSymbolPat({id=someParam({name,op_tag as NONE,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someSubPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someListPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someVectorPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someCharPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someCellPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someTablePat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(someMapPat({id=someParam({name,...}),...}),map) = S.enter(map,name,(~1,~1))
        | f(compoundPat({head_pat,rest_pats,...}),map) = fLst(head_pat::rest_pats,map)
        | f(disjPat({pats,...}),map) = fLst(pats,map)
        | f(wherePat({pat,...}),map) = f(pat,map)
        | f(_,map) = map 
      and fLst([],map) = map
        | fLst(p::more,map) = fLst(more,f(p,map))
  in
    f(pat,S.empty_mapping)
  end

fun mpatOps(pat) = 
  let fun f(idPat({name,op_tag as NONE,...}),map) = 
              (case MS.lookUp(map,msym name) of
                  SOME(i,j) => map
                | _ => MS.enter(map,msym name,(~1,~1)))
        | f(idPat({name,op_tag as SOME(i,j),...}),map) = MS.enter(map,msym name,(i,j))
        | f(listPats({member_pats,...}),map) = fLst(member_pats,map)
        | f(listPat({head_pat,tail_pat,...}),map) = fLst([head_pat,tail_pat],map)
        | f(cellPat({pat,...}),map) = f(pat,map)
        | f(splitPat({pats,...}),map) = fLst(pats,map)
        | f(reStarPat({pat,...}),map) = f(pat,map)
        | f(rePlusPat({pat,...}),map) = f(pat,map)
        | f(reRangePat({from_pat,to_pat,...}),map) = fLst([from_pat,to_pat],map)
        | f(reRepPat({pat,...}),map) = f(pat,map)
        | f(reLitPat({pat,...}),map) = f(pat,map)
        | f(reOptPat({pat,...}),map) = f(pat,map)
        | f(namedPat({name,pat,...}),map) = MS.enter(f(pat,map),msym name,(~1,~1))
        | f(someVarPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someQuantPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(somePropConPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someTermPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someAtomPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(somePropPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someFunctionPat({id=someParam({name,op_tag as SOME(i,j),...}),...}),map) = MS.enter(map,msym name,(i,j))
        | f(someFunctionPat({id=someParam({name,op_tag as NONE,...}),...}),map) = 
             let val name' = msym name 
             in  
               (case MS.lookUp(map,name') of
                   SOME(i,j) => map
                  | _ => MS.enter(map,name',(~1,~1)))
             end
        | f(someMethodPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someSymbolPat({id=someParam({name,op_tag as SOME(i,j),...}),...}),map) = MS.enter(map,msym name,(i,j))
        | f(someSymbolPat({id=someParam({name,op_tag as NONE,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someSubPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someListPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someVectorPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someCharPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someCellPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someTablePat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(someMapPat({id=someParam({name,...}),...}),map) = MS.enter(map,msym name,(~1,~1))
        | f(compoundPat({head_pat,rest_pats,...}),map) = fLst(head_pat::rest_pats,map)
        | f(disjPat({pats,...}),map) = fLst(pats,map)
        | f(wherePat({pat,...}),map) = f(pat,map)
        | f(_,map) = map 
      and fLst([],map) = map
        | fLst(p::more,map) = fLst(more,f(p,map))
  in
    f(pat,MS.empty_mapping)
  end

val no_dots_in_ids = ref true

fun checkNoDots(str,pos) = 
   if not(!no_dots_in_ids) then ()
    else 
       if Basic.stringContains(str,fn c => c = #".") then 
          raise SyntaxError("Illegal identifier: "^str^".\nNo dots are allowed inside identifiers in this context",SOME pos)
       else ()

fun checkNoDotsPat(pat) = 
       let val id_set = patBindableIds(pat)
           val res = S.setApp (fn sym => checkNoDots(S.name(sym),posOfPat(pat))) id_set
       in
          res
       end

fun splitBindings(blist) = 
      let fun f([]:binding list,bpats,nameset_lst,defs,pos_lst) = 
                (rev(bpats),rev(nameset_lst),rev(defs),rev(pos_lst))
            | f({bpat,def,pos,...}::more,bpats,nameset_lst,defs,pos_lst) = 
	              f(more,bpat::bpats,(patBindableIds bpat)::nameset_lst,def::defs,pos::pos_lst)
      in
         f(blist,[],[],[],[])
      end

fun splitBindingLst(blist) = 
      let fun f([]:binding list,nameset_lst,defs) = (rev(nameset_lst),rev(defs))
            | f({bpat,def,...}::more,nameset_lst,defs) = f(more,(patBindableIds bpat)::nameset_lst,def::defs)
      in
         f(blist,[],[])
      end

fun splitForModules(str) = 
  (case (String.tokens (fn c => c = #".") str) of
      L as (_::_::_) => let val modules = Basic.allButLast(L)
                        in
                           (modules,List.last(L))
                        end
    | L => if null(L) then ([],".") else ([],List.hd(L)))

fun parseNumberKindFromChars(str_lst) = 
  let val periods  = ref(0)
      fun doStr([]) = true
        | doStr(i::rest) = if Char.isDigit(i) then 
                              doStr(rest)
                           else
                              if i = #"." then 
                                 (Basic.inc(periods);
                                  if !periods > 1 then
                                     false
                                  else
                                     doStr(rest))
                              else
                                  false;
      fun whatNumber(lst) = if null(lst) orelse (lst = [#"."]) then 0
                            else
                               if not(doStr(lst)) then 0
                               else
                                   if !periods > 0 then 2
                                   else 1;
      in
        whatNumber(str_lst)
  end                     

fun parseNumberKind(str) = parseNumberKindFromChars(explode(str))

fun lessThanOne(#"."::_) = true
  | lessThanOne(#"0"::more) = lessThanOne(more)
  | lessThanOne(_) = false

fun getAthNumber(str) = 
          (case parseNumberKind(str) of
             1 => (case Int.fromString(str) of
                      SOME(i) => SOME(int_num(i,ref ""))
                    | _ => NONE)
           | 2 => let    val clist = explode(str)
                         val less_than_one = lessThanOne(clist)
                         val str' = if less_than_one andalso not(null(clist)) andalso hd(clist) = #"." then "0"^str else str
                  in
                     (case Real.fromString(str') of
                         SOME(r) => SOME(real_num(r,ref ""))
                       | _ => NONE)
                  end
           | _ => NONE)

fun legalIdentifier(str) = 
      let
          val len = String.size(str)
          fun inBounds(i) = i >= 0 andalso i < len 
          fun isDot(i) = String.sub(str,i) = #"."
          fun proper(i) = inBounds(i) andalso not(isDot(i))
          fun isNumber(str) = (case getAthNumber(str) of
                                  SOME(_) => true | _ => false)
          fun loop(i) = if not(inBounds(i)) then true
                        else if isDot(i) then (if proper(i+1) andalso proper(i-1) then loop(i+1) else false)
                             else loop(i+1)
      in
        if len = 1 andalso isDot(0) then true else 
           let val res = loop(0)
           in
             if not(res) then
                (if isNumber(str) then true else false)
             else res
           end
      end
      
fun splitForModules(str) = 
 if legalIdentifier(str) then 
  (case (String.tokens (fn c => c = #".") str) of
      L as (_::_::_) => let val modules = Basic.allButLast(L)
                        in
                           (modules,List.last(L))
                        end
    | L => if null(L) then ([],".") else ([],List.hd(L)))
 else raise SyntaxError("Illegal identifier: "^str,NONE)

fun makeModString(sym_list,sym) = Basic.printListStr(sym_list@[sym],Symbol.name,".")

fun makeMS(str,pos_opt) = 
     let val (modules,id) = splitForModules(str)
         val (modules',id') = (map Symbol.symbol modules,Symbol.symbol id)
         val s = Symbol.symbol str
         val ms = ModSymbol.makeModSymbol(modules',id',s)
     in
         ms 
     end

fun isNumeral(str) = let val num_kind = parseNumberKind(str)
                     in
                       num_kind = 1 orelse num_kind = 2
                     end

datatype aux_fsym_declaration_entry = fsym_prec of int * pos | fsym_assoc of bool * pos | fsym_overload of param | fsym_input_expansion of expression list * pos 

fun getAuxEntry((str,pos)) =
        (case Int.fromString(str) of 
            SOME(i) => fsym_prec(i,pos)
          | _ => (case str of 
                     "left-assoc" => fsym_assoc(true,pos)
                   | "right-assoc" => fsym_assoc(false,pos)
                   | _ => fsym_overload({name=S.symbol(str),pos=pos})))

fun makeFromOneEntry(fsym_prec(i,pos),exp_list_option) = {precedence=SOME(i),assoc=NONE,overload_sym=NONE,input_transformer=exp_list_option}
  | makeFromOneEntry(fsym_assoc(b,pos),elo) = {precedence=NONE,assoc=SOME(b),overload_sym=NONE,input_transformer=elo}
  | makeFromOneEntry(fsym_overload(p:param as {name=s,pos,...}),elo) = {precedence=NONE,assoc=NONE,overload_sym=SOME(p),input_transformer=elo}

fun makeFromTwoEntries([fsym_prec(i,pos),fsym_assoc(b,pos')],elo) = ({precedence=SOME(i),assoc=SOME(b),overload_sym=NONE,input_transformer=elo})
  | makeFromTwoEntries([fsym_prec(i,pos),fsym_overload(p as {name=s,pos=pos',...})],elo) = {precedence=SOME(i),assoc=NONE,overload_sym=SOME(p),input_transformer=elo}
  | makeFromTwoEntries([fsym_assoc(b,pos),fsym_prec(i,pos')],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=NONE,input_transformer=elo}
  | makeFromTwoEntries([fsym_assoc(b,pos),fsym_overload(p as {name=s,pos=pos',...})],elo) = {precedence=NONE,assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}
  | makeFromTwoEntries([fsym_overload(p as {name=s,pos,...}),fsym_prec(i,pos')],elo) = {precedence=SOME(i),assoc=NONE,overload_sym=SOME(p),input_transformer=elo}
  | makeFromTwoEntries([fsym_overload(p as {name=s,pos,...}),fsym_assoc(b,pos')],elo) = {precedence=NONE,assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo} 

fun makeFromThreeEntries([fsym_prec(i,pos),fsym_assoc(b,pos2),fsym_overload(p as {name=s,pos=pos3,...})],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}
  | makeFromThreeEntries([fsym_prec(i,pos),fsym_overload(p as {name=s,pos=pos2,...}),fsym_assoc(b,pos3)],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}
  | makeFromThreeEntries([fsym_assoc(b,pos),fsym_prec(i,pos2),fsym_overload(p as {name=s,pos=pos3,...})],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}
  | makeFromThreeEntries([fsym_assoc(b,pos),fsym_overload(p as {name=s,pos=pos2,...}),fsym_prec(i,pos3)],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}
  | makeFromThreeEntries([fsym_overload(p as {name=s,pos,...}),fsym_prec(i,pos2),fsym_assoc(b,pos3)],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}
  | makeFromThreeEntries([fsym_overload(p as {name=s,pos,...}),fsym_assoc(b,pos2),fsym_prec(i,pos3)],elo) = {precedence=SOME(i),assoc=SOME(b),overload_sym=SOME(p),input_transformer=elo}

fun makeAssocId(true) = "left-assoc"
  | makeAssocId(false) = "right-assoc" 

fun getPrecAssocOverloadSymFromFSymDeclaration(id_pos_list,exp_list_option) = 
     (case (List.map getAuxEntry id_pos_list) of 
         [entry] => let val res: {assoc:bool option, overload_sym:param option,precedence:int option,
                                  input_transformer:expression list option} = makeFromOneEntry(entry,exp_list_option) 
                    in res end
       | L as [entry_1,entry_2] => (makeFromTwoEntries(L,exp_list_option))
       | L as [entry_1,entry_2,entry_3] => (makeFromThreeEntries(L,exp_list_option)))

fun getCaseClausesAltsDeds(c) = 
       let fun f([]:case_clause list,(al,pl)) = (rev al,rev pl)
            |  f({alt,proof,...}::more,(al,pl)) = f(more,(alt::al,proof::pl))
        in
         f(c,([],[]))
       end

fun expVars(termVarExp({term_var,...}),vars) = term_var::vars
  | expVars(logicalAndExp({args,...}),vars) = phraseVarsLst(args,vars)
  | expVars(logicalOrExp({args,...}),vars) = phraseVarsLst(args,vars)
  | expVars(whileExp({test,body,...}),vars) = phraseVarsLst([test,body],vars)
  | expVars(beginExp({members,...}),vars) = phraseVarsLst(members,vars)
  | expVars(checkExp({clauses,...}),vars) = checkClauseVarsLst(clauses,vars)
  | expVars(tryExp({choices,...}),vars) = expVarsLst(choices,vars)
  | expVars(matchExp({discriminant,clauses,...}),vars) = 
       phraseVars(discriminant,matchClauseVarsLst(clauses,vars))
  | expVars(functionExp({body,...}),vars) = expVars(body,vars)
  | expVars(appExp({proc,args,...}),vars) = phraseVarsLst(args,phraseVars(proc,vars))
  | expVars(UAppExp({proc,arg,...}),vars) = phraseVarsLst([arg],phraseVars(proc,vars))
  | expVars(BAppExp({proc,arg1,arg2,...}),vars) = phraseVarsLst([arg1,arg2],phraseVars(proc,vars))
  | expVars(listExp({members,...}),vars) = phraseVarsLst(members,vars)
  | expVars(methodExp({body,...}),vars) = dedVars(body,vars)
  | expVars(letExp({bindings,body,...}),vars) = expVars(body,bindingVarsLst(bindings,vars))
  | expVars(letRecExp({bindings,body,...}),vars) = expVars(body,bindingVarsLst(bindings,vars)) 
  | expVars(cellExp({contents,...}),vars) = phraseVars(contents,vars)
  | expVars(refExp({cell_exp,...}),vars) = expVars(cell_exp,vars)
  | expVars(setCellExp({cell_exp,set_phrase,...}),vars) = expVars(cell_exp,phraseVars(set_phrase,vars))
  | expVars(vectorInitExp({length_exp,init_val,...}),vars) = phraseVars(init_val,expVars(length_exp,vars))
  | expVars(vectorSetExp({vector_exp,index_exp,new_val,...}),vars) = 
       phraseVars(new_val,expVars(index_exp,expVars(vector_exp,vars)))
  | expVars(vectorSubExp({vector_exp,index_exp,...}),vars) = expVars(vector_exp,expVars(index_exp,vars))
  | expVars(_,vars) = vars
and
    expVarsLst([],vars) = vars
  | expVarsLst(e::more,vars) = expVarsLst(more,expVars(e,vars))
and 
    dedVars(assumeDed({assumption,body,...}),vars) = dedVars(body,phraseVars(assumption,vars))
  | dedVars(infixAssumeDed({bindings,body,...}),vars) = dedVars(body,bindingVarsLst(bindings,vars)) 
  | dedVars(byCasesDed({disj,from_exps=NONE,arms,...}),vars) =
       let val (alts,deds) = getCaseClausesAltsDeds(arms)
       in
          dedVarsLst(deds,expVarsLst(alts,phraseVars(disj,vars)))
       end
  | dedVars(byCasesDed({disj,from_exps=SOME(exps),arms,...}),vars) = 
       let val (alts,deds) = getCaseClausesAltsDeds(arms)
       in
          dedVarsLst(deds,expVarsLst(alts,expVarsLst(exps,phraseVars(disj,vars))))
       end
  | dedVars(assumeLetDed({bindings,body,...}),vars) = dedVars(body,bindingVarsLst(bindings,vars))
  | dedVars(absurdDed({hyp,body,...}),vars) = dedVars(body,phraseVars(hyp,vars))
  | dedVars(absurdLetDed({named_hyp,body,...}),vars) = dedVars(body,bindingVars(named_hyp,vars))
  | dedVars(methodAppDed({method,args,...}),vars) = phraseVarsLst(args,expVars(method,vars))
  | dedVars(BMethAppDed({method,arg1,arg2,...}),vars) = phraseVarsLst([arg1,arg2],expVars(method,vars))
  | dedVars(UMethAppDed({method,arg,...}),vars) = phraseVars(arg,expVars(method,vars))
  | dedVars(matchDed({discriminant,clauses,...}),vars) = 
        dmatchClauseVarsLst(clauses,phraseVars(discriminant,vars))
  | dedVars(inductionDed({prop,clauses,...}),vars) = 
        dmatchClauseVarsLst(clauses,phraseVars(prop,vars))
  | dedVars(structureCasesDed({prop,clauses,...}),vars) = 
        dmatchClauseVarsLst(clauses,phraseVars(prop,vars))
  | dedVars(tryDed({choices,...}),vars) = dedVarsLst(choices,vars)
  | dedVars(letDed({bindings,body,...}),vars) = dedVars(body,bindingVarsLst(bindings,vars))
  | dedVars(letRecDed({bindings,body,...}),vars) = dedVars(body,bindingVarsLst(bindings,vars))
  | dedVars(beginDed({members,...}),vars) = dedVarsLst(members,vars)
  | dedVars(checkDed({clauses,...}),vars) = dcheckClauseVarsLst(clauses,vars)
  | dedVars(byDed({wanted_res,body,...}),vars) = dedVars(body,expVars(wanted_res,vars))
  | dedVars(fromDed({conclusion,premises,...}),vars) = expVars(conclusion,expVars(premises,vars))
  | dedVars(genOverDed({eigenvar_exp,body,...}),vars) = dedVars(body,expVars(eigenvar_exp,vars))
  | dedVars(pickAnyDed({body,...}),vars) = dedVars(body,vars)
  | dedVars(withWitnessDed({eigenvar_exp,body,...}),vars) = dedVars(body,expVars(eigenvar_exp,vars))
  | dedVars(pickWitnessDed({ex_gen,body,...}),vars) = dedVars(body,phraseVars(ex_gen,vars))
  | dedVars(pickWitnessesDed({ex_gen,body,...}),vars) = dedVars(body,phraseVars(ex_gen,vars))
and                
    dedVarsLst([],vars) = vars
  | dedVarsLst(d::rest,vars) = dedVarsLst(rest,dedVars(d,vars))
and
    phraseVars(exp(e),vars) = expVars(e,vars)
  | phraseVars(ded(d),vars) = dedVars(d,vars)
and
    phraseVarsLst([],vars) = vars
  | phraseVarsLst(p::more,vars) = phraseVarsLst(more,phraseVars(p,vars))
and                                 
    checkClauseVars({test=elseCond,result}:check_clause,vars) = expVars(result,vars)
  | checkClauseVars({test=boolCond(p),result},vars) = expVars(result,phraseVars(p,vars))
and
    checkClauseVarsLst([],vars) = vars                  
  | checkClauseVarsLst(c::more,vars) = checkClauseVarsLst(more,checkClauseVars(c,vars))
and                                                      
    dcheckClauseVars({test=elseCond,result}:dcheck_clause,vars) = dedVars(result,vars)
  | dcheckClauseVars({test=boolCond(p),result},vars) = dedVars(result,phraseVars(p,vars))
and
    dcheckClauseVarsLst([],vars) = vars                   
  | dcheckClauseVarsLst(c::more,vars) = dcheckClauseVarsLst(more,dcheckClauseVars(c,vars))
and                                               
    bindingVars({def,...}:binding,vars) = phraseVars(def,vars)
and
    bindingVarsLst([],vars) = vars
  | bindingVarsLst(b::more,vars) = bindingVarsLst(more,bindingVars(b,vars))
and
    matchClauseVars({pat,exp=exp'}:match_clause,vars) = patVars(pat,expVars(exp',vars))
and
    dmatchClauseVars({pat,ded=ded'}:dmatch_clause,vars) = patVars(pat,dedVars(ded',vars))
and                                                 
    matchClauseVarsLst([],vars) = vars                  
  | matchClauseVarsLst(c::more,vars) = matchClauseVarsLst(more,matchClauseVars(c,vars))
and                                            
    dmatchClauseVarsLst([],vars) = vars            
  | dmatchClauseVarsLst(c::more,vars) = dmatchClauseVarsLst(more,dmatchClauseVars(c,vars))
and                                                     
    patVars(constantTermVarPat({term_var,...}),vars) = term_var::vars
  | patVars(listPats({member_pats,...}),vars) = patVarsLst(member_pats,vars)
  | patVars(listPat({head_pat,tail_pat,...}),vars) = patVars(tail_pat,patVars(head_pat,vars))
  | patVars(cellPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(splitPat({pats,...}),vars) = patVarsLst(pats,vars)
  | patVars(reStarPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(rePlusPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(reRangePat({from_pat,to_pat,...}),vars) = patVarsLst([from_pat,to_pat],vars)
  | patVars(reRepPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(reLitPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(reOptPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(namedPat({pat,...}),vars) = patVars(pat,vars)
  | patVars(compoundPat({head_pat,rest_pats,...}),vars) = patVarsLst(rest_pats,patVars(head_pat,vars))
  | patVars(wherePat({pat,guard,...}),vars) = patVars(pat,expVars(guard,vars))
  | patVars(disjPat({pats,...}),vars) = patVarsLst(pats,vars)
  | patVars(_,vars) = vars                                   
and                                                 
    patVarsLst([],vars) = vars                        
  | patVarsLst(p::more,vars) = patVarsLst(more,patVars(p,vars)) 

fun getExpVars(e) = expVars(e,[])
fun getDedVars(d) = dedVars(d,[])
fun getPhraseVars(p) = phraseVars(p,[])

fun valOfIds(pat) = 
  let fun f(valOfPat({id={name,...},...}),res) = Symbol.add(name,res)
        | f(valOfPat1({id={name,...},...}),res) = Symbol.add(name,res)
        | f(listPats({member_pats,...}),res) = fLst(member_pats,res)
        | f(listPat({head_pat,tail_pat,...}),res) = fLst([head_pat,tail_pat],res)
        | f(cellPat({pat,...}),res) = f(pat,res)
        | f(splitPat({pats,...}),res) = fLst(pats,res)
        | f(reStarPat({pat,...}),res) = f(pat,res)
        | f(rePlusPat({pat,...}),res) = f(pat,res)
        | f(reRangePat({from_pat,to_pat,...}),res) = fLst([from_pat,to_pat],res)
        | f(reRepPat({pat,times,...}),res) = f(pat,res)
        | f(reOptPat({pat,...}),res) = f(pat,res)
        | f(namedPat({pat,...}),res) = f(pat,res)
        | f(compoundPat({head_pat,rest_pats,...}),res) = fLst(head_pat::rest_pats,res)
        | f(wherePat({pat,...}),res) = f(pat,res)
        | f(disjPat({pats,...}),res) = fLst(pats,res)
        | f(_,res) = res
      and
          fLst([],res) = res
        | fLst(p::more,res) = fLst(more,f(p,res))
  in
     f(pat,Symbol.empty_set)
  end

fun freeVarsExp(idExp({msym,...})) = MS.singleton(msym)
  | freeVarsExp(taggedConSym({name,...})) = MS.singleton(name)
  | freeVarsExp(opExp({op_exp,...})) = freeVarsExp(op_exp)
  | freeVarsExp(numExp({number,...})) = MS.singleton(msym (S.symbol(athNumberToString(number))))
  | freeVarsExp(logicalAndExp({args,...})) = freeVarsPhraseLst(args)
  | freeVarsExp(logicalOrExp({args,...})) = freeVarsPhraseLst(args)
  | freeVarsExp(whileExp({test,body,...})) = MS.union(freeVarsPhrase(body),freeVarsPhrase(test))
  | freeVarsExp(beginExp({members,...})) = freeVarsPhraseLst(members)
  | freeVarsExp(tryExp({choices,...})) = freeVarsExpLst(choices,MS.empty_set)
  | freeVarsExp(checkExp({clauses,...})) = freeVarsCheckClauseLst(clauses)
  | freeVarsExp(functionExp({params,body,...})) = MS.difference(freeVarsExp(body),
                                                              MS.symListToSet(map msym (getPWParamNames params)))
  | freeVarsExp(methodExp({params,body,...})) = MS.difference(freeVarsDed(body),
                                                              MS.symListToSet(map msym (getPWParamNames(params))))
  | freeVarsExp(appExp({proc,args,...})) = MS.union(freeVarsPhrase(proc),freeVarsPhraseLst(args))
  | freeVarsExp(UAppExp({proc,arg,...})) = MS.union(freeVarsPhrase(proc),freeVarsPhrase(arg))
  | freeVarsExp(BAppExp({proc,arg1,arg2,...})) = MS.union(freeVarsPhrase(proc),freeVarsPhraseLst([arg1,arg2]))
  | freeVarsExp(listExp({members,...})) = freeVarsPhraseLst(members)
  | freeVarsExp(matchExp({discriminant,clauses,...})) = 
       MS.union(freeVarsPhrase(discriminant),freeVarsMatchClauseLst(clauses))
  | freeVarsExp(letExp({bindings,body,...})) = 
        let val (nameset_lst,defs) = splitBindingLst(bindings)
            val body_fvars = MS.difference(freeVarsExp(body),msyms (Symbol.unionLst nameset_lst))
        in
           MS.union(freeVarsLetBindingLst(map msyms nameset_lst,defs),body_fvars)
        end
  | freeVarsExp(letRecExp({bindings,body,...})) = 
       let val name_set = Symbol.unionLst(map (fn b:binding as {bpat,...} => patBindableIds(bpat)) bindings)
           val mname_set = msyms name_set
           val body_fvars = MS.difference(freeVarsExp(body),mname_set)
           val binding_fvs = fvLetRecBindingLst(bindings,MS.empty_set,mname_set)
       in
         MS.union(body_fvars,binding_fvs)
       end
 | freeVarsExp(cellExp({contents,...})) = freeVarsPhrase(contents)
 | freeVarsExp(refExp({cell_exp,...})) = freeVarsExp(cell_exp)
 | freeVarsExp(setCellExp({cell_exp,set_phrase,...})) = 
         MS.union(freeVarsExp(cell_exp),freeVarsPhrase(set_phrase))
 | freeVarsExp(vectorInitExp({length_exp,init_val,...})) = 
        MS.union(freeVarsExp(length_exp),freeVarsPhrase(init_val))
 | freeVarsExp(vectorSetExp({vector_exp,index_exp,new_val,...})) = 
        MS.union(freeVarsExp(vector_exp),MS.union(freeVarsExp(index_exp),freeVarsPhrase(new_val)))
 | freeVarsExp(vectorSubExp({vector_exp,index_exp,...})) =   
           MS.union(freeVarsExp(vector_exp),freeVarsExp(index_exp))
 | freeVarsExp(_) = MS.empty_set
and
   freeVarsDed(assumeDed({assumption,body,...})) = MS.union(freeVarsPhrase(assumption),freeVarsDed(body))
 | freeVarsDed(assumeLetDed({bindings,body,...})) = 
        let val (nameset_lst,defs) = splitBindingLst(bindings)
            val body_fvars = MS.difference(freeVarsDed(body),msyms (Symbol.unionLst nameset_lst))
        in
           MS.union(freeVarsLetBindingLst(map msyms nameset_lst,defs),body_fvars)
        end        
 | freeVarsDed(infixAssumeDed({bindings,body,...})) = 
        let val (nameset_lst,defs) = splitBindingLst(bindings)
            val body_fvars = MS.difference(freeVarsDed(body),msyms (Symbol.unionLst nameset_lst))
        in
           MS.union(freeVarsLetBindingLst(map msyms nameset_lst,defs),body_fvars)
        end        
 | freeVarsDed(byCasesDed({disj,from_exps=SOME(exps),arms,...})) = 
        let val (alts,deds) = getCaseClausesAltsDeds(arms)
           val U = MS.unionLst
           fun caseClausesFV([],res) = res
             | caseClausesFV((cc:case_clause as {case_name=SOME({name,...}),alt,proof})::more,res) =
                 caseClausesFV(more,MS.union(res,MS.union(freeVarsExp(alt),
                               MS.difference(freeVarsDed(proof),MS.symListToSet([msym name])))))
             | caseClausesFV((cc:case_clause as {case_name=NONE,alt,proof})::more,res) =
                 caseClausesFV(more,MS.union(res,
                                    MS.union(freeVarsExp(alt),freeVarsDed(proof))))
        in
         caseClausesFV(arms,MS.union(freeVarsPhrase(disj),freeVarsPhraseLst(map exp exps)))
       end
 | freeVarsDed(byCasesDed({disj,from_exps=NONE,arms,...})) = MS.empty_set
 | freeVarsDed(absurdDed({hyp,body,...})) = MS.union(freeVarsPhrase(hyp),freeVarsDed(body))
 | freeVarsDed(letDed({bindings,body,...})) = 
        let val (nameset_lst,defs) = splitBindingLst(bindings)
            val body_fvars = MS.difference(freeVarsDed(body),msyms (Symbol.unionLst nameset_lst))
        in
           MS.union(freeVarsLetBindingLst(map msyms nameset_lst,defs),body_fvars)
        end
 | freeVarsDed(letRecDed({bindings,body,...})) = 
       let val name_set = Symbol.unionLst(map (fn b:binding as {bpat,...} => patBindableIds(bpat)) bindings)
           val mname_set = msyms name_set
           val body_fvars = MS.difference(freeVarsDed(body),mname_set)
           val binding_fvs = fvLetRecBindingLst(bindings,MS.empty_set,mname_set)
       in
         MS.union(body_fvars,binding_fvs)
       end
 | freeVarsDed(methodAppDed({method,args,...})) = MS.union(freeVarsExp(method),freeVarsPhraseLst(args))
 | freeVarsDed(BMethAppDed({method,arg1,arg2,...})) = MS.union(freeVarsExp(method),freeVarsPhraseLst([arg1,arg2]))
 | freeVarsDed(UMethAppDed({method,arg,...})) = MS.union(freeVarsExp(method),freeVarsPhrase(arg))
 | freeVarsDed(matchDed({discriminant,clauses,...})) = 
      MS.union(freeVarsPhrase(discriminant),freeVarsDMatchClauseLst(clauses))
 | freeVarsDed(inductionDed({prop,clauses,...})) = 
       MS.union(freeVarsPhrase(prop),freeVarsDMatchClauseLst(clauses))
 | freeVarsDed(structureCasesDed({prop,clauses,...})) = 
       MS.union(freeVarsPhrase(prop),freeVarsDMatchClauseLst(clauses))
 | freeVarsDed(tryDed({choices,...})) = freeVarsDedLst(choices)
 | freeVarsDed(beginDed({members,...})) = freeVarsDedLst(members)
 | freeVarsDed(checkDed({clauses,...})) = freeVarsDCheckClauseLst(clauses)
 | freeVarsDed(byDed({wanted_res,conc_name=NONE,body,...})) = MS.union(freeVarsExp(wanted_res),freeVarsDed(body))
 | freeVarsDed(byDed({wanted_res,conc_name=SOME({name,pos,...}),body,...})) = 
       MS.union(freeVarsExp(wanted_res),MS.difference(freeVarsDed(body),MS.singleton(msym name)))
 | freeVarsDed(fromDed({conclusion,premises,...})) = MS.union(freeVarsExp(conclusion),
								  freeVarsExp(premises))
 | freeVarsDed(genOverDed({eigenvar_exp,body,...})) = MS.union(freeVarsExp(eigenvar_exp),freeVarsDed(body))
 | freeVarsDed(pickAnyDed({eigenvars,body,...})) = MS.difference(freeVarsDed(body),
						   msyms (Symbol.symListToSet(map #name eigenvars)))
 | freeVarsDed(withWitnessDed({eigenvar_exp,ex_gen,body,...})) = 
     MS.union(freeVarsExp(eigenvar_exp),MS.union(freeVarsPhrase(ex_gen),freeVarsDed(body)))
 | freeVarsDed(pickWitnessDed({ex_gen,var_id,inst_id=SOME(in_id),body,...})) = 
      MS.union(freeVarsPhrase(ex_gen),MS.difference(freeVarsDed(body),msyms(Symbol.symListToSet([var_id,in_id]))))
 | freeVarsDed(pickWitnessDed({ex_gen,var_id,inst_id=NONE,body,...})) = 
      MS.union(freeVarsPhrase(ex_gen),MS.difference(freeVarsDed(body),MS.symListToSet([msym var_id])))
 | freeVarsDed(pickWitnessesDed({ex_gen,var_ids,inst_id=SOME(in_id),body,...})) = 
      MS.union(freeVarsPhrase(ex_gen),MS.difference(freeVarsDed(body),msyms(Symbol.symListToSet([in_id]@var_ids))))
 | freeVarsDed(pickWitnessesDed({ex_gen,var_ids,inst_id=NONE,body,...})) = 
      MS.union(freeVarsPhrase(ex_gen),MS.difference(freeVarsDed(body),msyms(Symbol.symListToSet(var_ids))))
and
   fvDedLst([],res) = res
 | fvDedLst(d::more,res) = fvDedLst(more,MS.union(freeVarsDed(d),res))
and
   freeVarsExpLst([],res) = res
 | freeVarsExpLst(e::more,res) = freeVarsExpLst(more,MS.union(freeVarsExp(e),res))
and
   freeVarsDedLst(dlist) = fvDedLst(dlist,MS.empty_set)      
and
   freeVarsPhrase(exp(e)) = freeVarsExp(e)
 | freeVarsPhrase(ded(d)) = freeVarsDed(d)
and 
   fvPhraseLst([],res) = res
 | fvPhraseLst(p::more,res) = fvPhraseLst(more,MS.union(freeVarsPhrase(p),res))
and
   freeVarsPhraseLst(pl) = fvPhraseLst(pl,MS.empty_set)
and
   fvLetBindingLst([],[],set_list,_) = MS.unionLst(set_list)
 | fvLetBindingLst(nameset::more_namesets,def::more_defs,set_list,previous_ids) = 
       fvLetBindingLst(more_namesets,more_defs,MS.difference(freeVarsPhrase(def),previous_ids)::set_list,
                       MS.union(nameset,previous_ids))
 | fvLetBindingLst(_) = raise Basic.Never 
and
   freeVarsLetBindingLst(nameset_lst:ModSymbol.set list,defs) = fvLetBindingLst(nameset_lst,defs,[],MS.empty_set)
and
   fvLetRecBindingLst([]:binding list,res,id_set:ModSymbol.set) = res
 | fvLetRecBindingLst({bpat,def,...}::more,res,id_set:ModSymbol.set) = 
       fvLetRecBindingLst(more,MS.union(res,MS.difference(freeVarsPhrase(def),id_set)),id_set)
and
   freeVarsMatchClause({pat,exp=exp'}:match_clause) = 
        MS.union(msyms(valOfIds pat),MS.difference(freeVarsExp(exp'),msyms (patBindableIds pat)))
and
   fvMatchClauseLst([],res) = res 
 | fvMatchClauseLst(c::more,res) = fvMatchClauseLst(more,MS.union(freeVarsMatchClause(c),res))
and
   freeVarsMatchClauseLst(clist) = fvMatchClauseLst(clist,MS.empty_set) 
and 
   freeVarsDMatchClause({pat,ded=ded'}:dmatch_clause) = 
      MS.union(msyms (valOfIds pat),MS.difference(freeVarsDed(ded'),msyms (patBindableIds pat)))
and
   fvDMatchClauseLst([],res) = res 
 | fvDMatchClauseLst(c::more,res) = fvDMatchClauseLst(more,MS.union(freeVarsDMatchClause(c),res))
and 
   freeVarsDMatchClauseLst(clist) = fvDMatchClauseLst(clist,MS.empty_set)
and
   freeVarsCheckClause({test=elseCond,result}:check_clause) = freeVarsExp(result)
 | freeVarsCheckClause({test=boolCond(p),result}) = MS.union(freeVarsPhrase(p),freeVarsExp(result))
and
   fvCheckClauseLst([],res) = res
 | fvCheckClauseLst(c::more,res) = fvCheckClauseLst(more,MS.union(freeVarsCheckClause(c),res))
and
   freeVarsCheckClauseLst(clist) = fvCheckClauseLst(clist,MS.empty_set)
and
   freeVarsDCheckClause({test=elseCond,result}:dcheck_clause) = freeVarsDed(result)
 | freeVarsDCheckClause({test=boolCond(p),result}) = MS.union(freeVarsPhrase(p),freeVarsDed(result))
and
   fvDCheckClauseLst([],res) = res
 | fvDCheckClauseLst(c::more,res) = fvDCheckClauseLst(more,MS.union(freeVarsDCheckClause(c),res))
and
   freeVarsDCheckClauseLst(clist) = fvDCheckClauseLst(clist,MS.empty_set)

fun freeVarsExpAsList(e) = map MS.nameAsSymbol (MS.listModSymbols(freeVarsExp(e)))

fun replaceIdInExp(x,e as idExp({msym,...}),e') = if MS.modSymEq(mSym x,msym) then e' else e
  | replaceIdInExp(_, e as taggedConSym({name,...}),_) = e 
  | replaceIdInExp(x,opExp({op_exp,pos}),e') = opExp({op_exp=replaceIdInExp(x,op_exp,e'),pos=pos})

  | replaceIdInExp(x,e as numExp({number,...}),e') = if S.symEq(S.symbol(athNumberToString(number)),x) then e' else e
  | replaceIdInExp(x,logicalAndExp({args,pos}),e') = logicalAndExp({args=map (fn p => replaceIdInPhrase(x,p,e')) args,pos=pos})
  | replaceIdInExp(x,logicalOrExp({args,pos}),e') = logicalOrExp({args=map (fn p => replaceIdInPhrase(x,p,e')) args,pos=pos})

  | replaceIdInExp(x,whileExp({test,body,pos}),e') = whileExp({test=replaceIdInPhrase(x,test,e'),body=replaceIdInPhrase(x,body,e'),pos=pos})

  | replaceIdInExp(x,beginExp({members,pos}),e') = beginExp({members=map (fn p => replaceIdInPhrase(x,p,e')) members,pos=pos})

  | replaceIdInExp(x,tryExp({choices,pos}),e') = tryExp({choices=map (fn e => replaceIdInExp(x,e,e')) choices,pos=pos})

  | replaceIdInExp(x,cellExp({contents,pos}),e') = cellExp({contents=replaceIdInPhrase(x,contents,e'),pos=pos})

  | replaceIdInExp(x,refExp({cell_exp,pos}),e') = refExp({cell_exp= replaceIdInExp(x,cell_exp,e'),pos=pos})

  | replaceIdInExp(x,setCellExp({cell_exp,set_phrase,pos}),e') = 
         setCellExp({cell_exp=replaceIdInExp(x,cell_exp,e'),set_phrase=replaceIdInPhrase(x,set_phrase,e'),pos=pos})

  | replaceIdInExp(x,vectorInitExp({length_exp,init_val,pos}),e') = 
          vectorInitExp({length_exp=replaceIdInExp(x,length_exp,e'),init_val=replaceIdInPhrase(x,init_val,e'),pos=pos})

  | replaceIdInExp(x,vectorSetExp({vector_exp,index_exp,new_val,pos}),e') = 
       vectorSetExp({vector_exp= replaceIdInExp(x,vector_exp,e'),
                     index_exp= replaceIdInExp(x,index_exp,e'),
                     new_val= replaceIdInPhrase(x,new_val,e'),pos=pos})
  

  | replaceIdInExp(x,checkExp({clauses,pos}),e') = checkExp({clauses=map (fn cc => replaceIdInCheckClause(x,cc,e')) clauses,pos=pos})

  | replaceIdInExp(x,e as functionExp({params,body,pos}),e') = 
       if S.isMember(x,S.symListToSet(getPWParamNames(params))) then e 
       else functionExp({params=params,body=replaceIdInExp(x,body,e'),pos=pos})
                                                              
  | replaceIdInExp(x,e as methodExp({params,body,pos,name}),e') = 
       if S.isMember(x,S.symListToSet(getPWParamNames(params))) then e 
       else methodExp({params=params,body=replaceIdInDed(x,body,e'),name=name,pos=pos})

  | replaceIdInExp(x,appExp({proc,args,pos,alt_exp=ref NONE}),e') = 
        appExp({proc=replaceIdInPhrase(x,proc,e'),args=map  (fn p => replaceIdInPhrase(x,p,e')) args,pos=pos,alt_exp=ref NONE})
                
  | replaceIdInExp(x,appExp({proc,args,pos,alt_exp=ref(SOME ae)}),e') = 
        appExp({proc=replaceIdInPhrase(x,proc,e'),args=map  (fn p => replaceIdInPhrase(x,p,e')) args,
                pos=pos,alt_exp=ref(SOME (replaceIdInExp(x,ae,e')))})

  | replaceIdInExp(x,UAppExp({proc,arg,pos}),e') = 
        UAppExp({proc=replaceIdInPhrase(x,proc,e'),arg=replaceIdInPhrase(x,arg,e'),pos=pos})
  | replaceIdInExp(x,BAppExp({proc,arg1,arg2,pos}),e') = 
        BAppExp({proc=replaceIdInPhrase(x,proc,e'),arg1=replaceIdInPhrase(x,arg1,e'),arg2=replaceIdInPhrase(x,arg2,e'),pos=pos})

 
  | replaceIdInExp(x,listExp({members,pos}),e') = listExp({members=map (fn p => replaceIdInPhrase(x,p,e')) members,pos=pos})
 
 | replaceIdInExp(x,matchExp({discriminant,clauses,pos}),e') = 
      matchExp({discriminant=replaceIdInPhrase(x,discriminant,e'),
                clauses=map (fn mc => replaceIdInMatchClause(x,mc,e')) clauses,pos=pos})

  | replaceIdInExp(x,letExp({bindings,body,pos}),e') = 
        let val (bindings',pat_ids) = replaceIdInLetBindings(x,bindings,e')
        in
           if Basic.isMemberEq(x,pat_ids,S.symEq) then 
                 letExp({bindings=bindings',body=body,pos=pos})
           else  letExp({bindings=bindings',body=replaceIdInExp(x,body,e'),pos=pos})
        end
  | replaceIdInExp(x,e as letRecExp({bindings,body,pos}),e') = 
        let val name_set = Symbol.unionLst(map (fn b:binding as {bpat,...} => patBindableIds(bpat)) bindings)
        in
           if S.isMember(x,name_set) then e
           else 
                let val bindings' = map (fn {bpat,def,pos}:binding => {bpat=bpat,def=replaceIdInPhrase(x,def,e'),pos=pos}) bindings
                in
                   letRecExp({bindings=bindings',body=replaceIdInExp(x,body,e'),pos=pos})
                end
        end
 | replaceIdInExp(x,e,e') = e
and
   replaceIdInLetBindings(x,bindings,e') =
     let fun f([],previous_ids,results) = (rev results,S.listSymbols previous_ids)
           | f(bindings as {bpat,def,pos}::rest,previous_ids,results) = 
                 let val previous_ids' = S.union(patBindableIds bpat,previous_ids)
                 in 
                    if S.isMember(x,previous_ids') then 
                      ((rev results)@bindings,S.listSymbols previous_ids')
                    else f(rest,previous_ids',{bpat=bpat,pos=pos,def=replaceIdInPhrase(x,def,e')}::results)
                 end
     in
       f(bindings,S.empty_set,[])
     end
and 
   replaceIdInDed(x,assumeDed({assumption,body,pos}),e') = 
      assumeDed({assumption=replaceIdInPhrase(x,assumption,e'),body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,infixAssumeDed({bindings,body,pos}),e') = 
       let val (bindings',pat_ids) = replaceIdInLetBindings(x,bindings,e')
       in 
          if Basic.isMemberEq(x,pat_ids,S.symEq) then  
             infixAssumeDed({bindings=bindings',body=body,pos=pos})
          else infixAssumeDed({bindings=bindings',body=replaceIdInDed(x,body,e'),pos=pos})
       end
 | replaceIdInDed(x,byCasesDed({disj,from_exps=NONE,arms,pos}),e') = 
      byCasesDed({disj= replaceIdInPhrase(x,disj,e'),
                  from_exps=NONE,arms=map (fn cc => replaceIdInCaseClause(x,cc,e')) arms,pos=pos})
 | replaceIdInDed(x,byCasesDed({disj,from_exps=SOME exps,arms,pos}),e') = 
      byCasesDed({disj= replaceIdInPhrase(x,disj,e'),from_exps=SOME(map (fn e => replaceIdInExp(x,e,e')) exps),
                  arms=map (fn cc => replaceIdInCaseClause(x,cc,e')) arms,pos=pos})
 | replaceIdInDed(x,assumeLetDed({bindings,body,pos}),e') = 
       let val (bindings',pat_ids) = replaceIdInLetBindings(x,bindings,e')
       in 
          if Basic.isMemberEq(x,pat_ids,S.symEq) then  
             assumeLetDed({bindings=bindings',body=body,pos=pos})
          else assumeLetDed({bindings=bindings',body=replaceIdInDed(x,body,e'),pos=pos})
       end
  | replaceIdInDed(x,absurdDed({hyp,body,pos}),e') = 
      absurdDed({hyp=replaceIdInPhrase(x,hyp,e'),body=replaceIdInDed(x,body,e'),pos=pos})
  | replaceIdInDed(x,absurdLetDed({named_hyp,body,pos}),e') = 
       let val (binding::_,pat_ids) = replaceIdInLetBindings(x,[named_hyp],e')
       in 
          if Basic.isMemberEq(x,pat_ids,S.symEq) then  
             absurdLetDed({named_hyp=binding,body=body,pos=pos})
          else absurdLetDed({named_hyp=binding,body=replaceIdInDed(x,body,e'),pos=pos})
       end
  | replaceIdInDed(x,methodAppDed({method,args,pos}),e') = 
          methodAppDed({method= replaceIdInExp(x,method,e'),args=map (fn p => replaceIdInPhrase(x,p,e')) args,pos=pos})

  | replaceIdInDed(x,BMethAppDed({method,arg1,arg2,pos}),e') = 
        BMethAppDed({method=replaceIdInExp(x,method,e'),arg1=replaceIdInPhrase(x,arg1,e'),arg2=replaceIdInPhrase(x,arg2,e'),pos=pos})


  | replaceIdInDed(x,UMethAppDed({method,arg,pos}),e') = 
        UMethAppDed({method=replaceIdInExp(x,method,e'),arg=replaceIdInPhrase(x,arg,e'),pos=pos})

 | replaceIdInDed(x,matchDed({discriminant,clauses,pos}),e') = 
      matchDed({discriminant=replaceIdInPhrase(x,discriminant,e'),
                clauses=map (fn mc => replaceIdInDMatchClause(x,mc,e')) clauses,pos=pos})
 | replaceIdInDed(x,inductionDed({prop,clauses,pos}),e') = 
      inductionDed({prop=replaceIdInPhrase(x,prop,e'),clauses=map (fn mc => replaceIdInDMatchClause(x,mc,e')) clauses,pos=pos})
 | replaceIdInDed(x,structureCasesDed({prop,clauses,term=NONE,pos}),e') = 
      structureCasesDed({prop=replaceIdInPhrase(x,prop,e'),term=NONE,clauses=map (fn mc => replaceIdInDMatchClause(x,mc,e')) clauses,pos=pos})
 | replaceIdInDed(x,structureCasesDed({prop,clauses,term=SOME(dt_exp),pos}),e') = 
      structureCasesDed({prop=replaceIdInPhrase(x,prop,e'),term=SOME(replaceIdInExp(x,dt_exp,e')),
                         clauses=map (fn mc => replaceIdInDMatchClause(x,mc,e')) clauses,pos=pos})
 | replaceIdInDed(x,tryDed({choices,pos}),e') = tryDed({choices=map (fn d => replaceIdInDed(x,d,e')) choices,pos=pos})
 | replaceIdInDed(x,letDed({bindings,body,pos}),e') = 
        let val (bindings',pat_ids) = replaceIdInLetBindings(x,bindings,e')
        in
           if Basic.isMemberEq(x,pat_ids,S.symEq) then 
                 letDed({bindings=bindings',body=body,pos=pos})
           else  letDed({bindings=bindings',body=replaceIdInDed(x,body,e'),pos=pos})
        end
 | replaceIdInDed(x,d as letRecDed({bindings,body,pos}),e') = 
       let val name_set = Symbol.unionLst(map (fn b:binding as {bpat,...} => patBindableIds(bpat)) bindings)
       in
          if S.isMember(x,name_set) then d
          else 
               let val bindings' = map (fn {bpat,def,pos}:binding => {bpat=bpat,def=replaceIdInPhrase(x,def,e'),pos=pos}) bindings
                in
                   letRecDed({bindings=bindings',body=replaceIdInDed(x,body,e'),pos=pos})
                end
        end
 | replaceIdInDed(x,beginDed({members,pos}),e') = 
      beginDed({members=map (fn d => replaceIdInDed(x,d,e')) members,pos=pos})
 | replaceIdInDed(x,checkDed({clauses,pos}),e') = 
    checkDed({clauses=map (fn cc => replaceIdInDCheckClause(x,cc,e')) clauses,pos=pos})
 | replaceIdInDed(x,byDed({wanted_res,conc_name,body,pos}),e') = 
       byDed({wanted_res=replaceIdInExp(x,wanted_res,e'),conc_name=conc_name,body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,fromDed({conclusion,premises,pos}),e') = 
       fromDed({conclusion=replaceIdInExp(x,conclusion,e'),premises=replaceIdInExp(x,premises,e'),pos=pos})
 | replaceIdInDed(x,genOverDed({eigenvar_exp,body,pos}),e') = 
       genOverDed({eigenvar_exp=replaceIdInExp(x,eigenvar_exp,e'),body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,d as pickAnyDed({eigenvars,body,pos}),e') = 
       if Basic.isMemberEq(x,map #name eigenvars,S.symEq) then d
       else pickAnyDed({eigenvars=eigenvars,body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,withWitnessDed({eigenvar_exp,ex_gen,body,pos}),e') = 
       withWitnessDed({eigenvar_exp=replaceIdInExp(x,eigenvar_exp,e'),
                       ex_gen=replaceIdInPhrase(x,ex_gen,e'),body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,pickWitnessDed({ex_gen,var_id,inst_id=NONE,body,pos}),e') = 
     if S.symEq(var_id,x) then 
        pickWitnessDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_id=var_id,inst_id=NONE,body=body,pos=pos})
     else pickWitnessDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_id=var_id,inst_id=NONE,body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,pickWitnessDed({ex_gen,var_id,inst_id=SOME ii,body,pos}),e') = 
     if S.symEq(var_id,x) orelse S.symEq(x,ii) then 
        pickWitnessDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_id=var_id,inst_id=SOME ii,body=body,pos=pos})
     else pickWitnessDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_id=var_id,inst_id=SOME ii,body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,pickWitnessesDed({ex_gen,var_ids,inst_id=NONE,body,pos}),e') = 
     if Basic.isMemberEq(x,var_ids,S.symEq) then 
        pickWitnessesDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_ids=var_ids,inst_id=NONE,body=body,pos=pos})
     else pickWitnessesDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_ids=var_ids,inst_id=NONE,body=replaceIdInDed(x,body,e'),pos=pos})
 | replaceIdInDed(x,pickWitnessesDed({ex_gen,var_ids,inst_id=SOME ii,body,pos}),e') = 
     if Basic.isMemberEq(x,var_ids,S.symEq) orelse S.symEq(x,ii) then 
        pickWitnessesDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_ids=var_ids,inst_id=NONE,body=body,pos=pos})
     else pickWitnessesDed({ex_gen=replaceIdInPhrase(x,ex_gen,e'),var_ids=var_ids,inst_id=NONE,body=replaceIdInDed(x,body,e'),pos=pos})
and
   replaceIdInPhrase(x,exp(e),e') = exp(replaceIdInExp(x,e,e'))  
|  replaceIdInPhrase(x,ded(d),e') = ded(replaceIdInDed(x,d,e'))
and 
   replaceIdInCaseClause(x,{case_name,alt,proof},e') = 
       {case_name=case_name,alt=replaceIdInExp(x,alt,e'),proof=replaceIdInDed(x,proof,e')}
and
   replaceIdInCheckClause(x,{test=elseCond,result},e') = {test=elseCond,result=replaceIdInExp(x,result,e')}
 | replaceIdInCheckClause(x,{test=boolCond(p),result},e') = {test=boolCond(replaceIdInPhrase(x,p,e')),result=replaceIdInExp(x,result,e')}
and
   replaceIdInDCheckClause(x,{test=elseCond,result},e') = {test=elseCond,result=replaceIdInDed(x,result,e')}
 | replaceIdInDCheckClause(x,{test=boolCond(p),result},e') = {test=boolCond(replaceIdInPhrase(x,p,e')),result=replaceIdInDed(x,result,e')}
and
   replaceIdInMatchClause(x,mc as {pat,exp=e},e') = if S.isMember(x,patBindableIds(pat)) then mc 
                                                    else {pat=pat,exp=replaceIdInExp(x,e,e')}
and
   replaceIdInDMatchClause(x,mc as {pat,ded=d},e') = if S.isMember(x,patBindableIds(pat)) then mc 
                                                     else {pat=pat,ded=replaceIdInDed(x,d,e')}

fun replaceIdInExpLst(ids,e:expression,exps') = 
        let fun loop([],_,res) = res
              | loop(x::more_ids,e'::more_exps',res) = loop(more_ids,more_exps',replaceIdInExp(x,res,e'))
        in
            loop(ids,exps',e)
        end
and
   replaceIdInDedLst(ids,d:deduction,exps') = 
        let fun loop([],_,res) = res
              | loop(x::more_ids,e'::more_exps',res) = loop(more_ids,more_exps',replaceIdInDed(x,res,e'))
        in
            loop(ids,exps',d)
        end
and
  replaceIdInPhraseLst(ids,exp e,exps') = exp(replaceIdInExpLst(ids,e,exps'))
| replaceIdInPhraseLst(ids,ded d,exps') = ded(replaceIdInDedLst(ids,d,exps'))

fun applyExpFunRecursively(f,p) = 
  let fun recurseOnExp(e as opExp({op_exp=e',pos})) = 
              f(opExp({op_exp=recurseOnExp e',pos=pos}))
        | recurseOnExp(e as whileExp({test,body,pos})) = 
              f(whileExp({test=recurseOnPhrase test,body=recurseOnPhrase body,pos=pos}))
        | recurseOnExp(beginExp({members,pos})) = 
              f(beginExp({members=map recurseOnPhrase members,pos=pos}))
        | recurseOnExp(logicalAndExp({args,pos})) = 
              f(logicalAndExp({args=map recurseOnPhrase args,pos=pos}))
        | recurseOnExp(logicalOrExp({args,pos})) = 
              f(logicalOrExp({args=map recurseOnPhrase args,pos=pos}))
        | recurseOnExp(e as functionExp({body=b,params,pos})) = 
              f(functionExp({body=recurseOnExp b,params=params,pos=pos}))

        | recurseOnExp(e as appExp({proc,args,pos,alt_exp=ref(NONE)})) = 
              f(appExp({proc=recurseOnPhrase proc,args=map recurseOnPhrase args,
 	                alt_exp=ref(NONE),pos=pos}))

        | recurseOnExp(e as appExp({proc,args,pos,alt_exp=ref(SOME(e'))})) = 
              f(appExp({proc=recurseOnPhrase proc,args=map recurseOnPhrase args,
 	                alt_exp=ref(SOME (recurseOnExp e')),pos=pos}))


        | recurseOnExp(e as UAppExp({proc,arg,pos})) = 
              f(UAppExp({proc=recurseOnPhrase proc,arg=recurseOnPhrase arg,pos=pos}))
        | recurseOnExp(e as BAppExp({proc,arg1,arg2,pos})) = 
              f(BAppExp({proc=recurseOnPhrase proc,arg1=recurseOnPhrase arg1,arg2=recurseOnPhrase arg2,pos=pos}))

        | recurseOnExp(listExp({members,pos,...})) = f(listExp({members=map recurseOnPhrase members,pos=pos}))
        | recurseOnExp(checkExp({clauses,pos})) = f(checkExp({clauses=map recurseOnCheckClause clauses,pos=pos}))
        | recurseOnExp(methodExp({params,body,pos,name})) = 
              f(methodExp({params=params,pos=pos,name=name,body=recurseOnDed(body)}))
        | recurseOnExp(matchExp({discriminant,clauses,pos})) = 
              f(matchExp({discriminant=recurseOnPhrase(discriminant),pos=pos,clauses=map recurseOnMatchClause clauses}))
        | recurseOnExp(tryExp({choices,pos,...})) = f(tryExp({choices=map recurseOnExp choices,pos=pos}))
        | recurseOnExp(letExp({bindings,body,pos})) = f(letExp({bindings=map recurseOnBinding bindings,body=recurseOnExp body,pos=pos}))
        | recurseOnExp(letRecExp({bindings,body,pos})) = f(letRecExp({bindings=map recurseOnBinding bindings,body=recurseOnExp body,pos=pos}))
        | recurseOnExp(cellExp({contents,pos})) = f(cellExp({contents=recurseOnPhrase contents,pos=pos}))
        | recurseOnExp(refExp({cell_exp,pos})) = f(refExp({cell_exp=recurseOnExp cell_exp,pos=pos}))
        | recurseOnExp(setCellExp({cell_exp,set_phrase,pos})) = 
             f(setCellExp({cell_exp=recurseOnExp cell_exp,set_phrase=recurseOnPhrase set_phrase,pos=pos}))
        | recurseOnExp(vectorInitExp({length_exp,init_val,pos})) = 
              f(vectorInitExp({length_exp=recurseOnExp length_exp,init_val=recurseOnPhrase init_val,pos=pos}))
        | recurseOnExp(vectorSetExp({vector_exp,index_exp,new_val,pos})) = 
              f(vectorSetExp({vector_exp=recurseOnExp vector_exp,index_exp=recurseOnExp index_exp,new_val=recurseOnPhrase new_val,pos=pos}))
        | recurseOnExp(vectorSubExp({vector_exp,index_exp,pos})) = 
              f(vectorSubExp({vector_exp=recurseOnExp vector_exp,index_exp = recurseOnExp index_exp,pos=pos}))
        | recurseOnExp(e) = f(e)
      and 
          recurseOnDed(assumeDed({assumption,body,pos})) = 
           assumeDed({assumption=recurseOnPhrase assumption,body=recurseOnDed body,pos=pos})
        | recurseOnDed(assumeLetDed({bindings,body,pos})) = 
            assumeLetDed({bindings=map recurseOnBinding bindings,body=recurseOnDed body,pos=pos})
        | recurseOnDed(infixAssumeDed({bindings,body,pos})) = 
             infixAssumeDed({bindings=map recurseOnBinding bindings,body=recurseOnDed body,pos=pos})
        | recurseOnDed(absurdDed({hyp,body,pos})) = absurdDed({hyp=recurseOnPhrase hyp,body=recurseOnDed body,pos=pos})
        | recurseOnDed(absurdLetDed({named_hyp,body,pos})) = 
             absurdLetDed({named_hyp=recurseOnBinding named_hyp,body=recurseOnDed body,pos=pos})
        | recurseOnDed(methodAppDed({method,args,pos})) = 
             methodAppDed({method=recurseOnExp method,args= map recurseOnPhrase args,pos=pos})

        | recurseOnDed(e as BMethAppDed({method,arg1,arg2,pos})) = 
              BMethAppDed({method=recurseOnExp method,arg1=recurseOnPhrase arg1,arg2=recurseOnPhrase arg2,pos=pos})

        | recurseOnDed(e as UMethAppDed({method,arg,pos})) = 
              UMethAppDed({method=recurseOnExp method,arg=recurseOnPhrase arg,pos=pos})


        | recurseOnDed(matchDed({discriminant,clauses,pos})) = 
             matchDed({discriminant= recurseOnPhrase discriminant,clauses=map recurseOnDMatchClause clauses,pos=pos})
        | recurseOnDed(inductionDed({prop,clauses,pos})) = 
             inductionDed({prop= recurseOnPhrase prop,clauses = map recurseOnDMatchClause clauses,pos=pos})
        | recurseOnDed(structureCasesDed({prop,term=NONE,clauses,pos})) = 
             structureCasesDed({prop= recurseOnPhrase prop,term=NONE,clauses = map recurseOnDMatchClause clauses,pos=pos})

        | recurseOnDed(structureCasesDed({prop,term=SOME(dt_exp),clauses,pos})) = 
             structureCasesDed({prop= recurseOnPhrase prop,term=SOME(recurseOnExp(dt_exp)),
                                clauses = map recurseOnDMatchClause clauses,pos=pos})


        | recurseOnDed(tryDed({choices,pos})) = tryDed({choices=map recurseOnDed choices,pos=pos})
        | recurseOnDed(letDed({bindings,body,pos})) = letDed({bindings=map recurseOnBinding bindings,body= recurseOnDed body,pos=pos})
        | recurseOnDed(letRecDed({bindings,body,pos})) = letRecDed({bindings=map recurseOnBinding bindings,body= recurseOnDed body,pos=pos})
        | recurseOnDed(beginDed({members,pos})) = beginDed({members=map recurseOnDed members,pos=pos})
        | recurseOnDed(checkDed({clauses,pos})) = checkDed({clauses=map recurseOnDCheckClause clauses,pos=pos})
        | recurseOnDed(byCasesDed({disj,from_exps=NONE,arms,pos})) = 
             byCasesDed({disj=recurseOnPhrase disj,from_exps=NONE,arms=map recurseOnCaseClause arms,pos=pos})
        | recurseOnDed(byDed({wanted_res,conc_name=NONE,body,pos})) = 
                byDed({wanted_res=recurseOnExp wanted_res,conc_name=NONE,body=recurseOnDed body,pos=pos})
        | recurseOnDed(byDed({wanted_res,conc_name=SOME p,body,pos})) = 
                byDed({wanted_res=recurseOnExp wanted_res,conc_name=SOME p,body=recurseOnDed body,pos=pos})
        | recurseOnDed(fromDed({conclusion,premises,pos})) = 
                fromDed({conclusion=recurseOnExp conclusion,premises=recurseOnExp premises,pos=pos})
        | recurseOnDed(byCasesDed({disj,from_exps=SOME(exps),arms,pos})) = 
             byCasesDed({disj=recurseOnPhrase disj,from_exps=SOME(map recurseOnExp exps),arms=map recurseOnCaseClause arms,pos=pos})
        | recurseOnDed(genOverDed({eigenvar_exp,body,pos})) = 
             genOverDed({eigenvar_exp=recurseOnExp eigenvar_exp,body=recurseOnDed body,pos=pos})
        | recurseOnDed(pickAnyDed({eigenvars,body,pos})) = pickAnyDed({eigenvars=eigenvars,body=recurseOnDed body,pos=pos})
        | recurseOnDed(withWitnessDed({eigenvar_exp,ex_gen,body,pos})) = 
             withWitnessDed({eigenvar_exp=recurseOnExp eigenvar_exp,ex_gen= recurseOnPhrase ex_gen,body= recurseOnDed body,pos=pos})
        | recurseOnDed(pickWitnessDed({ex_gen,var_id,inst_id,body,pos})) = 
             pickWitnessDed({ex_gen=recurseOnPhrase ex_gen,var_id=var_id,inst_id=inst_id,body=recurseOnDed body,pos=pos})
        | recurseOnDed(pickWitnessesDed({ex_gen,var_ids,inst_id,body,pos})) = 
             pickWitnessesDed({ex_gen=recurseOnPhrase ex_gen,var_ids=var_ids,inst_id=inst_id,body=recurseOnDed body,pos=pos})                
      and recurseOnCaseClause({case_name=NONE,alt,proof}) = {case_name=NONE,alt=recurseOnExp alt,proof=recurseOnDed proof}
        | recurseOnCaseClause({case_name=SOME p,alt,proof}) = {case_name=SOME p,alt=recurseOnExp alt,proof=recurseOnDed proof}
      and recurseOnCheckClause({test=elseCond,result}) = {test=elseCond,result=recurseOnExp result}
        | recurseOnCheckClause({test=boolCond p,result}) = {test=boolCond (recurseOnPhrase p),result=recurseOnExp result}
      and recurseOnDCheckClause({test=elseCond,result}) = {test=elseCond,result=recurseOnDed result}
        | recurseOnDCheckClause({test=boolCond p,result}) = {test=boolCond (recurseOnPhrase p),result=recurseOnDed result}
      and recurseOnMatchClause({pat=p,exp=e}) = {pat=p,exp=recurseOnExp e}
      and recurseOnDMatchClause({pat=p,ded=d}:dmatch_clause) = {pat=p,ded=recurseOnDed d}
      and recurseOnBinding({bpat,def,pos}) = {bpat=bpat,def=recurseOnPhrase def,pos=pos}
      and recurseOnPhrase(exp(e)) = exp(recurseOnExp(e))
        | recurseOnPhrase(ded(d)) = ded(recurseOnDed(d))
      and recurseOnPat(wherePat({pat,guard,pos})) = wherePat({pat=recurseOnPat(pat),guard=(recurseOnExp(guard)),pos=pos})
        | recurseOnPat(listPats({member_pats,pos})) = listPats({member_pats=(map recurseOnPat member_pats),pos=pos})    
        | recurseOnPat(listPat({head_pat,tail_pat,pos})) = listPat({head_pat=recurseOnPat(head_pat),tail_pat=recurseOnPat(tail_pat),pos=pos})
        | recurseOnPat(cellPat({pat,pos})) = cellPat({pat=recurseOnPat(pat),pos=pos})
        | recurseOnPat(splitPat({pats,pos,re_form,code})) = splitPat({pats=(map recurseOnPat pats),pos=pos,re_form=re_form,code=code})
        | recurseOnPat(reStarPat({pat,pos,re_form,code})) = reStarPat({pat=recurseOnPat(pat),pos=pos,re_form=re_form,code=code})
        | recurseOnPat(rePlusPat({pat,pos,re_form,code})) = rePlusPat({pat=recurseOnPat(pat),pos=pos,re_form=re_form,code=code})
        | recurseOnPat(reRangePat({from_pat,to_pat,lo,hi,pos})) = reRangePat({from_pat=recurseOnPat(from_pat),to_pat=recurseOnPat(to_pat),lo=lo,hi=hi,pos=pos})
        | recurseOnPat(reRepPat({pat,times,pos,re_form,code})) = reRepPat({pat=recurseOnPat(pat),times=times,pos=pos,re_form=re_form,code=code})
        | recurseOnPat(reLitPat({pat,pos})) = reLitPat({pat=recurseOnPat(pat),pos=pos})
        | recurseOnPat(reOptPat({pat,pos,re_form,code})) = reOptPat({pat=recurseOnPat(pat),pos=pos,re_form=re_form,code=code})
        | recurseOnPat(namedPat({name,pat,pos})) = namedPat({name=name,pat=recurseOnPat(pat),pos=pos})
        | recurseOnPat(compoundPat({head_pat,rest_pats,pos})) = compoundPat({head_pat=recurseOnPat(head_pat),rest_pats=(map recurseOnPat rest_pats),pos=pos})
        | recurseOnPat(disjPat({pats,pos})) = disjPat({pats=(map recurseOnPat pats),pos=pos})
        | recurseOnPat(p) = p 
  in 
     recurseOnPhrase(p) 
  end

fun makeCharConstraintRE(e:expression,p) = 
  let val id = Symbol.freshSymbol(NONE)
      val id_exp = idExp({msym=mSym(id),mods=[],no_mods=true,sym=id,pos=p})
      val ptp:possibly_typed_param = {name=id,pos=p,sort_as_sym_term=NONE,op_tag=NONE,sort_as_fterm=NONE,sort_as_exp=NONE}
      val app_exp = appExp({proc=exp(e),args=[exp(id_exp)],pos=p,alt_exp=ref(NONE)})
  in
     wherePat({pat=someCharPat({id=someParam(ptp),pos=p}),guard=app_exp,pos=p})
  end

fun applyPhraseFunRecursively(f:(phrase->phrase),p) = 
  let fun recurseOnExp(e as opExp({op_exp=e',pos})) = 
              f(exp(opExp({op_exp=getExp(recurseOnExp e'),pos=pos})))
        | recurseOnExp(e as whileExp({test,body,pos})) = 
              f(exp(whileExp({test=recurseOnPhrase test,body=recurseOnPhrase body,pos=pos})))
        | recurseOnExp(beginExp({members,pos})) = 
              f(exp(beginExp({members=map recurseOnPhrase members,pos=pos})))
        | recurseOnExp(logicalAndExp({args,pos})) = 
              f(exp(logicalAndExp({args=map recurseOnPhrase args,pos=pos})))
        | recurseOnExp(logicalOrExp({args,pos})) = 
              f(exp(logicalOrExp({args=map recurseOnPhrase args,pos=pos})))
        | recurseOnExp(e as functionExp({body=b,params,pos})) = 
              f(exp(functionExp({body=getExp(recurseOnExp b),params=params,pos=pos})))

        | recurseOnExp(e as appExp({proc,args,pos,alt_exp=ref(NONE)})) = 
              f(exp(appExp({proc=recurseOnPhrase proc,args=map recurseOnPhrase args,
 	                    alt_exp=ref(NONE),pos=pos})))
        | recurseOnExp(e as appExp({proc,args,pos,alt_exp=ref(SOME(e'))})) = 
              f(exp(appExp({proc=recurseOnPhrase proc,args=map recurseOnPhrase args,
 	                    alt_exp=ref(SOME(erecurseOnExp(e'))),pos=pos})))

        | recurseOnExp(e as UAppExp({proc,arg,pos})) = 
              f(exp(UAppExp({proc=recurseOnPhrase proc,arg=recurseOnPhrase arg,pos=pos})))
        | recurseOnExp(e as BAppExp({proc,arg1,arg2,pos})) = 
              f(exp(BAppExp({proc=recurseOnPhrase proc,arg1=recurseOnPhrase arg1,arg2=recurseOnPhrase arg2,pos=pos})))
 
        | recurseOnExp(listExp({members,pos,...})) = f(exp(listExp({members=map recurseOnPhrase members,pos=pos})))
        | recurseOnExp(checkExp({clauses,pos})) = f(exp(checkExp({clauses=map recurseOnCheckClause clauses,pos=pos})))
        | recurseOnExp(methodExp({params,body,pos,name})) = 
              f(exp(methodExp({params=params,pos=pos,name=name,body=drecurseOnDed(body)})))
        | recurseOnExp(matchExp({discriminant,clauses,pos})) = 
              f(exp(matchExp({discriminant=recurseOnPhrase(discriminant),pos=pos,clauses=map recurseOnMatchClause clauses})))
        | recurseOnExp(tryExp({choices,pos,...})) = f(exp(tryExp({choices=map (fn p => getExp(recurseOnExp p)) choices,pos=pos})))
        | recurseOnExp(letExp({bindings,body,pos})) = f(exp(letExp({bindings=map recurseOnBinding bindings,body=getExp(recurseOnExp body),pos=pos})))
        | recurseOnExp(letRecExp({bindings,body,pos})) = f(exp(letRecExp({bindings=map recurseOnBinding bindings,body=getExp(recurseOnExp body),pos=pos})))
        | recurseOnExp(cellExp({contents,pos})) = f(exp(cellExp({contents=recurseOnPhrase contents,pos=pos})))
        | recurseOnExp(refExp({cell_exp,pos})) = f(exp(refExp({cell_exp=getExp(recurseOnExp cell_exp),pos=pos})))
        | recurseOnExp(setCellExp({cell_exp,set_phrase,pos})) = 
             f(exp(setCellExp({cell_exp=getExp(recurseOnExp cell_exp),set_phrase=recurseOnPhrase set_phrase,pos=pos})))
        | recurseOnExp(vectorInitExp({length_exp,init_val,pos})) = 
              f(exp(vectorInitExp({length_exp=erecurseOnExp length_exp,init_val=recurseOnPhrase init_val,pos=pos})))
        | recurseOnExp(vectorSetExp({vector_exp,index_exp,new_val,pos})) = 
              f(exp(vectorSetExp({vector_exp=erecurseOnExp vector_exp,index_exp=erecurseOnExp index_exp,new_val=recurseOnPhrase new_val,pos=pos})))
        | recurseOnExp(vectorSubExp({vector_exp,index_exp,pos})) = 
              f(exp(vectorSubExp({vector_exp=erecurseOnExp vector_exp,index_exp = erecurseOnExp index_exp,pos=pos})))     
        | recurseOnExp(e) = f(exp(e))
      and 
          recurseOnDed(assumeDed({assumption,body,pos})) = 
           f(ded(assumeDed({assumption=recurseOnPhrase assumption,body=drecurseOnDed body,pos=pos})))
        | recurseOnDed(assumeLetDed({bindings,body,pos})) = 
            g(assumeLetDed({bindings=map recurseOnBinding bindings,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(infixAssumeDed({bindings,body,pos})) = 
             g(infixAssumeDed({bindings=map recurseOnBinding bindings,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(absurdDed({hyp,body,pos})) = g(absurdDed({hyp=recurseOnPhrase hyp,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(absurdLetDed({named_hyp,body,pos})) = 
             g(absurdLetDed({named_hyp=recurseOnBinding named_hyp,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(methodAppDed({method,args,pos})) = 
             g(methodAppDed({method=erecurseOnExp method,args= map recurseOnPhrase args,pos=pos}))

        | recurseOnDed(e as BMethAppDed({method,arg1,arg2,pos})) = 
              g(BMethAppDed({method=erecurseOnExp method,arg1=recurseOnPhrase arg1,arg2=recurseOnPhrase arg2,pos=pos}))

        | recurseOnDed(e as UMethAppDed({method,arg,pos})) = 
              g(UMethAppDed({method=erecurseOnExp method,arg=recurseOnPhrase arg,pos=pos}))
        | recurseOnDed(matchDed({discriminant,clauses,pos})) = 
             g(matchDed({discriminant= recurseOnPhrase discriminant,clauses=map recurseOnDMatchClause clauses,pos=pos}))
        | recurseOnDed(inductionDed({prop,clauses,pos})) = 
             g(inductionDed({prop= recurseOnPhrase prop,clauses = map recurseOnDMatchClause clauses,pos=pos}))

        | recurseOnDed(structureCasesDed({prop,term=NONE,clauses,pos})) = 
             g(structureCasesDed({prop= recurseOnPhrase prop,term=NONE,clauses = map recurseOnDMatchClause clauses,pos=pos}))
        | recurseOnDed(structureCasesDed({prop,term=SOME(dt_exp),clauses,pos})) = 
             g(structureCasesDed({prop=recurseOnPhrase prop,term=SOME(erecurseOnExp(dt_exp)),
                                  clauses = map recurseOnDMatchClause clauses,pos=pos}))


        | recurseOnDed(tryDed({choices,pos})) = g(tryDed({choices=map drecurseOnDed choices,pos=pos}))
        | recurseOnDed(letDed({bindings,body,pos})) = g(letDed({bindings=map recurseOnBinding bindings,body= drecurseOnDed body,pos=pos}))
        | recurseOnDed(letRecDed({bindings,body,pos})) = g(letRecDed({bindings=map recurseOnBinding bindings,body= drecurseOnDed body,pos=pos}))
        | recurseOnDed(beginDed({members,pos})) = g(beginDed({members=map drecurseOnDed members,pos=pos}))
        | recurseOnDed(checkDed({clauses,pos})) = g(checkDed({clauses=map recurseOnDCheckClause clauses,pos=pos}))
        | recurseOnDed(byCasesDed({disj,from_exps=NONE,arms,pos})) = 
             g(byCasesDed({disj=recurseOnPhrase disj,from_exps=NONE,arms=map recurseOnCaseClause arms,pos=pos}))
        | recurseOnDed(byDed({wanted_res,conc_name=NONE,body,pos})) = 
                g(byDed({wanted_res=erecurseOnExp wanted_res,conc_name=NONE,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(byDed({wanted_res,conc_name=SOME p,body,pos})) = 
                g(byDed({wanted_res=erecurseOnExp wanted_res,conc_name=SOME p,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(fromDed({conclusion,premises,pos})) = 
                g(fromDed({conclusion=erecurseOnExp conclusion,premises=erecurseOnExp premises,pos=pos}))
        | recurseOnDed(byCasesDed({disj,from_exps=SOME(exps),arms,pos})) = 
             g(byCasesDed({disj=recurseOnPhrase disj,from_exps=SOME(map erecurseOnExp exps),arms=map recurseOnCaseClause arms,pos=pos}))
        | recurseOnDed(genOverDed({eigenvar_exp,body,pos})) = 
             g(genOverDed({eigenvar_exp=erecurseOnExp eigenvar_exp,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(pickAnyDed({eigenvars,body,pos})) = g(pickAnyDed({eigenvars=eigenvars,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(withWitnessDed({eigenvar_exp,ex_gen,body,pos})) = 
             g(withWitnessDed({eigenvar_exp=erecurseOnExp eigenvar_exp,ex_gen= recurseOnPhrase ex_gen,body= drecurseOnDed body,pos=pos}))
        | recurseOnDed(pickWitnessDed({ex_gen,var_id,inst_id,body,pos})) = 
             g(pickWitnessDed({ex_gen=recurseOnPhrase ex_gen,var_id=var_id,inst_id=inst_id,body=drecurseOnDed body,pos=pos}))
        | recurseOnDed(pickWitnessesDed({ex_gen,var_ids,inst_id,body,pos})) = 
             g(pickWitnessesDed({ex_gen=recurseOnPhrase ex_gen,var_ids=var_ids,inst_id=inst_id,body=drecurseOnDed body,pos=pos}))
      and g(d) = f(ded(d))
      and recurseOnCaseClause({case_name=NONE,alt,proof}) = {case_name=NONE,alt=erecurseOnExp alt,proof=drecurseOnDed proof}
        | recurseOnCaseClause({case_name=SOME p,alt,proof}) = {case_name=SOME p,alt=erecurseOnExp alt,proof=drecurseOnDed proof}
      and recurseOnCheckClause({test=elseCond,result}) = {test=elseCond,result=erecurseOnExp result}
        | recurseOnCheckClause({test=boolCond p,result}) = {test=boolCond (recurseOnPhrase p),result=erecurseOnExp result}
      and recurseOnDCheckClause({test=elseCond,result}) = {test=elseCond,result=drecurseOnDed result}
        | recurseOnDCheckClause({test=boolCond p,result}) = {test=boolCond (recurseOnPhrase p),result=drecurseOnDed result}
      and recurseOnMatchClause({pat=p,exp=e}) = {pat=recurseOnPattern(p),exp=erecurseOnExp e}
      and recurseOnDMatchClause({pat=p,ded=d}:dmatch_clause) = {pat=recurseOnPattern(p),ded=drecurseOnDed d}
      and recurseOnBinding({bpat,def,pos}) = {bpat=recurseOnPattern(bpat),def=recurseOnPhrase def,pos=pos}
      and recurseOnPhrase(exp(e)) = recurseOnExp(e)
        | recurseOnPhrase(ded(d)) = recurseOnDed(d)
      and erecurseOnExp(e) = getExp(recurseOnExp(e))
      and drecurseOnDed(d) = getDed(recurseOnDed(d))
      and getExp(exp(e)) = e
      and getDed(ded(d)) = d
      and recurseOnPattern(wherePat({pat,guard,pos})) = wherePat({pat=recurseOnPattern(pat),guard=erecurseOnExp(guard),pos=pos})
        | recurseOnPattern(listPats({member_pats,pos})) = listPats({member_pats=(map recurseOnPattern member_pats),pos=pos})    
        | recurseOnPattern(listPat({head_pat,tail_pat,pos})) = listPat({head_pat=recurseOnPattern(head_pat),tail_pat=recurseOnPattern(tail_pat),pos=pos})
        | recurseOnPattern(cellPat({pat,pos})) = cellPat({pat=recurseOnPattern(pat),pos=pos})
        | recurseOnPattern(splitPat({pats,pos,re_form,code})) = splitPat({pats=(map recurseOnPattern pats),pos=pos,re_form=re_form,code=code})
        | recurseOnPattern(reStarPat({pat,pos,re_form,code})) = reStarPat({pat=recurseOnPattern(pat),pos=pos,re_form=re_form,code=code})
        | recurseOnPattern(reRangePat({from_pat,to_pat,lo,hi,pos})) = reRangePat({from_pat=recurseOnPattern(from_pat),to_pat=recurseOnPattern(to_pat),lo=lo,hi=hi,pos=pos})
        | recurseOnPattern(rePlusPat({pat,pos,re_form,code})) = rePlusPat({pat=recurseOnPattern(pat),pos=pos,re_form=re_form,code=code})
        | recurseOnPattern(reRepPat({pat,times,pos,re_form,code})) = reRepPat({pat=recurseOnPattern(pat),times=times,pos=pos,re_form=re_form,code=code})
        | recurseOnPattern(reLitPat({pat,pos})) = reLitPat({pat=recurseOnPattern(pat),pos=pos})
        | recurseOnPattern(reOptPat({pat,pos,re_form,code})) = reOptPat({pat=recurseOnPattern(pat),pos=pos,re_form=re_form,code=code})
        | recurseOnPattern(namedPat({name,pat,pos})) = namedPat({name=name,pat=recurseOnPattern(pat),pos=pos})
        | recurseOnPattern(compoundPat({head_pat,rest_pats,pos})) = compoundPat({head_pat=recurseOnPattern(head_pat),rest_pats=(map recurseOnPattern rest_pats),pos=pos})
        | recurseOnPattern(disjPat({pats,pos})) = disjPat({pats=(map recurseOnPattern pats),pos=pos})
        | recurseOnPattern(p) = p 
  in 
     recurseOnPhrase(p) 
  end

fun desugarNestedTrys(tryExp({choices=[e],pos})) = e
  | desugarNestedTrys(e as tryExp({choices=[e1,e2],pos})) = e
  | desugarNestedTrys(tryExp({choices=e1::e2::e3::rest,pos})) = 
        let val e' = desugarNestedTrys(tryExp({choices=e2::e3::rest,pos=pos}))
        in 
           tryExp({choices=[e1,e'],pos=pos})
        end
  | desugarNestedTrys(e) = e
  
fun desugarNestedLets(letExp({bindings=[],body,pos})) = body 
  | desugarNestedLets(letExp({bindings={bpat,def,pos=bpos}::rest,body,pos})) =
         let val rem_let_exp = (case rest of 
                                   [] => body
                                 | _ => desugarNestedLets(letExp({bindings=rest,body=body,pos=pos})))
         in 
            letExp({bindings=[{bpat=bpat,def=def,pos=bpos}],body=rem_let_exp,pos=pos})
         end
  | desugarNestedLets(e) = e

fun desugarSingleLets(letExp({bindings=[{bpat,def,pos=bpos}],body,pos})) = 
         matchExp({discriminant=def,clauses=[{pat=bpat,exp=body}],pos=pos})
  | desugarSingleLets(e) = e

fun desugarLetrecs(letRecExp({bindings,body,pos})) = 
     let fun makeUnitCell(some_pos) = cellExp({contents=exp(listExp({members=[],pos=some_pos})),pos=some_pos})
         fun getPatId(namedPat({name,...})) = name
           | getPatId(idPat({name,...})) = name 
         val ids_and_defs = List.map (fn {bpat,def,...} => (getPatId bpat,def)) bindings
         val (ids,defs) = Basic.unZip(ids_and_defs)
         val bindings':binding list = map (fn {bpat,def,pos} => {bpat=bpat,def=exp(makeUnitCell(pos)),pos=pos}) bindings
         fun makeRefExp(id) = refExp({cell_exp=idExp({msym=mSym id,mods=[],no_mods=true,sym=id,pos=dum_pos}),pos=dum_pos})
         val id_replacements = map makeRefExp ids
         val defs' = List.map (fn def => replaceIdInPhraseLst(ids,def,id_replacements)) defs
         val ids_defs' = Basic.zip(ids,defs')
         val body_members = map (fn (id,def') => exp(setCellExp({cell_exp=idExp({msym=mSym id,mods=[],no_mods=true,sym=id,pos=dum_pos}),
                                                                 set_phrase=def',pos=dum_pos}))) ids_defs'
         val body' = exp(replaceIdInExpLst(ids,body,id_replacements))
     in
       letExp({bindings=bindings',body=beginExp({members=body_members@[body'],pos=dum_pos}),pos=pos})
     end 
  | desugarLetrecs(e) = e

fun desugarUandBApps(BAppExp({proc,arg1,arg2,pos})) = appExp({proc=proc,args=[arg1,arg2],pos=pos,alt_exp=ref(NONE)})
  | desugarUandBApps(UAppExp({proc,arg,pos})) = appExp({proc=proc,args=[arg],pos=pos,alt_exp=ref(NONE)})
  | desugarUandBApps(e) = e

fun splitAppExps(e as (appExp({proc,args,pos,...}))) = 
       let val len = length(args)
       in
          if len = 1 then
             UAppExp({proc=proc,arg=hd args,pos=pos})
          else if len = 2 then
                   BAppExp({proc=proc,arg1 = hd(args), arg2 = hd(tl(args)), pos=pos})
               else e
       end
  | splitAppExps(e) = e

fun psplitAppExps(p as (exp(e as (appExp({proc,args,pos,alt_exp=ref(NONE),...}))))) = 
       let val len = length(args)
           val res = if len = 1 then
                        exp(UAppExp({proc=proc,arg=hd args,pos=pos}))
                     else if len = 2 then
                                exp(BAppExp({proc=proc,arg1 = hd(args), arg2 = hd(tl(args)), pos=pos}))
                          else p
       in
          res 
       end
  | psplitAppExps(p as (exp(e as (appExp({alt_exp=ref(SOME(e')),...}))))) = psplitAppExps(exp(e'))
  | psplitAppExps(p as (ded(d as (methodAppDed({method,args,pos}))))) = 
       let val len = length(args)
           val res = if len = 1 then
                        ded(UMethAppDed({method=method,arg=hd args,pos=pos}))
                     else if len = 2 then
                             ded(BMethAppDed({method=method,arg1=hd args,arg2=hd(tl(args)),pos=pos}))
                          else p
       in
          res 
       end         
  | psplitAppExps(p:phrase) = p

fun desugarUB(e) = (case (applyExpFunRecursively(desugarUandBApps,exp e)) of
                       exp(e) => e)

fun splitExpApps(p) = applyExpFunRecursively(splitAppExps,p)

fun splitApps(p) = applyPhraseFunRecursively(psplitAppExps,p)

fun desugarPhrase(p) = applyExpFunRecursively(desugarSingleLets,(applyExpFunRecursively(desugarNestedLets,
applyExpFunRecursively(desugarLetrecs,applyExpFunRecursively(desugarNestedTrys,p)))))

fun desugarListComprehension(e1,pat,e2,guard_opt) = 
   let val fresh_sym = Symbol.freshSymbol(SOME "v")
       val fresh_id = idExp({msym=msym(fresh_sym),mods=[],sym=fresh_sym,no_mods=true,pos=posOfPat(pat)})
       val match_exp = let val discriminant_phrase = exp(fresh_id)
                           val match_clause = {pat=pat,
					       exp=e1}
                       in
                         matchExp({discriminant=discriminant_phrase, 
				   clauses=[match_clause],
				   pos = posOfExp(e1)})
                       end
       val lambda_exp =  functionExp({params=[someParam({name=fresh_sym,pos=posOfPat(pat),sort_as_sym_term=NONE,op_tag=NONE,sort_as_fterm=NONE,sort_as_exp=NONE})],
				      body=match_exp,
				      pos=posOfExp(e1)})
       val map_sym = S.symbol("map")
       val map_select_sym = S.symbol("map-select-2")
       fun guardMatchExp(g) = let val discriminant_phrase = exp(fresh_id)
				  val match_clause = {pat=pat,
						      exp=g}
			      in
				  matchExp({discriminant=discriminant_phrase, 
					    clauses=[match_clause],
					    pos = posOfExp(e1)})
			      end
       fun guardLambdaExp(g) =  functionExp({params=[someParam({name=fresh_sym,pos=posOfPat(pat),sort_as_sym_term=NONE,op_tag=NONE,sort_as_fterm=NONE,sort_as_exp=NONE})],
					    body=guardMatchExp(g),
					    pos=posOfExp(e1)})

    in 
      (case guard_opt of 
          NONE => appExp({proc=exp(idExp({msym=msym(map_sym),mods=[],sym=map_sym,no_mods=true,pos=posOfExp(e1)})),
			  args=[exp(lambda_exp),exp(e2)], 
			  pos=posOfExp(e1),
			  alt_exp=ref(NONE)})
        | SOME(g) => appExp({proc=exp(idExp({msym=msym(map_select_sym),mods=[],sym=map_select_sym,no_mods=true,pos=posOfExp(e1)})),
			     args=[exp(lambda_exp),
				   exp(e2),
				   exp(guardLambdaExp(g))],
			     pos=posOfExp(e1),
			     alt_exp=ref(NONE)}))
    end				   

fun symTermAppToExp(t) = 
      let fun printSymTermVar(sym) = (Names.sort_variable_prefix)^(Symbol.name sym)
          fun unparse(t) = (case SymTerm.isTaggedConstant(t) of  
                               SOME(fsym,tpos) => let val (mods,s) = MS.split(fsym)
                                                  in
                                                     idExp({msym=fsym,mods=mods,sym=s,no_mods=null(mods),pos=tpos})
                                                  end
                             | _ => (case SymTerm.isTaggedApp(t) of 
                                       SOME(fsym,tpos,subterms) => 
                                          let val exps = map exp (map unparse subterms)
                                              val (mods,s) = MS.split(fsym)
                                              val app_res = appExp({proc=exp(idExp({msym=fsym,mods=mods,sym=s,no_mods=null(mods),pos=tpos})),
                                                                    args = exps,alt_exp=ref(NONE),pos=tpos})
                                          in   
                                             app_res
                                          end
                                     | _ => Basic.fail("")))
         val res = unparse(t)
      in 
         (case splitApps(exp(res)) of
            exp(e) => e)
      end  

fun checkInductionSyntax(d) =
     let fun checkIndClause({pat,...}:dmatch_clause) = 
               if isInductivePattern(pat) then ()
               else
                  raise SyntaxError("Invalid induction pattern: "^printPat(pat),SOME(posOfPat(pat)))
     in
        case d of 
           inductionDed({clauses,...}) => List.app checkIndClause clauses
         | _ => ()
     end

fun checkStructureCasesSyntax(d) =
     let fun checkIndClause({pat,...}:dmatch_clause) = 
               if isMultipleDTPattern(pat) then ()
               else
                  raise SyntaxError("Invalid constructor pattern: "^printPat(pat),SOME(posOfPat(pat)))
     in
        case d of 
           structureCasesDed({clauses,...}) => List.app checkIndClause clauses
         | _ => ()
     end

fun phraseToExp(exp(e)) = e

fun namePhrase(exp(functionExp({params,body,pos})),str) = 
               exp(functionExp({params=params,body=body,pos=pos}))
  | namePhrase(exp(methodExp({params,body,pos,name})),str) = 
               exp(methodExp({params=params,body=body,name=ref(str),pos=pos}))
  | namePhrase(p,str) = p

fun desugarRuleDef(prim_method_name:string,rule_body:expression) = 
 let val rule_body' = 
          (case splitApps(exp rule_body) of
             exp(rb) => rb)
     val rule_body = rule_body'
 in
  (case rule_body of
      functionExp({params,body,pos,...}) =>
         let val arity = length(params)
             val ptp:possibly_typed_param = {name=dummy_sym,pos=dum_pos,sort_as_sym_term=NONE,op_tag=NONE,sort_as_fterm=NONE,sort_as_exp=NONE}
             val binding:binding = {bpat=idPat(ptp),def=exp(rule_body),pos=posOfExp(rule_body)}
             val dum_modsym':MS.mod_symbol = MS.makeModSymbol([],dummy_sym,dummy_sym)	       	     
             fun getArg(someParam({name,pos,...})) = exp(idExp({msym=msym(name),mods=[],sym=name,no_mods=true,pos=pos}))
               | getArg(wildCard(pos)) = exp(idExp({msym=dum_modsym',mods=[],sym=dummy_sym,no_mods=true,pos=dum_pos}))
             val fun_app = if arity = 1 then UAppExp({proc=exp(idExp({msym=dum_modsym',mods=[],sym=dummy_sym,no_mods=true,pos=dum_pos})),
                                                      arg=getArg(hd(params)),pos=dum_pos})
                           else if arity = 2 then 
                                BAppExp({proc=exp(idExp({msym=dum_modsym',mods=[],sym=dummy_sym,no_mods=true,pos=dum_pos})),
                                         arg1=getArg(hd(params)),arg2=getArg(hd(tl(params))),pos=dum_pos})
                           else appExp({proc=exp(idExp({msym=dum_modsym',mods=[],sym=dummy_sym,no_mods=true,pos=dum_pos})),alt_exp=ref(NONE),
                                        args=(map getArg params),pos=dum_pos})
             val body = methodAppDed({method=idExp({msym=Names.mprivate_force_symbol,mods=[],sym=Names.private_force_symbol,no_mods=true,pos=dum_pos}),
                                      args=[exp(fun_app)],pos=dum_pos})
             val dlet_proof = letDed({bindings=[binding],body=body,pos=dum_pos})
         in
           methodExp({params=params,body=dlet_proof,pos=pos,name=ref(prim_method_name)})
         end)
  end

fun defToString({name,...}:possibly_typed_param,e) = 
    let val fv = MS.listModSymbols(freeVarsExp(e)) handle _ => []
    in
        "\nParameter " ^ (S.name name) ^ " has this defining expression: " ^ (unparseExp e) ^
	", whose free ids are: " ^ (Basic.printListStr(fv,MS.name,","))
    end

fun directiveToString(definition(sym,p,b)) = 
   let val fv = MS.listModSymbols(freeVarsPhrase(p)) handle _ => []
   in
      "definition: symbol " ^ (S.name(sym)) ^ " is defined as the phrase: " ^ (unparsePhrase p) ^
      ", whose free ids are: " ^ (Basic.printListStr(fv,MS.name,","))
   end
  | directiveToString(definitions(param_exp_list,b)) = "definitions: " ^ Basic.printListStr(param_exp_list,defToString,"\n")
  | directiveToString(_) = "Some other directive"

fun getPair({name,...}:possibly_typed_param,e) = (name,e)

fun getDefPairs(definition(sym,exp(e),b)) = [(sym,e)]
  | getDefPairs(definitions(param_exp_list,b)) = (List.map getPair param_exp_list)
  | getDefPairs(_) = []

fun hoistRecDefs(inputs: user_input list) = 
     let val _ = (List.app (fn direcInput(i) => print("\n" ^ (directiveToString i)) 
                             | _ => ()) inputs)
         val def_pairs = Basic.flatten(List.map (fn direcInput(i) => getDefPairs(i)) inputs)
         val syms = map (fn (x,_) => x) def_pairs
	 val sym_set = S.symListToSet(syms)
	 val def_tripes = map (fn (sym,def_exp) => let val fvs = MS.listModSymbols(freeVarsExp(def_exp)) handle _ => []
	                                               val free_sym_set = S.symListToSet(map MS.nameAsSymbol fvs)
                                                       val intersection = S.intersection(sym_set,free_sym_set)
                                                   in
                                                      (sym,def_exp,intersection)
                                                   end)
                              def_pairs
         
     in
        inputs
     end

end (* of structure AbstractSyntax   *)
