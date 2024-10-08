(*======================================================================

This file contains a hand-rolled tokenizer and parser for infix-style function
applications in Athena. It can handle precedence levels and associativity specs,
and can also mix infix and prefix styles.

=======================================================================*)

structure InfixParser =
struct

structure F = FTerm
structure D = Data 
open AbstractSyntax
open SemanticValues

exception InfixParseError of string

fun infixParseError(msg,SOME(pos)) = 
       raise InfixParseError(A.posToString(pos)^": Infix parsing error: "^msg^".")
  | infixParseError(msg,NONE) = raise InfixParseError(" Infix parsing error "^msg^".")

datatype associativity = LEFT | RIGHT

fun debugPrint(str) = if true orelse !Options.first_time then () else print(str)

fun decodeAssoc(true) = LEFT
  | decodeAssoc(false) = RIGHT

fun tranAssoc(ref(NONE)) = NONE
  | tranAssoc(ref(SOME(b))) = SOME(decodeAssoc b)

datatype tok = LPAREN of pos | RPAREN of pos | COMMA of pos | DOT of pos 
             | NOT of pos | AND of pos | OR of pos | IF of pos | IFF of pos | QUANT of  A.expression * pos 
             | OP of {name:MS.mod_symbol,arity:int,prec:int,assoc:associativity option,
                      is_fsym:bool,pos:pos,orig_exp:AbstractSyntax.phrase option}  
             | exp_tok of AbstractSyntax.phrase

fun nullaryApp(toks) = let fun singleTokList([t]) = true
                             | singleTokList(_) = false
                           fun loop(toks) = if singleTokList(toks) then true 
                                            else (case (List.hd(toks),List.last(toks)) of
                                                    (LPAREN(_),RPAREN(_)) => loop(List.take(tl(toks),length(toks)-2))
                                                  | _ => false)
                       in
                         loop(toks)
                       end

fun isFSymToStr(true) = "IS_fsym"
  | isFSymToStr(_) = "IS_NOT_fsym"

fun tok2String(tok) = 
 let fun f(LPAREN(_)) = "LPAREN"
       | f(RPAREN(_)) = "RPAREN"
       | f(COMMA(_)) = "COMMA"
       | f(DOT(_)) = "DOT"
       | f(NOT(_)) = "NOT"
       | f(AND(_)) = "AND"
       | f(OR(_)) = "OR"
       | f(IF(_)) = "IF"
       | f(IFF(_)) = "IFF"
       | f(QUANT(_)) = "QUANT"
       | f(OP({name,arity,is_fsym,...})) = "OP: "^(MS.name(name))^":"^(Int.toString arity)^":"^(isFSymToStr(is_fsym))
       | f(exp_tok(p)) = "exp_tok: "^(A.unparsePhrase(p))
 in
    f(tok)
 end

fun toks2String(toks) = Basic.printListStr(toks,tok2String,"  ")

fun showToks(toks) = Basic.printListStr(toks,tok2String, " || ")

fun tokPos(LPAREN(pos)) = pos
  | tokPos(RPAREN(pos)) = pos
  | tokPos(COMMA(pos)) = pos
  | tokPos(DOT(pos)) = pos
  | tokPos(NOT(pos)) = pos
  | tokPos(AND(pos)) = pos
  | tokPos(OR(pos)) = pos
  | tokPos(IF(pos)) = pos
  | tokPos(IFF(pos)) = pos
  | tokPos(QUANT(_,pos)) = pos
  | tokPos(OP({pos,...})) = pos
  | tokPos(exp_tok(p)) = posOfPhrase(p)

fun isAlternation(f) = MS.name(f) = "or" orelse MS.name(f) = "|"

fun isImplication(f) = MS.name(f) = "if" orelse MS.name(f) = "==>"

fun isMOR(A.exp(A.appExp({proc=exp(idExp({sym,...})),args=[e1,e2],...}))) = 
           if Symbol.name(sym) = "MOR" then SOME(e1,e2) else NONE
  | isMOR(_) = NONE 

fun getSort(A.exp(appExp({proc=exp(idExp({msym,...})),...}))) = 
      (let val (_,result_sort,_,_) = Data.getSignature(msym)
       in
         SOME(result_sort) 
       end handle _ => NONE)
  | getSort(A.exp(idExp({msym,...}))) = 
      (let val (_,result_sort,_,_) = Data.getSignature(msym)
       in
         SOME(result_sort) 
       end handle _ => NONE)
 | getSort(_) = NONE

fun doIte(f,e1,e2,sort_option_2,default_res,op_pos) = 
                  (case (isAlternation(f),sort_option_2) of
                      (true,SOME(sort)) => let val _ = ()
                                           in
                                           if F.sortEq(sort,F.boolean_sort) then
                                              default_res
                                           else 
                                             let val res = A.exp(appExp({proc=exp(idExp({msym=Names.mMOR_symbol,mods=[],no_mods=true,
                                                                                         sym=MS.lastName(Names.mMOR_symbol),pos=op_pos})),
                                                                         args=[e1,e2],alt_exp=ref(NONE),pos=op_pos}))
                                             in
                                                res                                       
                                             end
                                           end
                    | (true,NONE) => let val _ = ()
                                     in
                                        (case getSort(e2) of
                                            SOME(sort2) => if not(F.sortEq(sort2,F.boolean_sort)) then
                                                              A.exp(appExp({proc=exp(idExp({msym=Names.mMOR_symbol,mods=[],no_mods=true,
                                                                                         sym=MS.lastName(Names.mMOR_symbol),pos=op_pos})),
                                                                         args=[e1,e2],alt_exp=ref(NONE),pos=op_pos}))
                                                           else default_res 
                                          | _ => let val sort1 = getSort(e1)
                                                 in
                                                   (case  sort1 of
                                                       SOME(sort1) => let val _ = ()
                                                                      in
                                                                        if not(F.sortEq(sort1,F.boolean_sort)) then
                                                                         A.exp(appExp({proc=exp(idExp({msym=Names.mMOR_symbol,mods=[],no_mods=true,
                                                                                           sym=MS.lastName(Names.mMOR_symbol),pos=op_pos})),
                                                                           args=[e1,e2],alt_exp=ref(NONE),pos=op_pos}))
                                                                        else default_res 
                                                                      end
                                                     | _ => default_res)
                                                  end)
                                     end
                    | _ => (case (isImplication(f),isMOR(e2)) of
                              (true,SOME(e2_left,e2_right)) => 
                                     let val ite_msym = Names.mite_symbol
                                         val res = A.exp(appExp({proc=exp(idExp({msym=ite_msym,mods=[],no_mods=true,sym=Names.ite_symbol,pos=op_pos})),
                                                                         args=[e1,e2_left,e2_right],alt_exp=ref(NONE),pos=op_pos}))
                                     in
                                        res
                                     end
                            | _ => default_res))

fun doBinary(f,e1,e2,op_pos,orig_exp,sort_option_2) = 
 let
 in
 (case orig_exp of 
     SOME(e) => let val default_res = A.exp(appExp({proc=e,args=[e1,e2],alt_exp=ref(NONE),pos=op_pos}))
                    val res = (doIte(f,e1,e2,sort_option_2,default_res,op_pos)) handle _ => (print("\ndoIte failed!");default_res)
                in
                  res
                end
   | _ => let val f_modules = MS.modules(f) 
              val default_res = A.exp(appExp({proc=exp(idExp({msym=f,mods=f_modules,no_mods=null(f_modules),sym=MS.lastName(f),pos=op_pos})),
                                              args=[e1,e2],alt_exp=ref(NONE),pos=op_pos}))
          in
            doIte(f,e1,e2,sort_option_2,default_res,op_pos)
          end)
 end

fun doUnary(f,e,op_pos,orig_exp) = 
 (case orig_exp of 
     SOME(e') => A.exp(appExp({proc=e',args=[e],alt_exp=ref(NONE),pos=op_pos}))
   | _ => A.exp(appExp({proc=exp(idExp({msym=f,mods=MS.modules(f),no_mods=null(MS.modules(f)),sym=MS.lastName(f),pos=op_pos})),args=[e],
                         alt_exp=ref(NONE),pos=op_pos})))

fun doNullary(f,op_pos,orig_exp) = 
 (case orig_exp of 
     SOME(e) => A.exp(appExp({proc=e,args=[],alt_exp=ref(NONE),pos=op_pos}))
    | NONE => A.exp(appExp({proc=exp(idExp({msym=f,mods=MS.modules(f),no_mods=null(MS.modules(f)),sym=MS.lastName(f),pos=op_pos})),args=[],alt_exp=ref(NONE),pos=op_pos})))

fun doApp(f,exps,op_pos,orig_exp) = 
 (case orig_exp of 
     SOME(e) => A.exp(appExp({proc=e,args= exps, alt_exp=ref(NONE),pos=op_pos}))
   | _ => A.exp(appExp({proc=exp(idExp({msym=f,mods=MS.modules(f),no_mods=null(MS.modules(f)),sym=MS.lastName(f),pos=op_pos})),args= exps,alt_exp=ref(NONE),pos=op_pos})))
                                   
fun okSorts(e:phrase,sort_option,previous_op,f,true) = 

(* Two sort constraints must be satisfied: (1) the resulting sort of f must be            *)
(* unifiable with the rightmost-argument sort of previous_op (if there is a previous_op   *)
(* at all); and (2) the leftmost-argument sort of f must be unifiable with                *)
(* sort_option, if that is defined at all.                                                *)

  let 
      val (f_param_sorts,f_result_sort,_,_) = Data.getSignature(f)
      val constraint_1 = 
           (case previous_op of 
               SOME(g) => let val (g_param_sorts,g_result_sort,_,_) = Data.getSignature(g)
                              val (p_sorts,a_sorts) = ([hd (rev g_param_sorts)],[f_result_sort])
                              val U = F.chooseUnificationProcedureForSortLists(p_sorts,a_sorts)
                              val res = (U(a_sorts,p_sorts,1);true) handle _ => false
                           in 
                             res
                           end
             | _ => true)
      val constraint_2 = (case sort_option of
                             SOME(sort) => let val (p_sorts,a_sorts) = ([hd f_param_sorts],[sort])
                                               val U = F.chooseUnificationProcedureForSortLists(p_sorts,a_sorts)
                                            in
                                               (U(a_sorts,p_sorts,1);true) handle _ => false
                                            end
                           | _ => true)
  in
     constraint_1 andalso constraint_2
  end
| okSorts(_) = true

fun sortsWorkOut x = (okSorts x) handle _ => true

fun combineSorts(f,SOME(arg_sorts)) = 
  let fun getResultSort() = let val (param_sorts,result_sort,is_poly,_) = Data.getSignature(f) 
                                val U = F.chooseUnificationProcedureForSortLists(param_sorts,arg_sorts)
                                val theta = U(arg_sorts,param_sorts,1)
                            in
                               F.applySub(theta,result_sort)
                            end
  in
     (SOME (getResultSort())) handle _ => NONE
  end
  | combineSorts(f,NONE) = 
      (let val (param_sorts,result_sort,is_poly,_) = Data.getSignature(f) 
       in
         if F.isGround(result_sort) then SOME(result_sort)
         else NONE
       end) handle _ => NONE

fun allSortOptions(L:{infix_exp:phrase, sort_option:FTerm.term option} list) = 
                       if Basic.forall(L,fn {sort_option=SOME(_),...} => true | _ => false) then
                           SOME(map #infix_exp L,map (fn {sort_option=SOME(sort),...} => sort) L)
                        else NONE

fun makeQuant(q,vars,e,pos) = A.exp(A.appExp({proc=exp(q),alt_exp=ref(NONE),
                                              args=vars@[e],pos=pos}))

fun tokenize(e,evPhrase,op_table) = 
  let 
      fun isMinusOrPlus(OP({name,...})) = if MS.modSymEq(name,Names.msubtraction_symbol) orelse MS.modSymEq(name,Names.maddition_symbol) then
                                          SOME(name) else NONE
        | isMinusOrPlus(_) = NONE
      fun getPrecedence(i,j) = if j < 0 then Options.defaultPrec(i) + 1 else j 
      fun unparseExp(unitExp({pos,...})) = [(LPAREN pos),RPAREN(Position.incPos(pos))]
      | unparseExp(e as opExp(_)) = [exp_tok(A.exp(e))]
      | unparseExp(e as idExp({msym=id_name,pos=id_pos,...})) = 
           if MS.name(id_name) = "." then [(DOT id_pos)]
           else if MS.name(id_name) = "," then ([(COMMA id_pos)])
           else (case MS.lookUp(op_table,id_name) of
                      SOME(i,j) => if i >= 0 then 
                                      let val j' = getPrecedence(i,j)
                                      in 
                                        [OP({name=id_name,arity=i,prec=j',
                                             assoc=NONE,is_fsym=false,pos=id_pos,orig_exp=SOME(A.exp(e))})]
                                      end
                                   else translate(e)
                   | _ => translate(e))
        | unparseExp(appExp({proc,pos,args,...})) = 
           let val toks = Basic.foldr(op@,[],map unparsePhrase args)
               val tail_pos = Position.incPos(if not(null(args)) then posOfPhrase(List.last(args)) else posOfPhrase(proc))
               val proc_tok = (unparsePhrase proc)
               val proc_tok' = if null(proc_tok) then proc_tok
                               else 
                                 (case isMinusOrPlus(hd proc_tok) of
                                   SOME(sym) => if length(args) = 1 then
                                                   [OP({name=sym,arity=1,
                                                    prec=Options.lowest_fsymbol_precedence,
                                                    assoc=NONE,is_fsym=true,pos=AbstractSyntax.posOfPhrase(proc),orig_exp=SOME(proc)})]
                                                else proc_tok 
                                 | _ => proc_tok)
           in
              [(LPAREN pos)]@proc_tok'@toks@[(RPAREN tail_pos)]
           end
       | unparseExp(e) = translate(e) 
     and translate(e) = 
          let val e_pos = AbstractSyntax.posOfExp(e) 
(***
              val _ = print("\nTokenizing this expression: "  ^ (A.unparseExp e))
***)
          in  
            (case evPhrase(A.exp e) of
                    termConVal(regFSym(some_fsym)) => 
                      (case Data.fsymAssoc(some_fsym) of
                          ref(SOME(b)) => 
                             [OP({name=D.fsymName(some_fsym),arity=D.fsymArity(some_fsym),
                                  prec=(!(D.fsymPrec some_fsym)),
                                  assoc=SOME(decodeAssoc(b)),is_fsym=true,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                        | ref(_) => [OP({name=D.fsymName(some_fsym),
					 arity=D.fsymArity(some_fsym),
                                         prec=(!(D.fsymPrec some_fsym)),
                                         assoc=NONE,
					 is_fsym=true,
					 pos=e_pos,
					 orig_exp=SOME(A.exp(e))})])
                  | termVal(t) => 
                        let val term_sort = AT.getSort(t)
                            (** val _ = print("\nHere's the INFIX term: " ^ (AT.toPrettyStringDefault(0,t)))  **)
                        in
                           (case F.isApp(term_sort) of 
                               SOME(fun_sort,sort_args) => 
                                 (* Shut this off for now, causing more problems than it solves. But still might make sense to 
                                    change the tokenizer to handle higher-order arguments in a different way... *)
                                 if AT.isGeneralConstant(t) andalso MS.modSymEq(fun_sort,Names.fun_name_msym) then 
                                   let val root_name = (case AT.isApp(t) of SOME(f,_) => f)
                                       val root_arity = length(sort_args)-1							   
                                   in
                                      [OP({name=root_name,
  					   arity=root_arity,
                                           prec=(if root_arity = 1 orelse root_arity = 2 then 110 else 0),
                                           assoc=NONE,
					   is_fsym=false,
					   pos=e_pos,
					   orig_exp=SOME(A.exp(e))})]
                                   end
                                 else
                                   (case AthTerm.isConstant(t) of
                                       SOME(f) => ([OP({name=f,arity=0,prec=0,assoc=NONE,
                                                        is_fsym=true,pos=e_pos,orig_exp=SOME(A.exp(e))})])
                                     | _ => (case AthTerm.isVarOpt(t) of
                                                SOME(v) => [exp_tok(A.exp e)] 
                                              | _ => [exp_tok(A.exp e)])))
                        end
                  | closUFunVal(_,_,_,{prec,name}) =>
                       [OP({name=A.makeMS(!name,NONE),arity=1,prec=(!prec),
                            assoc=NONE,is_fsym=false,pos=A.posOfExp(e),orig_exp=SOME(A.exp(e))})]
                  | closBFunVal(_,_,_,_,{prec,name,assoc}) =>
                       [OP({name=A.makeMS(!name,NONE),arity=2,prec=(!prec),
                            assoc=(case !assoc of NONE => NONE | SOME(b) => SOME(decodeAssoc(b))),
                            is_fsym=false,pos=A.posOfExp(e),orig_exp=SOME(A.exp(e))})]
                  | closFunVal(functionExp({params,body,pos=fpos}),_,{name,prec,assoc=ref(SOME(b))}) =>
                       [OP({name=A.makeMS(!name,NONE),arity=length(params),prec=(!prec),
                            assoc=SOME(decodeAssoc(b)),is_fsym=false,pos=fpos,orig_exp=SOME(A.exp(e))})]
                  | closFunVal(functionExp({params,body,pos=fpos}),_,{name,prec,assoc=ref(NONE)}) =>
                       [OP({name=A.makeMS(!name,NONE),arity=length(params),prec=(!prec),
                            assoc=NONE,is_fsym=false,pos=fpos,orig_exp=SOME(A.exp(e))})]
                  | primBFunVal(_,{name,prec,assoc=ref(SOME(b))}) => 
                       [OP({name=A.makeMS(name,NONE),arity=2,prec=(!prec),
                            assoc=SOME(decodeAssoc(b)),is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | primBFunVal(_,{name,prec,assoc=ref(NONE)}) => 
                       [OP({name=A.makeMS(name,NONE),arity=2,prec=(!prec),
                            assoc=NONE,is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | primUFunVal(_,{name,prec}) => 
                       [OP({name=A.makeMS(name,NONE),arity=1,prec=(!prec),
                            assoc=NONE,is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | funVal(_,fun_name,{arity,prec,assoc=ref(SOME(b))}) =>
                       [OP({name=A.makeMS(fun_name,NONE),arity=arity,prec=(!prec),
                            assoc=SOME(decodeAssoc(b)),is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | funVal(_,fun_name,{arity,prec,assoc=ref(NONE)}) =>
                       [OP({name=A.makeMS(fun_name,NONE),arity=arity,prec=(!prec),
                            assoc=NONE,is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | propConVal(notCon) => 
                       [OP({name=Names.mnot_symbol,arity=1,prec=(!(#prec(A.not_con_passoc))),
                            assoc=NONE,is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | propConVal(andCon) => 
                       [OP({name=Names.mand_symbol,arity=2,prec=(!(#prec(A.and_con_passoc))),
                            assoc=tranAssoc(#assoc(A.and_con_passoc)),is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | propConVal(orCon) => 
                       [OP({name=Names.mor_symbol,arity=2,prec=(!(#prec(A.or_con_passoc))),
                           assoc=tranAssoc(#assoc(A.or_con_passoc)),is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | propConVal(ifCon) => 
                      [OP({name=Names.mif_symbol,arity=2,prec=(!(#prec(A.if_con_passoc))),
                           assoc=tranAssoc(#assoc(A.if_con_passoc)),is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]
                  | propConVal(iffCon) => 
                      [OP({name=Names.miff_symbol,arity=2,prec=(!(#prec(A.iff_con_passoc))),
                           assoc=tranAssoc(#assoc(A.iff_con_passoc)),is_fsym=false,pos=e_pos,orig_exp=SOME(A.exp(e))})]

                  | propConVal(forallCon) =>  [QUANT(e,e_pos)]

                  | propConVal(existsCon) => [QUANT(e,e_pos)]
                  | propConVal(existsUniqueCon) => [QUANT(e,e_pos)]                 
                  | _ => [exp_tok(A.exp e)]) handle _ => [exp_tok(A.exp e)]
          end
      and unparseDed(d) = [exp_tok(A.ded d)]
      and unparsePhrase(exp(e)) = unparseExp(e)
        | unparsePhrase(ded(d)) = unparseDed(d)
  in
     unparseExp(e)
  end

fun parseExpTop1(token_list,evPhrase) = 
 let 
    fun endsWithDot(name) = (case List.last(explode(name)) of
                                #"." => true
                              | _ => false)
    fun warn(name,pos) = print((A.posToString pos)^": Warning: Quantifier variable name ends with dot: "^
                               (Names.variable_prefix)^name^"\nInfix notation intended?\n")
    fun checkVars(var_exps as (e::rest),more,SOME(last_var_name)) = 
         if endsWithDot(last_var_name) then (warn(last_var_name,A.posOfExp(e));(rev var_exps,more))
         else (rev var_exps,more)
     | checkVars(var_exps,more,_) = (rev var_exps,more) 
    fun parseExp2(tokens) = parseBinary({op_name=NONE,op_precedence=0},tokens)
    and doError(msg,t::_,_) = infixParseError(msg,SOME (tokPos(t)))
      | doError(msg,[],all_toks) = infixParseError(msg,SOME (Position.incPos(tokPos(List.last(all_toks)))))
    and parseBinary({op_name,op_precedence},tokens) = 
         let fun loop(res as ({infix_exp=e1,sort_option},(tok as (OP({name=f,arity=2,prec,assoc,pos,is_fsym,orig_exp,...})))::rest)) = 
                     if  Int.>=(prec,op_precedence) andalso sortsWorkOut(e1,sort_option,op_name,f,is_fsym) then 
                        let val prec' = (case assoc of 
                                            NONE => prec
                                          | SOME(RIGHT) => prec 
                                          | SOME(LEFT)  => prec + 1)
                            val op_name_opt = if is_fsym then SOME(f) else NONE
                         in
                           (case parseBinary({op_name=op_name_opt,op_precedence=prec'},rest) of 
                              ({infix_exp=e2,sort_option=sort_option_2},rest') => 
                                 loop({infix_exp=doBinary(f,e1,e2,pos,orig_exp,sort_option_2),sort_option=NONE},rest')) handle _ => res 
                
                         end
                     else res
               | loop(res) = res
            val parse_unary_results = let val _ = debugPrint("\n[[[[[ About to parseUnary these toks: " ^ (showToks tokens))
                                          val res = (case parseUnary(tokens) of 
                                                        (results as (_,more_toks)) => (debugPrint("\n]]]]] Remaining tokens: " ^ (showToks more_toks)); results))
                                      in 
                                         res
                                      end
         in
           loop(parse_unary_results)
         end
   and parseUnary(all_toks as (QUANT(q,pos))::rest) = 
          (case parseVars(rest,[]) of
             (vars,(DOT pos)::rest') => 
                (case  parseBinary({op_name=NONE,op_precedence=0},rest') of
                   ({infix_exp=e,...},rest'') => ({infix_exp=makeQuant(q,vars,e,pos),sort_option=NONE},rest''))
           | (_,toks) => doError("dot expected here",toks,all_toks))
     | parseUnary((OP({name=f,arity=1,prec,assoc,is_fsym,pos,orig_exp,...}))::rest) = 
         if is_fsym then 
           (case parseBinary({op_name=SOME f,op_precedence=prec},rest) of
               ({infix_exp=e,sort_option=SOME(sort)},rest') => 
                   ({infix_exp=doUnary(f,e,pos,orig_exp),sort_option=combineSorts(f,SOME [sort])},rest')
             | ({infix_exp=e,sort_option=NONE},rest') => ({infix_exp=doUnary(f,e,pos,orig_exp),sort_option=combineSorts(f,NONE)},rest'))
         else            
           (case parseBinary({op_name=NONE,op_precedence=prec},rest) of
               ({infix_exp=e,sort_option},rest') => ({infix_exp=doUnary(f,e,pos,orig_exp),sort_option=NONE},rest'))

     | parseUnary(all_toks as (LPAREN lp_pos)::(QUANT(q,pos))::rest) = 
        let val vars_res = parseVars(rest,[])
        in
          (case vars_res of
             (vars,(DOT pos)::rest') => 
                (case parseExp2(rest') of
                   ({infix_exp=e,...},(RPAREN _)::rest'') => ({infix_exp=makeQuant(q,vars,e,pos),sort_option=NONE},rest'')
                 | (_,toks) => doError("right parenthesis expected here",toks,all_toks))

           | (vars,rest') => (case parseExp2(rest') of
                                ({infix_exp=e,...},(RPAREN _)::rest'') => ({infix_exp=makeQuant(q,vars,e,pos),sort_option=NONE},rest'')
                              | (_,toks) => doError("right parenthesis expected here",toks,all_toks)))
        end
     | parseUnary(all_toks as (LPAREN lp_pos)::rest) = 
        ((case rest of
              (OP({name=f,arity=n,prec,assoc,is_fsym,pos,orig_exp,...}))::rest' => 
               if n > 1 then 
                let val app_arity = 
                         if MS.modSymEq(f,Names.app_fsym_mname) then 
			    Basic.skipAllAndReturnCount(rest',(fn tok => (case tok of RPAREN(_) => false | _ => true)))
                         else n
                    val _ = debugPrint("\nIn parseUnary APP_ARITY = " ^ (Int.toString app_arity) ^ "\nwith these rest' toks: " ^ (Basic.printListStr(rest',tok2String," || ")))
                in
                 ((case parse_N_Exps(rest',app_arity,[]) of
                     (results,(RPAREN _)::rest'') => 
                      let val _ = debugPrint("\nMADE IT HERE...")
                      in
       	                (case allSortOptions(results) of 
                            SOME(exps,sorts) => 
                              (({infix_exp=doApp(f,exps,pos,orig_exp),sort_option=combineSorts(f,SOME sorts)},rest''))
                            | _ => (({infix_exp=doApp(f,map #infix_exp results,pos,orig_exp),sort_option=combineSorts(f,NONE)},rest'')))
                      end
                   | (_,toks) => let val _ = debugPrint("\nWas expecting a rparen after parsing 4 expressions, instead got this: " ^ (Basic.printListStr(toks,tok2String," || ")))							
                                 in
                                   (doError("right parenthesis expected here",toks,all_toks))
                                end) handle ex => (debugPrint("\nEXCEPTION HERE!!!"); raise ex))
                end
               else 
                (case rest' of  (* New code here to deal with nullary applications *)
                    (RPAREN _)::rest'' => 
                       let val e = (case orig_exp of SOME(e') => e' | _ => A.exp(idExp({msym=f,mods=MS.modules(f),no_mods=null(MS.modules(f)),sym=MS.lastName(f),pos=pos})))
                       in
                          ({infix_exp=A.exp(appExp({proc=e,args=[],alt_exp=ref NONE,pos=posOfPhrase(e)})),
                                                   sort_option=combineSorts(f,NONE)},rest')
                       end
                   | _ => (case parseExp2(rest) of
                             ({infix_exp=e,sort_option},(RPAREN _)::rest') => ({infix_exp=e,sort_option=sort_option},rest')
                           | (_,toks) => (doError("right parenthesis expected here",toks,all_toks))))
          | _ => (
                  (case rest of  (* More new code here to deal with nullary applications *)
                     (exp_tok p)::(RPAREN _)::rest' => ({infix_exp=A.exp(appExp({proc=p,args=[],alt_exp=ref NONE,pos=posOfPhrase(p)})),
                                                         sort_option=NONE},rest')
                  | (exp_tok p1)::(exp_tok p2)::(RPAREN _)::rest' => 
                                   ({infix_exp=A.exp(appExp({proc=p1,args=[p2],alt_exp=ref NONE,pos=posOfPhrase(p1)})),
                                                         sort_option=NONE},rest')
                  | (OP({name=f,arity as 0,orig_exp as SOME(e),...}))::(RPAREN _)::rest' =>  
                                   ({infix_exp=A.exp(appExp({proc=e,args=[],alt_exp=ref NONE,pos=posOfPhrase(e)})),
                                     sort_option=combineSorts(f,NONE)},rest')
                  | (OP({name=f,arity as 0,pos,orig_exp as NONE,...}))::(RPAREN _)::rest' =>  
                                   ({infix_exp=A.exp(appExp({proc=exp(idExp({msym=f,mods=MS.modules(f),no_mods=null(MS.modules(f)),
                                                                             sym=MS.lastName(f),pos=pos})),args=[],alt_exp=ref NONE,pos=pos})),
                                     sort_option=combineSorts(f,NONE)},rest')
                  | _ => (case parseExp2(rest) of
                            ({infix_exp=e,sort_option},(RPAREN _)::rest') => 
                                if nullaryApp(List.take(rest,List.length(rest)-1)) then
                                       ({infix_exp=A.exp(appExp({proc=e,args=[],alt_exp=ref NONE,pos=posOfPhrase(e)})),
                                         sort_option=NONE},rest')
                                 else ({infix_exp=e,sort_option=sort_option},rest')
                          | (_,toks) => doError("right parenthesis expected here",toks,all_toks))))))
     | parseUnary((OP({name=f,arity=n,prec,assoc,is_fsym,pos,orig_exp,...}))::rest) = 
          if n = 0 andalso is_fsym then
               (case orig_exp of 
                 SOME(oe) => ({infix_exp=oe,sort_option=combineSorts(f,SOME [])},rest)
               | _ => ({infix_exp=doApp(f,[],pos,orig_exp),sort_option=combineSorts(f,SOME [])},rest))
          else (
          if is_fsym then
           (case parse_N_Exps(rest,n,[]) of 
                  (results,rest') => 
                     (case allSortOptions(results) of 
                         SOME(exps,sorts) => 
                           ({infix_exp=doApp(f,exps,pos,orig_exp),sort_option=combineSorts(f,SOME sorts)},rest')
                         | _ => ({infix_exp=doApp(f,map #infix_exp results,pos,orig_exp),sort_option=combineSorts(f,NONE)},rest')))
          else
           (case parse_N_Exps(rest,n,[]) of 
               (results,rest') => 
                  if n = 0 then 
                    (
                     (case orig_exp of 
                         SOME(oe) => ({infix_exp=oe,sort_option=combineSorts(f,NONE)},rest')
                       | _ => ({infix_exp=doApp(f,[],pos,orig_exp),sort_option=combineSorts(f,NONE)},rest)))
                  else  ({infix_exp=doApp(f,map #infix_exp results,pos,orig_exp),sort_option=combineSorts(f,NONE)},rest')))
     | parseUnary(exp_tok(A.exp(e as numExp({number=int_num(_),...})))::rest) = 
            ({infix_exp=A.exp e,sort_option=SOME(F.int_sort)},rest)
     | parseUnary((exp_tok(A.exp(e as numExp({number=real_num(_),...}))))::rest) = 
            ({infix_exp=A.exp e,sort_option=SOME(F.real_sort)},rest)
     | parseUnary((exp_tok(A.exp(e as termVarExp({term_var,...}))))::rest) = 
            ({infix_exp=A.exp e,sort_option=SOME(AthTermVar.getSort(term_var))},rest)
     | parseUnary((exp_tok e)::rest) = (({infix_exp=e,sort_option=NONE},rest))
     | parseUnary(toks) = doError("term or sentence expected here",toks,token_list)
   and parse_N_Exps(toks,0,res) = (rev(res),toks)
     | parse_N_Exps(toks,i,res) = 
            let val _ = debugPrint("\nInside parse_N_exps with i: " ^ (Int.toString i) ^ ", about to parse these toks: " ^ (Basic.printListStr(toks,tok2String," || ")))
            in 
              (case parseExp2(toks) of 
                  ({infix_exp=e,sort_option},more) => parse_N_Exps(more,i-1,{infix_exp=e,sort_option=sort_option}::res))
            end
   and parse_N_Comma_Separated_Exps(toks,0,res) = (rev(res),toks)
     | parse_N_Comma_Separated_Exps(toks,1,res) = 
           (case parseExp2(toks) of 
               ({infix_exp=e,sort_option},more) => let val sole = {infix_exp=e,sort_option=sort_option}
                                                   in (rev(sole::res),more)
                                                   end)
     | parse_N_Comma_Separated_Exps(toks,i,res) = 
                                  (case parseExp2(toks) of 
                                     ({infix_exp=e,sort_option},(COMMA pos)::more) => 
                                        parse_N_Comma_Separated_Exps(more,i-1,{infix_exp=e,sort_option=sort_option}::res))
   and parseExps(toks,res) = let val exp_opt = (SOME (parseExp2 toks)) handle _ => NONE 
                             in 
                                (case exp_opt of 
                                    NONE => (res,toks)
                                  | SOME({infix_exp=e,sort_option=so},more) => parseExps(more,{infix_exp=e,sort_option=so}::res))
                             end
   and parseVars(toks as (exp_tok e)::more,res) = 
        let val (e_res,ev_failed) = (evPhrase e,false) handle _  => (unitVal,true)
        in
          (case e_res of 
              termVal(t) => (case AT.isVarOpt(t) of
                                SOME(v) => (let val v_name = ATV.name(v)
                                                val _ = if endsWithDot(v_name) then warn(v_name,A.posOfPhrase(e)) else ()
                                            in 
                                               parseVars(more,e::res)
                                            end)
                             | _ => (rev res,toks))
            | _ => 

                     if ev_failed then parseVars(more,e::res)
                     else (rev res,toks))
        end
      | parseVars(toks as (t as (LPAREN lp_pos))::more,res) =  
           (case parseExp2(more) of
              ({infix_exp=e,...},(RPAREN _)::more') => parseVars(more',e::res)
            | (_,toks') => infixParseError("Missing right parenthesis for this left parenthesis",SOME((tokPos(t)))))
      | parseVars(more,res) = (rev res,more)
   val res = parseExp2(token_list)
in
  (res,parseExp2,parseUnary,parseBinary)
end

fun parseExpTop(token_list,evPhrase) = #1(parseExpTop1(token_list,evPhrase))

fun parse(e,evPhrase,op_table) = 
  let val toks = tokenize(e,evPhrase,op_table)
(*******)
      val _ = debugPrint("\nAbout to infix-parse this exp: " ^ (A.unparseExp e) ^ "\nHere are the tokens: " ^ (Basic.printListStr(toks,tok2String," || ")))
(*******)
      val res = (case parseExpTop(toks,evPhrase) of 
                   ({infix_exp=e,...},_) => e)
  in
    res
  end

fun parseOpt(e,evPhrase,op_table) = 
  let val toks = tokenize(e,evPhrase,op_table)
      val res = SOME(parseExpTop(toks,evPhrase)) handle _ => NONE
  in
    (case res of 
        SOME({infix_exp=e,...},_) => SOME(e)
      | _ => NONE)
  end

end

