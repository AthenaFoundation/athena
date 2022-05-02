(*======================================================================

A preliminary, experimental (and incomplete) compiler from Athena to SML.

=======================================================================*)

structure AthenaCompiler =

struct

structure S = Symbol
structure MS = ModSymbol
structure A = AbstractSyntax
structure Ab = ABase
structure B = Basic
structure N = Names
structure F = FTerm
structure Pos = Position
structure P = Prop
structure D = Data
structure ATV = AthTermVar
structure AT = AthTerm

val global_fresh_counter = ref(0)

fun makeFreshId() = "v" ^ (Int.toString(Basic.incAndReturn(global_fresh_counter)))

datatype SML_Expression  =  
  varExp of string 
| intExp of int
| realExp of real 
| stringExp of string
| appExp of SML_Expression * (SML_Expression list) 
| handleExp of {main: SML_Expression, except: SML_Expression, alternative: SML_Expression}
| lambdaExp of string list * SML_Expression
| listExp of SML_Expression list 
| logAndExp of SML_Expression list
| logOrExp of SML_Expression list
| letExp of {bindings: (SML_Pattern * SML_Expression) list, body: SML_Expression}
| letrecExp of {bindings: (SML_Pattern * SML_Expression) list, body: SML_Expression}
| caseExp of {disc:SML_Expression, clauses: (SML_Pattern * SML_Expression) list}
| ifExp of {cond:SML_Expression,true_branch:SML_Expression, false_branch: SML_Expression}
| unitExp 
and 
  SML_Pattern = varPat of string |    
                wildcardPat | 
                intPat of int |
                realPat of real | 
                stringPat of string | 
                bracketListPat of (SML_Pattern list) | 
                consPat of SML_Pattern * SML_Pattern | 
                asPat of string * SML_Pattern | 
                treePat of string * (SML_Pattern list)

val (lp,rp,lb,rb,comma,quote,blank) = (Basic.lparen,Basic.rparen,Basic.lbrack,Basic.rbrack,Basic.comma,Basic.string_quote,Basic.blank)

fun unparse(varExp(s)) = s
  | unparse(intExp(i)) = Int.toString(i)
  | unparse(realExp(i)) = Real.toString(i)
  | unparse(stringExp(str)) = quote ^ str ^ quote
  | unparse(appExp(proc,args)) =(unparse proc) ^ lp ^ (Basic.printListStr(args,unparse,",")) ^ rp 
  | unparse(handleExp({main, except, alternative,...})) = lp ^ lp ^ (unparse main) ^ rp ^ " handle " ^ (unparse except) ^ " => " ^ (unparse alternative) ^ rp ^ rp 
  | unparse(lambdaExp(params,body)) = lp ^ "fn " ^ lp ^ (Basic.printListStr(params,fn x => x,",")) ^ rp ^
                                      " => " ^ (unparse body) ^ rp
  | unparse(listExp(exps)) = lb ^ (Basic.printListStr(exps,unparse,",")) ^ rb
  | unparse(logAndExp(args)) = lp ^ (Basic.printListStr(args,unparse," andalso ")) ^ rp
  | unparse(logOrExp(args)) = lp ^ (Basic.printListStr(args,unparse," orelse ")) ^ rp
  | unparse(letExp({bindings,body})) = "let " ^ (unparseBindings bindings) ^ "\nin\n" ^ (unparse body) ^ "\nend\n"
  | unparse(letrecExp({bindings,body})) = "let " ^ (unparseLetrecBindings bindings) ^ "\nin\n" ^ (unparse body) ^ "\nend\n"
  | unparse(caseExp({disc,clauses,...})) = 
      "(case " ^ (unparse disc) ^ " of " ^ (Basic.printListStr(clauses,unparseClause," | ")) ^ ")"
  | unparse(ifExp({cond,true_branch,false_branch,...})) = lp ^ "if " ^ (unparse cond) ^ " then " ^ (unparse true_branch) ^ " else " ^ (unparse false_branch) ^ rp
  | unparse(unitExp) = "()"
and unparsePattern(varPat(s)) = s
  | unparsePattern(wildcardPat) = "_"
  | unparsePattern(intPat(i)) = Int.toString(i)
  | unparsePattern(realPat(r)) = Real.toString(r)
  | unparsePattern(asPat(str,p)) = lp ^ str ^ " as " ^ (unparsePattern p) ^ rp 
  | unparsePattern(consPat(p1,p2)) = lp ^ (unparsePattern p1) ^ "::" ^ (unparsePattern p2) ^ rp
  | unparsePattern(bracketListPat(pats)) = lb ^ (Basic.printListStr(pats,unparsePattern,",")) ^ rb
  | unparsePattern(treePat(s,args)) = s ^ lp ^ (Basic.printListStr(args,unparsePattern,",")) ^ rp 
  | unparsePattern(_) = "DON'T KNOW HOW TO UNPARSE THIS PATTERN" 
and unparseClause(pat,exp) = unparsePattern(pat) ^ " => " ^ (unparse exp)
and unparseBindings(binding_list) = (Basic.printListStr(binding_list,unparseBinding,"\n"))
and unparseBinding(pat,e) = " val " ^ (unparsePattern pat) ^ " = " ^ (unparse e)
and unparseLetrecBindings((varPat(s),lambdaExp(params,body))::more) = " fun " ^ s ^ lp ^ (Basic.printListStr(params,fn x => x,",")) ^ rp ^ " = " ^ (unparse body) ^
                                                                      (Basic.printListStr(more,unparseLetrecBinding,"\n"))
and unparseLetrecBinding(varPat(s),lambdaExp(params,body)) = "\n and " ^ s ^ lp ^ (Basic.printListStr(params,fn x => x,",")) ^ rp ^ " = " ^ (unparse body)

val makeFreshAb = 
  let val ab_counter = ref(0)
  in 
     (fn () => "ab" ^ (Int.toString(Basic.incAndReturn ab_counter)))
  end

fun doInjections([],e:SML_Expression) = e
  | doInjections(injections:(string * string) list,e:SML_Expression) =
     let fun loop([],res) = res 
           | loop((injector,str)::more,res) = loop(more,(varPat(str),appExp(varExp(injector),[varExp(str)]))::res)
         val binding_list = loop(injections,[])
     in 
       letExp({bindings=binding_list,body=e})
     end

fun compilePhrase(phrase) = 
  let val top_ab_param = varExp(makeFreshAb())
      fun isFree(name) = true
      fun getArg(A.wildCard(_)) = "_"
        | getArg(A.someParam({name,...})) = S.name(name)    
      fun comExp(A.idExp({msym,pos,...}),_) = varExp(MS.name(msym))
        | comExp(A.unitExp(_),_) = varExp("unitVal")
        | comExp(A.listExp({members,...}),ab) = appExp(varExp("listVal"),[listExp(map (fn p => comPhrase(p,ab)) members)])
        | comExp(A.functionExp({params, body, pos,...}),ab) =  
            let val args = map getArg params
                val ab' = makeFreshAb()
                val args' = args@[ab']
            in
               lambdaExp(args',comExp(body,varExp(ab')))
            end
        | comExp(A.logicalAndExp({args,...}),ab:SML_Expression) = logAndExp(map (fn p => comPhrase(p,ab)) args)
        | comExp(A.logicalOrExp({args,...}),ab) = logOrExp(map (fn p => comPhrase(p,ab)) args)
        | comExp(A.letExp({bindings,body,pos,...}),ab) = 
              let val SML_bindings = compileLetBindings(bindings,ab)
                  val SML_body = comExp(body,ab)
              in
                 letExp({bindings=SML_bindings,body=SML_body})
              end
        | comExp(A.letRecExp({bindings,body,pos,...}),ab) = 
              let val SML_bindings = compileLetBindings(bindings,ab)
                  val SML_body = comExp(body,ab)
              in
                 letrecExp({bindings=SML_bindings,body=SML_body})
              end
        | comExp(A.UAppExp({proc,arg,pos,...}),ab) = 
             (case proc of 
                A.exp(A.idExp({msym,...})) => let val id_name = MS.name(msym)
                                              in
                                                 if isFree(id_name) then 
                                                    let val e:SML_Expression = comPhrase(arg,ab)
                                                    in
                                                       appExp(varExp(id_name),[e,ab])
                                                    end
                                                 else apply(id_name,[arg],ab)
                                              end
               | _ => appExp(comPhrase(proc,ab),[comPhrase(arg,ab),ab]))
        | comExp(A.BAppExp({proc,arg1,arg2,pos,...}),ab) = 
             (case proc of 
                A.exp(A.idExp({msym,...})) => 
                   let val id_name = MS.name(msym)
                   in
                      if isFree(id_name) then appExp(varExp(id_name),[comPhrase(arg1,ab),comPhrase(arg2,ab),ab]) else apply(id_name,[arg1,arg2],ab)
                   end
               | _ => appExp(comPhrase(proc,ab),[comPhrase(arg1,ab),comPhrase(arg2,ab),ab]))
        | comExp(A.checkExp({clauses,pos,...}),ab) = 
            (case clauses of 
                [] => appExp(varExp("Semant.evError"),[(stringExp "check error: all alternatives failed"),varExp("NONE")])
              | {test=A.boolCond(phr),result}::more => let val t = comPhrase(phr,ab)
                                                           val t' = appExp(varExp("valEq"),[t,varExp("Semant.true_val"),ab])
                                                       in
                                                          ifExp({cond=t',true_branch=comExp(result,ab),false_branch=comExp(A.checkExp({clauses=more,pos=pos}),ab)})
                                                       end
             | {test=A.elseCond,result}::more => comExp(result,ab))
        | comExp(A.matchExp({discriminant,clauses,pos,...}),ab) = 
             let val sml_disc = comPhrase(discriminant,ab)
                 val d_var_str = makeFreshId()
                 val d_var = varExp(d_var_str)
                 fun compileClause({pat,exp,...}:A.match_clause,more_clauses:A.match_clause list,ab) = 
                        let val (sml_pat,sml_conds,injections) = compilePattern(pat,ab)
                            val sml_exp = comExp(exp,ab)
                        in
                          (case sml_conds of
                              [] => (sml_pat,doInjections(injections,sml_exp))
                             | _ => let val sml_exp' = let val sml_clauses = compileClauses(more_clauses,[],ab)
                                                           val fb = caseExp({disc=d_var,clauses=sml_clauses})
                                                       in
                                                         ifExp({cond=logAndExp(sml_conds),true_branch=doInjections(injections,sml_exp),false_branch=fb})
                                                       end
                                    in
                                      (sml_pat,doInjections(injections,sml_exp'))
                                    end)
                        end
                 and compileClauses([],sml_clauses,ab) = rev(sml_clauses)
                   | compileClauses(clause::more_clauses,sml_clauses,ab) = 
                        let val sml_clause as (sml_pat,sml_exp) = compileClause(clause,more_clauses,ab)
                        in
                          compileClauses(more_clauses,sml_clause::sml_clauses,ab)
                        end
                 val sml_clauses = compileClauses(clauses,[],ab)
             in
                letExp({bindings=[(varPat(d_var_str),sml_disc)],body=caseExp({disc=d_var,clauses=sml_clauses})})
             end
    | comExp(A.appExp({proc,args,pos,alt_exp,...}),ab) = 
        (print("\nApp here...\n");
         (case proc of 
                A.exp(A.idExp({msym,...})) => 
                   let val id_name = MS.name(msym)
                   in
                      if isFree(id_name) then appExp(varExp(id_name),(map (fn p => comPhrase(p,ab)) args)@[ab])
                      else apply(id_name,args,ab)
                   end
               | _ => appExp(comPhrase(proc,ab),(map (fn p => comPhrase(p,ab)) args)@[ab])))
    | comExp(e,ab) = unitExp
    and      
          comDed(A.assumeDed(_),_) = raise Basic.Never
        | comDed(_,_) = raise Basic.Never
    and
         comPhrase(A.exp(e),ab) = comExp(e,ab)
       | comPhrase(A.ded(d),ab) = comDed(d,ab)
    and apply(id_name,args,ab) = raise Basic.Never 
    and compileLetBindings(bindings,ab) = 
           let fun loop([],res) = rev(res)
                 | loop(binding::more,res) = loop(more,(compileLetBinding(binding,ab))::res)
           in
              loop(bindings,[])
           end
    and compileLetBinding({bpat,def,pos,...}:A.binding,ab) = 
            let val (pat,conds,injections) = compilePattern(bpat,ab)
                val phrase = comPhrase(def,ab)
            in 
               (pat,phrase)
            end
    and compilePattern(pat,ab) = 
           let fun comPat(A.idPat({name,sort_as_sym_term,op_tag,sort_as_fterm,sort_as_exp,...}),conds,injections) = 
                             (varPat(S.name(name)),conds,injections)

                 | comPat(A.anyPat(_),conds,injections) = (wildcardPat,conds,injections)


                 | comPat(A.listPats({member_pats,pos,...}),conds,injections) = 
                     let val (sml_pats,conds',injections') = comPatLst(member_pats,[],conds,injections)
                      in
                         (bracketListPat(sml_pats),conds',injections')
                      end

                 | comPat(A.listPat({head_pat,tail_pat as A.idPat({name,...}),pos,...}),conds,injections) = 
                      let val ([sml_head_pat,sml_tail_pat],conds',injections') = comPatLst([head_pat,tail_pat],[],conds,injections)
                      in
                         (consPat(sml_head_pat,sml_tail_pat),conds',("listVal",S.name(name))::injections')
                      end

                 | comPat(A.listPat({head_pat,tail_pat,pos,...}),conds,injections) = 
                      let val ([sml_head_pat,sml_tail_pat],conds',injections') = comPatLst([head_pat,tail_pat],[],conds,injections)
                      in
                         (consPat(sml_head_pat,sml_tail_pat),conds',injections')
                      end
                 | comPat(A.someListPat({id as A.someParam({name,...}),pos,...}),conds,injections) = 
                         (varPat(S.name(name)),conds,("listVal",S.name(name))::injections)

                 | comPat(A.someListPat(_),conds,injections) =  
                       (wildcardPat,conds,injections)

                 | comPat(pat,_,_) = raise Basic.Never

               and comPatLst([],sml_pats,conds,injections) = (rev sml_pats,rev conds, rev injections)
                 | comPatLst(p::more,sml_pats,conds,injections) = 
                      let val (sml_pat,conds',injections') = comPat(p,conds,injections)
                      in
                         comPatLst(more,sml_pat::sml_pats,conds',injections')
                      end

               val res as (sml_pat,conds,injections) = comPat(pat,[],[])
           in
              if A.isListPat(pat) then (treePat("listVal",[sml_pat]),conds,injections) else res
           end
 in
    comPhrase(phrase,top_ab_param)
 end

end

