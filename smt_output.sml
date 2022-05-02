(*======================================================================

Code for processing outputs of SMT solvers.

=======================================================================*)

structure SMTOutput = 

struct

structure A = AbstractSyntax

open Semantics

val fmap_module = Symbol.symbol("DMap")

val (fmap_sort_name,fmap_empty_map_name,fmap_update_name,fmap_apply_name) = ("DMap","empty-map","update","apply")

val (fmap_sort_symbol,
     fmap_empty_map_symbol,
     fmap_update_symbol,
     fmap_apply_symbol) = 
          (Symbol.symbol fmap_sort_name,
	   Symbol.symbol fmap_empty_map_name,
	   Symbol.symbol  fmap_update_name,
	   Symbol.symbol fmap_apply_name)

val (mfmap_sort_symbol,
     mfmap_empty_map_symbol,
     mfmap_update_symbol,
     mfmap_apply_symbol) = 
          (ModSymbol.makeModSymbol'([fmap_module],fmap_sort_symbol),
	   ModSymbol.makeModSymbol'([fmap_module],fmap_empty_map_symbol),
	   ModSymbol.makeModSymbol'([fmap_module],fmap_update_symbol),
	   ModSymbol.makeModSymbol'([fmap_module],fmap_apply_symbol))

fun isFMap(sort) = (case F.isApp(sort) of
                       SOME(root,_) => MS.modSymEq(root,mfmap_sort_symbol)
                     | _ => false)

exception missing_selector_ex      

val selector_warning = "\nWARNING: Some model identities require datatype selectors to be expressed,\n"^
                       "and some of the relevant datatypes do not have selectors.\n"^
                       "To get the full model, please add selectors to all datatypes and try again.\n"

fun processYicesOutput(stream:TextIO.instream,
		       conjuncts,
		       simplify_on,
		       var_table,
		       fsym_table,
		       poly_to_mono_sort_table,
		       id_table_opt) =		       
  let val (no_id_table,id_table) = (case id_table_opt of
                                       SOME(table) => (false,table)
                                     | _ => (true,HashTable.mkTable(SemanticValues.hashVal, valEq) (5,Data.GenEx("Failed table creation"))))
      val selector_warning_showed = ref(false)
      fun showSelectorWarning() = if !selector_warning_showed then () else (print(selector_warning); selector_warning_showed := true)
      fun refreshIdTable(term_val_1,term_val_2) = 					    
             (case (HashTable.find id_table term_val_1) of
                 SOME(listVal(vals)) => (HashTable.insert id_table (term_val_1,listVal(term_val_2::vals)))
               | _ => (HashTable.insert id_table (term_val_1,listVal([term_val_2]))))
      fun getLine() = Basic.getBalancedLine(stream)
      fun isIntNum(t) = (case AT.isNumConstantOpt(t) of
                            SOME(A.int_num(_)) => true
                          | _ => false)
      fun skipable(left,right) = let fun f((#"L")::(#"E")::(#"T")::_) = true
                                       | f((#"L")::(#"A")::(#"M")::(#"B")::(#"D")::(#"A")::_) = true
                                       | f(_) = false
                                 in 
                                    f(left) orelse f(right) 
                                 end
      fun rationalToReal(n,d) = 
             let val n' = (case Real.fromString(n^".0") of 
                             SOME(r) => r)
                 val d' = (case Real.fromString(d) of
                              SOME(r) => r)
                 val r = Real./(n',d')
             in 
                AT.makeNumTerm(A.real_num(r,ref (A.convertRealStr(Real.toString(r)))))
             end
      fun getVal(clist,arg_sort_opt,yices_numerals) = 
           let val str = implode(clist)
               val num_opt = (case AbstractSyntax.getAthNumber(str) of
                                SOME(anum) => (case arg_sort_opt of
                                                  SOME(arg_sort) => if F.termEq(arg_sort,F.int_sort) then SOME(AT.makeNumTerm(anum)) 
                                                                    else let val var_str = "fresh-"^(A.athNumberToString(anum)) 
								             val ynt = ATV.athTermVarWithSort(var_str,arg_sort) 
									     val _ = yices_numerals := ynt::(!yices_numerals)
                                                                         in
									    SOME(AT.makeVar(ynt))
                                                                          end
                                                | _ => SOME(AT.makeNumTerm(anum)))
                              | _ => if String.sub(str,0) = #"-" then 
                                       (case AbstractSyntax.getAthNumber(String.substring(str,1,String.size(str) - 1)) of
                                           SOME(anum) => SOME(AT.makeApp(Names.msubtraction_symbol,[AT.makeNumTerm(anum)]))
                                         | _ => NONE)
                                     else NONE)
           in
              (case num_opt of
                  SOME(t) => t
                | _ => (case (String.tokens (fn c => c = #"/") str) of
                           [n,d] => rationalToReal(n,d)
                         | _ => AT.makeConstant(A.makeMS(str,NONE))))
                    handle Basic.FailLst(_) => AT.true_term
           end
      val yices_numerals = ref []
      val first_line = getLine()
      fun makeTerm(fsym,args) = let val fsym_name = (MS.name(fsym))
                                in
				  applyTermConstructorNoPos(fsym,args)
				end
      fun getTail(_::t) = t
        | getTail(_) = []			
      fun parseTerm(clist,yices_numerals) = 
            let fun getFunctor(clist,res) = 
                       (case clist of
                           #" "::more => (rev res,more)
                         | #"\n"::more => (rev res,more)
                         | #")"::more => (rev res,clist)
                         | c::more => getFunctor(more,c::res)
                         | [] => (rev res,[]))
                fun getTerm(clist,arg_sort_opt) = 
                  let val clist = Basic.skipWhiteSpace(clist)
                  in
                     (case clist of
                        #"("::more => let val (fsym_clist,rest) = getFunctor(more,[])
					  val functor_app = implode(fsym_clist)
                                          val fsym_sym = (case fsym_clist of 
                                                             (#"m")::(#"o")::(#"d")::[] => Names.mmodulo_symbol
                                                           | (#"d")::(#"i")::(#"v")::[] => Names.mdivision_symbol
                                                           | c::rest => if Char.toString(c) = Names.smt_poly_con_name_prefix then
                                                                           let val (digits,rem) = Basic.skipUntil(rest,fn c => not(Char.isDigit(c)))
                                                                               val len = (case (Int.fromString(implode digits)) of
                                                                                             SOME(i) => i)
                                                                               val rem' = rev(List.take(rev(rem),len))
                                                                               val res = (implode rem')
									       val sort_string = List.take(rem,length(rem)-len)
                                                                           in
                                                                              if (res = "CONS") then N.mdouble_colon_cons_symbol else A.makeMS(res,NONE)
                                                                           end
                                                                        else let val fname_lst = tl(fsym_clist)
                                                                                 val res = (A.makeMS((implode fname_lst),NONE))
                                                                             in
                                                                                res
                                                                             end)
  				          val arg_sorts = (case (HashTable.find poly_to_mono_sort_table functor_app) of
                                                              SOME((asorts,_)) => asorts
                                                            | _ => let val (arg_sorts,range_sort,_,has_pred_based_sorts) = D.getSignature(fsym_sym) 
							           in arg_sorts end)
                                                                         handle e => 
                                                                               if Basic.prefix(Names.smt_default_selector_fun_sym_prefix_char_list, tl(fsym_clist))
                                                                               then raise missing_selector_ex else raise e
                                      in
                                        (case (let val res = getTerms(rest,arg_sorts,[])
                                              in
                                                 res
                                              end) of
                                            (args,#")"::rest') =>
                                              (case fsym_clist of
                                                (#"v")::rest => let val var_name = implode rest 
                                                                    val v = ATV.athTermVar(var_name)
                                                                    val vterm = (case ATV.find(var_table,v) of
                                                                                    SOME(v') => AT.makeVar(v')
                                                                                  | _ => AT.makeVar(v))
                                                                in  
                                                                   (makeTerm(mfmap_apply_symbol,[vterm,hd args]),rest')
                                                                end 
                                               | _ => ((makeTerm(fsym_sym,args),rest')
                                                   handle _ => (let val (arg_sorts,range_sort,_,has_pred_based_sorts) = D.getSignature(fsym_sym)
                                                                in 
                                                                   if null(arg_sorts) andalso isFMap(range_sort) then
                                                                      let val res_term = makeTerm(mfmap_apply_symbol,(makeTerm(fsym_sym,[]))::args)
                                                                      in 
                                                                        (res_term,rest')
                                                                      end
                                                                else let 
                                                                    fun f(arg,expected_sort) = 
                                                                            if isIntNum(arg) andalso not(F.sortEq(expected_sort,D.int_sort))
                                                                            then 
                                                                                 let val var_str = "fresh-"^(AT.toStringDefault(arg)) (***)
                                                                                     val ynt = ATV.athTermVarWithSort(var_str,expected_sort) 
                                                                                     val _ = yices_numerals := ynt::(!yices_numerals)
                                                                                 in
                                                                                    AT.makeVar(ynt)
                                                                                 end
                                                                            else arg 
                                                                    val args' = map f (Basic.zip(args,arg_sorts))
                                                                    val res_term = makeTerm(fsym_sym,args')
                                                                in
                                                                   (res_term,rest')
                                                                end end)))
                                          | (args,[]) => (makeTerm(fsym_sym,args),[]))
                                      end
                      | _ => let val (fsym_clist,rest) = getFunctor(clist,[])
                                 val fsym_clist' = tl fsym_clist
                                 val fsym_str = implode fsym_clist'
                                 val fsym_sym = A.makeMS(fsym_str,NONE)
                             in
                                (case fsym_clist of
                                    #"f"::rest' => if fsym_str = "alse" then (AT.false_term,rest)
                                                   else (makeTerm(fsym_sym,[]),rest)
                                  | #"p"::rest' => let val (digits,rem) = Basic.skipUntil(rest',fn c => not(Char.isDigit(c)))
                                                       val len = (case (Int.fromString(implode digits)) of
                                                                     SOME(i) => i)
                                                       val rem' = rev(List.take(rev(rem),len))
                                                       val res = (implode rem')
                                                       val fsym_sym = A.makeMS(res,NONE)
                                                   in
                                                      (case arg_sort_opt of 
                                                          SOME(arg_sort) => let val res = AT.makeSortedConstant(fsym_sym,arg_sort)
                                                                            in (res,rest) end
                                                        | _ => (case (HashTable.find poly_to_mono_sort_table (implode fsym_clist)) of
                                                                   SOME(_,res_sort) => let in (AT.makeSortedConstant(fsym_sym,res_sort),rest) end
                                                                 | _ =>  let in (makeTerm(fsym_sym,[]),rest) end))
                                                   end
                                  | #"v"::_ =>  let val var_name = fsym_str
                                                    val v = ATV.athTermVar(fsym_str)
                                                in
                                                   (case ATV.find(var_table,v) of
                                                       SOME(v') => (AT.makeVar(v'),rest)
                                                     | _ => (AT.makeVar(v),rest))
                                                end
                                  | #"'"::_ =>  (AT.makeIdeConstant(fsym_str),rest)
                                  | _ => let val res = (getVal(fsym_clist,arg_sort_opt,yices_numerals),rest)
                                         in
                                           res
                                         end)
                             end)
                  end
                and getTerms([],_,results) = (rev results,[])
                  | getTerms(clist,arg_sorts as arg_sort::more_argsorts,results) = 
                            (case getTerm(clist,SOME(arg_sort)) of
                                (t,#" "::rest) => getTerms(rest,more_argsorts,t::results)
                              | (t,rest as (#")"::_)) => (rev (t::results),rest)
                              | (t,rest as (_::_)) => getTerms(rest,more_argsorts,t::results)
                              | (t,[]) => (rev (t::results),[]))
            in
               getTerm(clist,NONE)
            end 
    fun makeNewIdentity(left,right) = 
            let val var_sort = AT.getSort(left)
                val ynt_str = "fresh-"^(AT.toStringDefault(right))
                val ynt = ATV.athTermVarWithSort(ynt_str,var_sort)
                val new_right = AT.makeVar(ynt)
                val _ = yices_numerals := ynt::(!yices_numerals)
                val res = makeTerm(Names.mequal_logical_symbol,[left,new_right])
            in
               (res,new_right)
            end
      val all_var_table_items = ref(NONE)
      fun getVarTableItems() = (case (!all_var_table_items) of
                                    NONE => let val res = ATV.listItemsi(var_table)
                                                val _ = all_var_table_items := SOME(res)
                                            in
                                              res
                                            end
                                   | SOME(res) => res)
      fun isNonIntVar(left) =
            (case AT.isVarOpt(left) of
                SOME(v) => (case (Basic.constructiveExists(getVarTableItems(),fn (v',_) => ATV.nameEq(v,v'))) of
                               SOME(v',_) => AT.makeVar(v')
                             | _ => left))
      fun processLine(line_chars) = 
               (case line_chars of 
                   [] => NONE
                 | (#"(")::(#"=")::(#" ")::rest => 
                     let val (left,rest') = parseTerm(rest,yices_numerals)
                         val (right,#")"::_) = parseTerm(Basic.skipWhiteSpace rest',yices_numerals)
                         val (identity,right') = 
                                     (((makeTerm(Names.mequal_logical_symbol,[left,right]),right)
                                           handle _ => if isIntNum(right) then let val res = makeNewIdentity(left,right) in res end 
                                                       else Basic.fail("\nSMT translation error.\n")))
                         val identity' = if AT.isVar(right) andalso not(AT.isVar(left)) then
                                           makeTerm(Names.mequal_logical_symbol,[right,left])
                                         else identity
                         val identity = identity'
                     in
                       if AT.termEq(left,right) then NONE
                       else (if (AT.isGround(identity) andalso Basic.isMemberEq(Prop.makeEquality(left,right'),conjuncts,Prop.alEq)) then
                                NONE else SOME(propVal (Prop.makeAtom identity)))
                     end
                 | _ => NONE)
      fun getModel(L) = 
            let val line = getLine()
                val line_chars = explode(line)
            in 
               if null(line_chars) then L
               else
                  let val identity_option = (processLine line_chars) handle e => (case e of
                                                                                       missing_selector_ex => (showSelectorWarning();NONE)
                                                                                     | _ => (NONE))
                  in  
		    (case identity_option of 
                        SOME(identity) => getModel(identity::L)
                      | _ => getModel(L))
                  end
            end
      fun allDistinct(terms) = let fun negateOne(s,terms) = 
                                           let fun loop([],res) = res
                                                 | loop(t::more,res) = let val res' = ((propVal(Prop.makeNegation(Prop.makeEquality(s,t))))::res)  handle _ => res
                                                                       in
                                                                          loop(more,res')
                                                                       end
                                           in
                                               loop(terms,[])
                                           end
                                   fun loop([],res) = res
                                     | loop(t::more,res) = loop(more,(negateOne(t,more))@res)
                               in
                                  loop(terms,[])
                               end
      fun isInputLeaf(x) = Basic.exists(conjuncts,fn c => (case Prop.isAtom(c) of 
                                                              SOME(t) => Basic.isMemberEq(x,AT.leaves(t),AT.termEq)
                                                            | _ => false))
      fun isFreshVariable(t) = (case AT.isVarOpt(t) of
                                   SOME(v) => let val str = ATV.name(v) 
                                              in
                                                if String.size(str) >= 6 andalso String.substring(str,0,6) = "fresh-" 
                                                then SOME(v) else NONE
                                              end
                                 | _ => NONE)
      fun simplify(propVal(eqn),model:value list)  = 
             (case Prop.isEquality(eqn) of
                 SOME(l,r) => (case isFreshVariable(r) of 
                                  SOME(v) => if isInputLeaf(l) then 
                                               (true,map (fn propVal(p) => propVal(Prop.replace(v,l,p))) model)
                                             else (false,model)
                                 | _ => (false,model))
               | _ => (false,model))
      fun simplifyModel(L) = 
              let fun loop([],latest_model) = latest_model
                    | loop(eqn::more,latest_model) = 
                         let val (has_change,model) = simplify(eqn,latest_model)
                         in
                            if has_change then loop(more,model)
                             else loop(more,latest_model)
                         end
                  fun removeTautologies(L) = 
                         Basic.filterOut(L,fn propVal(id) => (case Prop.isEquality(id) of
                                                                 SOME(l,r) => let val (lv,rv) = (termVal(l),termVal(r))
								                  val cond = AT.termEq(l,r)
                                                                                  val _ = if cond orelse no_id_table then () 
                                                                                          else (refreshIdTable(lv,rv);
                                                                                                if AT.isVar(l) orelse AT.isNumConstant(r) then () else  
                                                                                               (refreshIdTable(rv,lv)))
                                                                              in
                                                                                if no_id_table then cond else true
                                                                              end
                                                               | _ => Basic.fail("SMT translation error: identity expected here; instead found this sentence: " ^ 
							                         (Prop.toPrettyStringDefault(0,id)))))
                  fun removeRedundancies(L) = 
                         Basic.filterOut(L,fn propVal(id) => (case Prop.isEquality(id) of
                                                                 SOME(l,r) => let val (lv,rv) = (termVal(l),termVal(r))
                                                                                  val cond = ((Basic.isMemberEq(id,conjuncts,Prop.alEq) andalso not(AT.isVar(l))) 
                                                                                             orelse AT.termEq(l,r))
                                                                                  val _ = if cond orelse no_id_table then () 
                                                                                          else ((refreshIdTable(lv,rv));
                                                                                                if AT.isVar(l) orelse AT.isNumConstant(r) then () else  
                                                                                               (refreshIdTable(rv,lv)))
                                                                              in 
                                                                                 if no_id_table then cond else true                                                                     
                                                                              end
                                                               | _ => Basic.fail("SMT translation error: identity expected here.")))
              in
                 if simplify_on then removeRedundancies(loop(L,L))
                 else removeTautologies(loop(L,L))
              end
      fun getUnSatAssertions(clist) = 
             let fun loop(clist,res) = (case (Basic.skipWhiteSpace(clist)) of
                                          [] => res
                                        | clist' => (case parseTerm(clist',yices_numerals) of
                                                       (n,rest) => loop(rest,n::res)))
              in 
                 loop(clist,[])
              end
      fun getModel'(L) =
            (case getModel(L) of
               bindings => (case Basic.removeDuplicatesEq(!yices_numerals,ATV.athTermVarEq) of
                               [] => (simplifyModel(bindings))
                              | ynterms => let val L1 = simplifyModel(bindings)
					       val vars0 = List.filter (fn v => Basic.exists(L1,fn propVal(p) => P.occursFree(v,p))) ynterms
					       val vars = (List.map AT.makeVar vars0)
                                               val L2 = allDistinct vars
                                          in
					     L1@L2
					  end))
  in
    (case (explode first_line) of
       (#"u")::(#"n")::(#"s")::(#"a")::(#"t")::_ => (termVal(AT.makeIdeConstant("Unsatisfiable")))
     | (#"E")::(#"r")::(#"r")::(#"o")::(#"r")::_ => (termVal(AT.makeIdeConstant("Unknown-error")))
     | (#"u")::(#"n")::(#"k")::(#"n")::(#"o")::(#"w")::(#"n")::_ => 
          ((listVal([termVal(AT.makeIdeConstant("unknown")),listVal(getModel'([]))]))
             handle _ => termVal(AT.makeIdeConstant("unknown")))
     | (#"s")::(#"a")::(#"t")::_ => 
                  (case TextIO.lookahead(stream) of
                      SOME(#"u") => let val line2 = getLine()
                                    in
                                      if String.size(line2) > 26 andalso String.substring(line2,0,27) = "unsatisfied assertion ids: "
                                      then let val unsat_assertions = getUnSatAssertions(List.drop(explode(line2),27))
                                               val res:value list = getModel'([]) 
                                               val elem_1 = listVal([termVal(AT.makeIdeConstant("satisfying-assignment")),listVal res])
                                               val elem_2 = listVal([termVal(AT.makeIdeConstant("unsatisfied-assertions")),listVal(map termVal unsat_assertions)])
                                           in
                                              listVal([elem_1,elem_2])
                                           end
                                      else listVal(getModel'([]))
                                    end
                   | _ => listVal(getModel'([])))
     | _ => termVal(AT.makeIdeConstant("unknown")))
  end


fun processCVCOutput(stream:TextIO.instream,conjuncts,simplify_on,
                     tables as {domain_stream:TextIO.outstream, dec_stream: TextIO.outstream,
                                main_stream: TextIO.outstream, sel_counter:int ref,fsym_counter:int ref,dom_counter:int ref,var_counter: int ref, 
                                var_table: string AthTermVar.htable,inverse_var_table: (string,ATV.ath_term_var) HashTable.hash_table, 
                                fsym_table: string ModSymbol.htable, inverse_fsym_table: (string,ModSymbol.mod_symbol) HashTable.hash_table, 
                                domain_table: (string,string) HashTable.hash_table,inverse_domain_table: (string,string) HashTable.hash_table},id_table_opt) = 
  let fun debugPrint(s) = ()
      (** Define the above as print(s) and uncomment below occurrences for debugging **)
      val (no_id_table,id_table) = (case id_table_opt of
                                       SOME(table) => (false,table)
                                     | _ => (true,HashTable.mkTable(SemanticValues.hashVal, valEq) (5,Data.GenEx("Failed table creation"))))
      fun addCode(msym,str) = let val msym_str = MLStringToAthString(MS.name(msym))
	                      in
			         (HashTable.insert id_table (msym_str,MLStringToAthString(str)))
			       end
      fun refreshIdTable(term_val_1,term_val_2) =
             (case (HashTable.find id_table term_val_1) of
                 SOME(listVal(vals)) => (HashTable.insert id_table (term_val_1,listVal(term_val_2::vals)))
               | _ => (HashTable.insert id_table (term_val_1,listVal([term_val_2]))))
      fun getLine() = Basic.getBalancedLine(stream)
      fun isIntNum(t) = (case AT.isNumConstantOpt(t) of
                            SOME(A.int_num(_)) => true
                          | _ => false)
      fun skipable(left,right) = let fun f((#"L")::(#"E")::(#"T")::_) = true
                                       | f((#"L")::(#"A")::(#"M")::(#"B")::(#"D")::(#"A")::_) = true
                                       | f(_) = false
                                 in 
                                    f(left) orelse f(right) 
                                 end
      fun rationalToReal(n,d) = 
             let val n' = (case Real.fromString(n^".0") of 
                             SOME(r) => r)
                 val d' = (case Real.fromString(d) of
                              SOME(r) => r)
                 val r = Real./(n',d')
             in 
                AT.makeNumTerm(A.real_num(r,ref (A.convertRealStr(Real.toString(r)))))
             end
      fun getVal(clist) = 
           let val str = implode(clist)
               val num_opt = (case AbstractSyntax.getAthNumber(str) of
                                SOME(anum) => SOME(AT.makeNumTerm(anum))
                              | _ => if String.sub(str,0) = #"-" then 
                                       (case AbstractSyntax.getAthNumber(String.substring(str,1,String.size(str) - 1)) of
                                           SOME(anum) => SOME(AT.makeApp(Names.msubtraction_symbol,[AT.makeNumTerm(anum)]))
                                         | _ => NONE)
                                     else NONE)
           in
              (case num_opt of
                  SOME(t) => t
                | _ => let val (is_neg,str) = if hd(clist) = #"-" then (true,implode(tl(clist))) else (false,str)
                       in
                         (case (String.tokens (fn c => c = #"/") str) of
                             [n,d] => if is_neg then AT.makeApp(Names.msubtraction_symbol,[rationalToReal(n,d)])
                                      else rationalToReal(n,d)
                           | _ => let (* val _ = debugPrint("\nAbout to call make constant on this str: " ^ str) *)
                                      val res = AT.makeConstant(A.makeMS(str,NONE))
                                      (* val _ = debugPrint("\nAnd the result: " ^ (AT.toStringDefault(res)))    *)
                                  in
                                     res
                                   end)
                       end)
           end
      val cvc_numerals = ref []
      val first_line = getLine()
      fun makeTerm(fsym,args) = let val fsym_name = (MS.name(fsym))
                                in
				   (applyTermConstructorNoPos(fsym,args)) handle _ => AT.makeVar(ATV.fresh())
				end
      fun parseTerm(clist,cvc_numerals) = 
            let fun getFunctor(clist,res) = 
                       (case clist of
                           #" "::more => (rev res,more)
                         | #"\n"::more => (rev res,more)
                         | #"("::more => (rev res,clist)
                         | #")"::more => (rev res,clist)
                         | #","::more => (rev res,clist)
                         | #";"::more => (rev res,clist)
                         | #"]"::more => (rev res,clist)
                         | #"["::more => (rev res,clist)
                         | c::more => getFunctor(more,c::res)
                         | [] => (rev res,[]))
                fun getTerm(clist) = 
                  let val clist = Basic.skipWhiteSpace(clist)
                   (* val _ = debugPrint("\nCalling getTerm on this clist: "^(implode clist))  *)
                  in
                     (case clist of
                        #"f"::more => let val (fsym_clist,#"("::rest) = getFunctor(clist,[])
                                       (* val _ = debugPrint("\nfsym_clist: "^(implode fsym_clist)) *)
                                          val fsym_str = implode(fsym_clist)
                                          val toks = String.tokens (fn c => c = #"_") fsym_str 
                                          val fsym_sym = (case fsym_clist of 
                                                             (#"m")::(#"o")::(#"d")::[] => Names.mmodulo_symbol
                                                           | (#"d")::(#"i")::(#"v")::[] => Names.mdivision_symbol
                                                           | _ => (case (HashTable.find inverse_fsym_table (hd toks)) of
                                                                      SOME(f) => f
                                                                   | _ => (print("\nCould not find an inverse function for this symbol: " ^ (hd toks)); raise Basic.Never)))
                                       (* val _ = debugPrint("\nProper (non-constant) term-app functor: "^(MS.name(fsym_sym))^"\n") *)
                                      in
                                        (case (let val res = getTerms(rest,[])
                                              in
                                                 res
                                              end) of
                                            (args,rest') =>
                                              let (* val _ = debugPrint("\nGot the following args: " ^ (Basic.printListStr(args,AT.toStringDefault,",")))
                                                     val _ = debugPrint("\nAnd this remainder: " ^ (implode rest'))
						  *)
                                              in
                                              (case fsym_clist of
                                                (full_vname as ((#"v")::rest)) => 
                                                                let val var_name = implode full_vname
                                                                    val v = ATV.athTermVar(var_name)
                                                                    val vterm = (case (HashTable.find inverse_var_table var_name) of 
                                                                                    SOME(v') => AT.makeVar(v')
                                                                                  | _ => AT.makeVar(v))
                                                                in  
                                                                   (makeTerm(mfmap_apply_symbol,[vterm,hd args]),rest')
                                                                end 
                                               | _ => (makeTerm(fsym_sym,args),rest'))
                                              end)
                                      end
                      | #"("::more => let val (fsym_clist,rest) = getFunctor(more,[])  (** Must be a rational number of the form "(x/y)" **)
                                       (* val _ = debugPrint("\nGot this rational? char list: " ^ (implode fsym_clist) ^ " with remainder: " ^ (implode rest)) *)
                                          val res = (getVal(fsym_clist),tl rest)
                                      in
                                         res
                                      end
                      | _ => let val (fsym_clist,rest) = getFunctor(clist,[])
                                 val fsym_clist' = tl fsym_clist
                                 val fsym_str = implode fsym_clist'
                                 val fsc = (implode fsym_clist)
                                 val (fsym_sym,already_exists) = 
                                               (case (HashTable.find inverse_fsym_table fsc) of
                                                   SOME(f) => (f,true)
                                                 | _ => (A.makeMS(fsym_str,NONE),false))
                             in
                                (case fsym_clist of
                                    #"f"::rest' => if fsym_str = "alse" then (AT.false_term,rest)
                                                   else (makeTerm(fsym_sym,[]),rest)
                                  | #"v"::_ =>  let val var_name = fsym_str
                                                    val full_var_name = "v"^var_name
                                                 (* val _ = debugPrint("\nvar_name: "^var_name) *)
                                                    val v = ATV.athTermVar(fsym_str)
                                                 (* val _ = debugPrint("\nVariable made...")    *)
                                                in
                                                   (case (HashTable.find inverse_var_table full_var_name) of
                                                       SOME(v') => (AT.makeVar(v'),rest)
                                                     | _ => (AT.makeVar(v),rest))
                                                end

                                  | #"u"::_ =>  let val var_name = fsc
                                                 (* val _ = debugPrint("\nvar_name: "^var_name)    *)
                                                    val v = ATV.athTermVar(var_name)
                                                 (* val _ = debugPrint("\nFresh variable made...") *)
                                                in
                                                   (AT.makeVar(v),rest)
                                                end
                                  | #"'"::_ =>  (AT.makeIdeConstant(fsym_str),rest)
                                  | _ => if already_exists then (AT.makeConstant(fsym_sym),rest)
                                         else 
                                           (getVal(fsym_clist),rest))
                             end)
                  end
                and getTerms([],results) = (rev results,[])
                  | getTerms(#")"::more,results) = (rev results,more)
                  | getTerms(clist,results) = 
                            (case getTerm(clist) of
                                (t,#","::(#" ")::rest) => getTerms(rest,t::results)
                              | (t,#","::rest) => getTerms(rest,t::results)
                              | (t,rest as (_::_)) => getTerms(rest,t::results)
                              | (t,[]) => (rev (t::results),[]))
            in
               getTerm clist
            end 
    fun makeNewIdentity(left,right) = 
            let val var_sort = AT.getSort(left)
                val ynt_str = "fresh-"^(Basic.toLower (F.toOneStringDefault var_sort))^"-"^(AT.toStringDefault(right))
                val ynt = ATV.athTermVarWithSort(ynt_str,var_sort)
                val new_right = AT.makeVar(ynt)
                val _ = cvc_numerals := ynt::(!cvc_numerals)
                val res = makeTerm(Names.mequal_logical_symbol,[left,new_right])
            in
               (res,new_right)
            end
      val all_var_table_items = ref(NONE)
      fun getVarTableItems() = (case (!all_var_table_items) of
                                    NONE => let val res = ATV.listItemsi(var_table)
                                                val _ = all_var_table_items := SOME(res)
                                            in
                                              res
                                            end
                                   | SOME(res) => res)
      fun isNonIntVar(left) =
            (case AT.isVarOpt(left) of
                SOME(v) => (case (Basic.constructiveExists(getVarTableItems(),fn (v',_) => ATV.nameEq(v,v'))) of
                               SOME(v',_) => AT.makeVar(v')
                             | _ => left))
      fun ridType(chars) =
           (case Basic.skipUntil(chars,fn c => c = #":") of
	       ([],_) => implode(chars)
	     | (_,[]) => implode(chars)
	     | (arg_chars,rest) => implode(rev(arg_chars)))
      fun extractArgs0(chars,results) =
            (case Basic.skipUntil(chars,fn c => (c = #"," orelse c = #")")) of 
	        (arg_chars,#","::rest) => extractArgs0(Basic.skipWhiteSpace(rest),ridType(rev(arg_chars))::results)
              | (arg_chars,(#")")::(#":")::rest) => let val results' = rev(ridType(rev(arg_chars))::results)
	                                            in
						       (results',Basic.skipWhiteSpace(rest))
						    end)
      fun extractArgs(chars) =
            (case extractArgs0(chars,[]) of
	       (args,rest) => let val T = HashTable.mkTable(Basic.hashString, op=) (100,Basic.Never)
	                          fun loop([],_) = ()
				    | loop(arg::rest,i) = let val _ = (HashTable.insert T (arg,i))
				                          in loop(rest,i+1) end
                                   val _ = loop(args,1)							  
	                          fun argOrd(s) = (case (HashTable.find T s) of
				                     SOME(index) => index)
                              in
			         (args,argOrd,rest)
			      end)
      fun getGuard(chars) = ("",chars)			      
      fun extractGuards(chars,args,ithArg,whichArg) = raise Basic.Never
      fun getEqualitiesFromLambda(chars) =
            (case Basic.skipUntil(chars,fn c => c = #"=") of
	      (_,chars) =>
                (case Basic.skipWhiteSpace(tl(chars)) of
  	          (#"(")::(#"L")::(#"A")::(#"M")::(#"B")::(#"D")::(#"A")::(#"(")::rest =>
	                 let val (args,argOrd,rest) = extractArgs(rest)
			     fun display([]) = ()
			       | display(arg::rest) = let val index = argOrd(arg)
			                                  val _ = print("\nArgument " ^ arg ^ " has index: " ^ (Int.toString(index)))
			  	 	  	      in
						         display(rest)
						      end
			     val arity = length(args)
			     val ithArg = (fn i => Basic.nth(args,i-1))
			 in
			     (case extractGuards(rest,args,ithArg,argOrd) of
			        (eqns,#")"::_) => eqns
			      | _ => [])
			 end))
      fun makeGuardEquality(fsym_chars,arg_chars,args,ithArg,argOrd) =
            let val (s1,s2) = (implode(fsym_chars),implode(arg_chars))
	        val (arg,other) = if Basic.isMember(s1,args) then (s1,s2) else (s2,s1)
   		val other = if (hd(explode(other)) = #"f") then
               	             (case (HashTable.find inverse_fsym_table other) of
		                 SOME(msym) => let val res = MS.name(msym)
				               in
					          res
					       end
			       | _ => let val pairs = HashTable.listItemsi inverse_fsym_table
					  val table_str = Basic.printListStr(pairs,fn (str,msym) => "\n" ^ str ^ " --> " ^ (MS.name msym),"\n")
			                  val _ = print("\nAnd here's the fsym_table:\nSTART\n" ^ table_str ^ "\nEND\n")
			              in
				        other
				      end)
		            else other
            in
	       "(equal? " ^ arg ^ " " ^ other ^ ")"
	    end
      fun getGuardExpression((#"(")::(chars as (#"f")::rest),args,ithArg,argOrd) =
            (case Basic.skipUntil(chars,fn c => c = #"(") of
              (sym_chars,(#"(")::(#")")::rest) =>
                (case Basic.skipUntil(rest,fn c => c = #"=") of
		   (_,(#"=")::rest) => (case Basic.skipUntil(Basic.skipWhiteSpace(rest),fn c => c = #")") of
		                          (arg_chars,(#")")::rest) => (makeGuardEquality(rev(sym_chars),rev(arg_chars),args,ithArg,argOrd),Basic.skipWhiteSpace(rest)))))
        | getGuardExpression((#"(")::(chars as c::rest),args,ithArg,argOrd) =
 	    (case Basic.skipUntil(chars,fn c => c = #"=") of
	        (arg_chars,(#"=")::rest) =>
		   (case Basic.skipUntil(Basic.skipWhiteSpace(rest),fn c => c = #")") of
		       (fsym_chars,(#")")::rest) =>
		          (makeGuardEquality(rev(fsym_chars),rev(arg_chars),args,ithArg,argOrd),Basic.skipWhiteSpace(rest))))
      fun makeCheckExp(guard_exp,pos_clause,neg_clause) = "(check (" ^ guard_exp ^ " " ^ pos_clause ^ ") (else " ^ neg_clause ^"))" 	   
      fun getExpression(chars as ((#"I")::(#"F")::rest),args,ithArg,argOrd) =
             (case getGuardExpression(Basic.skipWhiteSpace(rest),args,ithArg,argOrd) of
	         (guard_exp,(#"T")::(#"H")::(#"E")::(#"N")::rest) =>
                    (case getExpression(Basic.skipWhiteSpace(rest),args,ithArg,argOrd) of
		        (pos_clause,(#"E")::(#"L")::(#"S")::(#"E")::rest) =>
			   (case getExpression(Basic.skipWhiteSpace(rest),args,ithArg,argOrd) of
			      (neg_clause,(#"E")::(#"N")::(#"D")::(#"I")::(#"F")::rest) =>
			         (makeCheckExp(guard_exp,pos_clause,neg_clause),Basic.skipWhiteSpace(rest)))))
        | getExpression(chars as ((#"f")::rest),args,ithArg,argOrd) =
	     (case Basic.skipUntil(chars,fn c => c = #"(") of
	       (sym_chars,(#"(")::(#")")::rest) =>
	         (case (HashTable.find inverse_fsym_table (implode(rev(sym_chars)))) of
		     SOME(msym) => (MS.name(msym),Basic.skipWhiteSpace(rest))
		   | _ => (print("\nCould not find a symbol for this key: " ^ (implode(rev(sym_chars))));raise Basic.Never)))
        | getExpression(chars as (c::rest),args,ithArg,argOrd) =
	       if Char.isDigit(c) then
	          (case Basic.skipUntil(chars,fn c => not(c = #".") andalso not(Char.isDigit(c))) of
		      (digits,rest) => (implode(digits),Basic.skipWhiteSpace(rest)))
               else
	          (case Basic.skipUntil(chars,fn c => c = #" ") of
		     (letters,rest) => let val s = implode(rev(letters))
		                           val rest = Basic.skipWhiteSpace(rest)
					   val result as (s,rest) = if (s = "TRUE") then ("true",rest) else if (s = "FALSE") then ("false",rest) else ("",rest)
					   val got_result = not(s = "")
					   val result as (s,rest) =
					         if got_result then result
					         else ((getGuardExpression(Basic.skipWhiteSpace(chars),args,ithArg,argOrd)) handle _ => ("",rest))
		                       in
                                          if s = "" then (print("\nERROR: Don't know how to handle this constant prim exp: " ^ (implode chars)); raise Basic.Never)
					  else result 
				       end)
      fun getCodeFromLambda(chars) =
            (case Basic.skipUntil(chars,fn c => c = #"=") of
	      (_,chars) =>
                (case Basic.skipWhiteSpace(tl(chars)) of
  	          (#"(")::(#"L")::(#"A")::(#"M")::(#"B")::(#"D")::(#"A")::(#"(")::rest =>
	                 let val (args,argOrd,rest) = extractArgs(rest)
			     val prefix = "(lambda (" ^ (Basic.printListStr(args,fn x => x," ")) ^ ") "
			     val ithArg = (fn i => Basic.nth(args,i-1))
			 in
			     (case getExpression(rest,args,ithArg,argOrd) of
			        (body,#")"::_) => (prefix ^ body ^ ")")
			      | _ => "") 
			 end))
      fun getVar([],res) = (rev res,[])
        | getVar(c::more,res) = if Char.isDigit(c) then getVar(more,c::res) else (rev res,more)
      fun getModel(L) = 
            let val line = getLine()
                val line_chars = explode(line)
            in 
               (case line_chars of 
                   [] => L
                 | (#"f")::rest => let val (fsym_chars,rest) = getVar(rest,[])
                                       val fsym_str = implode (#"f"::fsym_chars)
				       val constant_term_opt = 
                                               (case (HashTable.find inverse_fsym_table fsym_str) of
                                                            SOME(ms) => let val ms_str = MS.name(ms)
									    val res = (if (String.sub(ms_str,0) = Names.metaIdPrefix_char) then
                                                                                         (SOME(AT.makeIdeConstant(String.substring(ms_str,1,String.size(ms_str)-1))),SOME(ms))
                                                                                      else 
                                                                                         (SOME(AT.makeConstant(ms)),SOME(ms))) handle _ => ((NONE,SOME(ms)))
                                                                        in
                                                                          res
                                                                        end
                                                      | _ => (NONE,NONE))
                                                                       
                                   in
                                    (case constant_term_opt of
                                      (SOME(constant_term),_) => 
                                        (case Basic.skipWhiteSpace(rest) of
                                           (#":")::rest' => let val (_,_::rest'') = Basic.skipUntil(rest',fn c => c = #"=")
                                                                val (term,line_remainder) = parseTerm(rest'',cvc_numerals)
                                                                val eqn = makeTerm(Names.mequal_logical_symbol,[constant_term,term])
                                                            in
                                                               getModel((propVal (Prop.makeAtom eqn))::L)
                                                            end)
                                    | (NONE,SOME(fsym)) => let val code = getCodeFromLambda(rest)
							       val _ = addCode(fsym,code)
                                                               in
	  	  	   		                         getModel(L)
					                       end)
                                   end
                 | (#"v")::rest => let val (var_chars,rest) = getVar(rest,[])
                                       val var_str = implode (#"v"::var_chars)
                                       val var = (case (HashTable.find inverse_var_table var_str) of
                                                     SOME(v) => v
                                                  | _ => (print("\nCould not find a variable in the inverse table for this: " ^ var_str ^ "\n");raise Basic.Never))
                                       val avar = AT.makeVar(var)						  
                                   in
                                      (case Basic.skipWhiteSpace(rest) of
                                         (#":")::rest' => let val (_,_::rest'') = Basic.skipUntil(rest',fn c => c = #"=")
                                                              val (term,line_remainder) = parseTerm(rest'',cvc_numerals)
                                                              val eqn = makeTerm(Names.mequal_logical_symbol,[avar,term])
                                                          in
                                                             getModel((propVal (Prop.makeAtom eqn))::L)
                                                          end)
                                   end
                 | (#"(")::(#"=")::(#" ")::rest => 
                     let val (left,rest') = parseTerm(rest,cvc_numerals)
                      (* val _ = debugPrint("\nLeft term: "^(AT.toStringDefault(left)))       *)
                         val (right,#")"::_) = parseTerm(Basic.skipWhiteSpace rest',cvc_numerals)
                      (* val _ = debugPrint("\nAnd right term: "^(AT.toStringDefault(right))) *)
                         val _ = raise Basic.Never
                         val (identity,right') = 
                                     (((makeTerm(Names.mequal_logical_symbol,[left,right]),right)
                                          handle _ => (if isIntNum(right) then makeNewIdentity(left,right)
                                                       else Basic.fail("\nSMT translation error.\n"))))
                         val identity' = if AT.isVar(right) andalso not(AT.isVar(left)) then
                                           makeTerm(Names.mequal_logical_symbol,[right,left])
                                         else identity
                         val identity = identity'
                     in
                       if AT.termEq(left,right) then getModel(L)
                       else (if (AT.isGround(identity) andalso Basic.isMemberEq(Prop.makeEquality(left,right'),conjuncts,Prop.alEq)) then
                                getModel(L) else getModel((propVal (Prop.makeAtom identity)::L)))
                     end
                 | _ => getModel(L)) handle _ => getModel(L)
            end
      fun allDistinct(terms) = let fun negateOne(s,terms) = 
                                           let fun loop([],res) = res
                                                 | loop(t::more,res) = let val res' = ((propVal(Prop.makeNegation(Prop.makeEquality(s,t))))::res)  handle _ => res
                                                                       in
                                                                          loop(more,res')
                                                                       end
                                           in
                                               loop(terms,[])
                                           end
                                   fun loop([],res) = res
                                     | loop(t::more,res) = loop(more,(negateOne(t,more))@res)
                               in
                                  loop(terms,[])
                               end
      fun isInputLeaf(x) = Basic.exists(conjuncts,fn c => (case Prop.isAtom(c) of 
                                                              SOME(t) => Basic.isMemberEq(x,AT.leaves(t),AT.termEq)
                                                            | _ => false))
      fun isFreshVariable(t) = (case AT.isVarOpt(t) of
                                   SOME(v) => let val str = ATV.name(v) 
                                              in
                                                if String.size(str) >= 6 andalso String.substring(str,0,6) = "fresh-" 
                                                then SOME(v) else NONE
                                              end
                                 | _ => NONE)
      fun simplify(propVal(eqn),model:value list)  = 
             (case Prop.isEquality(eqn) of
                 SOME(l,r) => (case isFreshVariable(r) of 
                                  SOME(v) => if isInputLeaf(l) then 
                                               (true,map (fn propVal(p) => propVal(Prop.replace(v,l,p))) model)
                                             else (false,model)
                                 | _ => (false,model))
               | _ => (false,model))
      fun simplifyModel(L) = 
              let fun loop([],latest_model) = latest_model
                    | loop(eqn::more,latest_model) = 
                         let val (has_change,model) = simplify(eqn,latest_model)
                         in
                            if has_change then loop(more,model)
                             else loop(more,latest_model)
                         end
                  fun removeTautologies(L) = 
                         Basic.filterOut(L,fn propVal(id) => (case Prop.isEquality(id) of
                                                                 SOME(l,r) => let val (lv,rv) = (termVal(l),termVal(r))
								                  val cond = AT.termEq(l,r)
                                                                                  val _ = if cond orelse no_id_table then () 
                                                                                          else (refreshIdTable(lv,rv);
                                                                                                if AT.isVar(l) orelse AT.isNumConstant(r) then () else  
                                                                                                (refreshIdTable(rv,lv)))
                                                                              in
                                                                                if no_id_table then cond else true
                                                                              end
                                                               | _ => Basic.fail("SMT translation error: identity expected here.")))
                  fun removeRedundancies(L) = 
                         Basic.filterOut(L,fn propVal(id) => (case Prop.isEquality(id) of
                                                                 SOME(l,r) => let val (lv,rv) = (termVal(l),termVal(r))
                                                                                  val cond = ((Basic.isMemberEq(id,conjuncts,Prop.alEq) andalso not(AT.isVar(l))) 
                                                                                             orelse AT.termEq(l,r))
                                                                                  val _ = if cond orelse no_id_table then () 
                                                                                          else (refreshIdTable(lv,rv);
                                                                                                if AT.isVar(l) orelse AT.isNumConstant(r) then () else  
                                                                                               (refreshIdTable(rv,lv)))
                                                                              in 
                                                                                 if no_id_table then cond else true                                                                     
                                                                              end
                                                               | _ => Basic.fail("SMT translation error: identity expected here.")))
              in
                 if simplify_on then removeRedundancies(loop(L,L))
                 else removeTautologies(loop(L,L))
              end
      fun getUnSatAssertions(clist) = 
             let fun loop(clist,res) = (case (Basic.skipWhiteSpace(clist)) of
                                          [] => res
                                        | clist' => (case parseTerm(clist',cvc_numerals) of
                                                       (n,rest) => loop(rest,n::res)))
              in 
                 loop(clist,[])
              end
      fun getModel'(L) =
            (case getModel(L) of
               bindings => (case Basic.removeDuplicatesEq(!cvc_numerals,ATV.athTermVarEq) of
                               [] => (simplifyModel(bindings))
                             | ynterms => let val vars = (List.map AT.makeVar ynterms)
                                              val L2 = allDistinct vars
                                              val L1 = simplifyModel(bindings)
                                              val res = L1@L2
                                          in res end))
  in
    (case (explode first_line) of
       (#"u")::(#"n")::(#"s")::(#"a")::(#"t")::_ => (termVal(AT.makeIdeConstant("Unsatisfiable")))
     | (#"E")::(#"r")::(#"r")::(#"o")::(#"r")::_ => (termVal(AT.makeIdeConstant("Unknown-error")))
     | (#"u")::(#"n")::(#"k")::(#"n")::(#"o")::(#"w")::(#"n")::_ => 
          ((listVal([termVal(AT.makeIdeConstant("unknown")),listVal(getModel'([]))]))
             handle _ => termVal(AT.makeIdeConstant("unknown")))
     | (#"s")::(#"a")::(#"t")::_ => listVal(getModel'([]))
     | _ => termVal(AT.makeIdeConstant("unknown")))
  end

fun yicesWriteDefsFun([listVal(def_vals),listVal(prop_vals),file_val,file_extension_val],env,_) = 
  (let val (file_name,file_extension) = 
                   (case (isStringValConstructive(file_val),isStringValConstructive(file_extension_val)) of
                         (SOME(str1),SOME(str2)) => (str1,str2))
      val props = Semantics.getProps(prop_vals,"the argument list given to "^"yices-write-defs",env)
      fun getDef(listVal([termVal(t),propVal(p)])) = (t,p)
        | getDef(listVal([tv,v])) = 
             (case coerceValIntoTerm(tv) of
                   SOME(t) => (case coerceValIntoProp(v) of
                                 SOME(p) => (t,p)
                               | _ => primError("\nWrong sort of value given as second element of definition: "^(prettyValToString v)^"\n")))
      val defs: (AT.term * P.prop) list = map getDef def_vals 
      val _ = Prop.writeSMTDefs(defs,file_name,file_extension)
  in
     unitVal 
  end)

end (** Of structure SMTOutput **)