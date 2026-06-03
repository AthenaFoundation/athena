(*======================================================================

A structure for symbolic terms. 

=======================================================================*)

structure SymTerm: TERM = 

struct 

type variable = Symbol.symbol;

type fsymbol = ModSymbol.mod_symbol

datatype label = varLabel of variable | fsymLabel of fsymbol | noLabel;

val varEq = Symbol.symEq;

val fsymEq = ModSymbol.modSymEq;

exception Subterm

abstype term = Var of variable | App of fsymbol * term list
with

     fun termEq(Var(v),Var(v')) = varEq(v,v') 
       | termEq(App(f,terms1),App(g,terms2)) = fsymEq(f,g) andalso termEqLst(terms1,terms2)
       | termEq(_,_) = false
       and
         termEqLst([],[]) = true
      | termEqLst(t1::rest1,t2::rest2) = termEq(t1,t2) andalso termEqLst(rest1,rest2)
       | termEqLst(_,_) = false;

     infix ==;

     fun t1 == t2 = termEq(t1,t2);

     fun makeVar(v) = Var(v);

     fun makeConstant(c) = App(c,[]);

     fun makeApp(f,term_list) = App(f,term_list);

     fun isVar(Var(v)) = SOME(v) 
       | isVar(_) = NONE;

     fun isConstant(App(f,[])) = SOME(f)
       | isConstant(_) = NONE;

     fun isApp(App(f,terms)) = SOME(f,terms)
       | isApp(_) = NONE;

     fun isGround(Var(_)) = false 
       | isGround(App(_,terms)) = areGround(terms)
       and areGround([]) = true
         | areGround(t::rest) = isGround(t) andalso areGround(rest);

     fun varOccursIn(v,Var(v')) = varEq(v,v')
       | varOccursIn(v,App(_,terms)) = Basic.exists(terms,fn t => varOccursIn(v,t))

     fun fsymOccursIn(f,App(g,args)) = fsymEq(f,g) orelse 
                                       Basic.exists(args,fn t => fsymOccursIn(f,t))
       | fsymOccursIn(f,_) = false;

     fun getNthSubterm(t,[]) = t
       | getNthSubterm(t as App(_,args),pos as i::rest) = 
           if i > 0 andalso i <= length(args) then 
              getNthSubterm(List.nth(args,i-1),rest)
           else raise Subterm
       | getNthSubterm(t,pos) = raise Subterm;

     fun isLegal(Var(v),_,isLegalVariable) = let val res = isLegalVariable v
					     in
						 res
					     end
       | isLegal(App(f,terms),arityOf,isLegalVariable) = 
             case arityOf(f) of
                SOME(n) => n = length(terms) andalso 
                           Basic.forall(terms,fn t => isLegal(t,arityOf,isLegalVariable))
              | NONE => false;
         
    fun areLegal(terms,arityOf,isLegalVariable) = 
          Basic.forall(terms,fn t => isLegal(t,arityOf,isLegalVariable))

     fun isLegalFlex(Var(v),_,isLegalVariable,_) = isLegalVariable v
       | isLegalFlex(App(f,terms),arityOf,isLegalVariable,flex_fun_name_msym) = 
             (case arityOf(f) of
                SOME(n) => n = length(terms) andalso 
                           Basic.forall(terms,fn t => isLegalFlex(t,arityOf,isLegalVariable,flex_fun_name_msym))
               (*** Treat the designated flex_fun_name_msym in a special way ***)
              | NONE => if ModSymbol.modSymEq(flex_fun_name_msym,f) then Basic.forall(terms,fn t => isLegalFlex(t,arityOf,isLegalVariable,flex_fun_name_msym)) else false)

    fun areLegalFlex(terms,arityOf,isLegalVariable,flex_fun_name_msym) = 
          Basic.forall(terms,fn t => isLegalFlex(t,arityOf,isLegalVariable,flex_fun_name_msym))

    fun getDom(t) = 
	let fun dom(Var(_)) = [[]] 
	      | dom(App(f,[])) = [[]]
	      | dom(App(f,args)) =  
	             let val doms = map dom args
	                 fun augment(dom,i) = map (fn lst => i::lst) dom
	                 fun makeNewDoms([],_,results) = results
	                   | makeNewDoms(dom::more,i,results) = 
	                         let val new_dom = augment(dom,i)
	                             in
	                                makeNewDoms(more,i+1,new_dom@results)
	                         end
	                 in
	                   []::makeNewDoms(doms,1,[])
	             end
            in
              rev(dom t)
       end;

     fun getFDom(t) = List.filter (fn path => (case isVar(getNthSubterm(t,path)) of
                                                    NONE => true | _ => false)) (getDom(t));


     fun getVDom(t) = List.filter (fn path => (case isApp(getNthSubterm(t,path)) of
                                                    NONE => true | _ => false)) (getDom(t));

     fun getLabel(t,pos) = 
           let val sub_term = SOME(getNthSubterm(t,pos)) handle Subterm => NONE
               in
                  (case sub_term of
                      SOME(t') => 
                          (case isApp(t') of
                              SOME(fsym,_) => fsymLabel(fsym)
                            | _ => (case isVar(t') of 
                                       SOME(v) => varLabel(v)
                                     | _ => raise Basic.Never))
                    | _ => noLabel)
           end;

     val (getVars,getVarsLst) = 
         let fun isMember(v,[]) = false
               | isMember(v,v'::rest) = if varEq(v,v') then true else isMember(v,rest);
             fun gleanVars(Var(v),lst) = if isMember(v,lst) then lst else v::lst
               | gleanVars(App(_,terms),lst) = gleanVarsLst(terms,lst)
               and
                 gleanVarsLst([],lst) = lst
               | gleanVarsLst(t::rest,lst) = gleanVars(t,lst)@gleanVarsLst(rest,lst)
             in
                (fn t => gleanVars(t,[]), fn terms => gleanVarsLst(terms,[]))
         end

     type sub = variable -> term;

     val empty_sub = fn v => Var(v);

     fun inSupp(v,sub:sub) = not (sub(v) == Var(v));

     fun incSub(sub,(v,t)) = fn var => if varEq(var,v) then t else sub(var);

     infix ++;

     fun sub ++ (v,t) = incSub(sub,(v,t));

     fun extendSub(sub,[]) = sub |
         extendSub(sub,(v,t)::rest) = extendSub(sub++(v,t),rest);


     fun makeSub(pairs) = extendSub(empty_sub,pairs);

     fun applySub(sub,Var(v)) = sub(v) 
       | applySub(sub,App(f,terms)) = App(f,map (fn t => applySub(sub,t)) terms);
     
     fun applySubLst(sub,lst) = map (fn t => applySub(sub,t)) lst;
     
     fun composeSubs(sub2,sub1:sub) = fn v:variable => applySub(sub2,sub1(v));


     fun replace(v,t1,t2) = let val unit_sub = makeSub([(v,t1)])
                                in
                                  applySub(unit_sub,t2)
                            end;

     fun replaceSubterm(t,[],new_part) = new_part
       | replaceSubterm(App(f,args),i::rest,new_part) = 
            if (0 < i) andalso (i <= length(args)) then
               let val t = replaceSubterm(List.nth(args,i-1),rest,new_part)
                   in
                     App(f,List.take(args,i-1)@[t]@List.drop(args,i))
               end
            else
               raise Subterm
       | replaceSubterm(_,_,_) = raise Subterm;


     fun match(_,_) = NONE;

     fun unify(s as Var(v),t) = if varOccursIn(v,t) then
                                    if t == s then SOME(empty_sub)
                                    else NONE
                                 else
                                    SOME(makeSub([(v,t)]))
       | unify(s,t as Var(_)) = unify(t,s)
       | unify(App(f,terms1),App(g,terms2)) = if fsymEq(f,g) then unifyLst(terms1,terms2) else NONE
       and
         unifyLst([],[]) = SOME(empty_sub)
       | unifyLst(t1::rest1,t2::rest2) = 
            (case unify(t1,t2) of
                SOME(sub) => let val new_rest1 = map (fn t => applySub(sub,t)) rest1
                                  val new_rest2 = map (fn t => applySub(sub,t)) rest2
                                  in
                                    (case unifyLst(new_rest1,new_rest2) of
                                        SOME(sub') => SOME(composeSubs(sub',sub))
                                      | _ => NONE)
                              end
              | _ => NONE)
       | unifyLst(_,_) = NONE;     

     exception UniFailure;

     val (unifyEx,unifyExLst) = 
             let fun U(s as Var(v),t) = if varOccursIn(v,t) then
                                           if t == s then empty_sub
                                           else raise UniFailure
                                        else
                                           makeSub([(v,t)])
                  | U(s,t as Var(_)) = U(t,s)
                  | U(App(f,terms1),App(g,terms2)) = if fsymEq(f,g) then ULst(terms1,terms2) 
                                                     else raise UniFailure
                  and
                    ULst([],[]) = empty_sub
                  | ULst(t1::rest1,t2::rest2) = 
                       let val sub = U(t1,t2)
                           val (new_rest1,new_rest2) = (applySubLst(sub,rest1),applySubLst(sub,rest2))
                           val sub' = ULst(new_rest1,new_rest2)
                           in
                             composeSubs(sub',sub)
                       end
                  | ULst(_,_) = raise UniFailure
                 in
                   (fn (s,t) => U(s,t), fn (slist,tlist) => ULst(slist,tlist))
             end


     fun height(App(f,args)) = 1 + Basic.maxLst(map height args)
       | height(_) = 0;

     fun toString(Var v,printVarSort) = printVarSort v
       | toString(App(f,[]),_) = ModSymbol.name(f)
       | toString(App(f,args),printVarSort) = 
		"("^ModSymbol.name(f)^" "^(Basic.printSExpListStr(args,fn t => toString(t,printVarSort)))^")";

     fun toStringDefault(Var v) = Symbol.name(v)
       | toStringDefault(App(f,[])) = ModSymbol.name(f)
       | toStringDefault(App(f,args)) = 
		"("^ModSymbol.name(f)^" "^(Basic.printSExpListStr(args,fn t => toStringDefault(t)))^")";


fun toPrettyString(start,t,printVar) = 
       let fun pp(_,Var(v)) = printVar v
             | pp(_,App(f,[])) = ModSymbol.name(f)
             | pp(s,App(f,args)) = 
		 	let val str = ModSymbol.name(f)
                            val break_up = List.exists (fn t => height(t) > 0) args
                        in
                           "("^str^" "^ppArgs(s+String.size(str)+2,args,break_up)^")" 
                        end 
          and ppArgs(s,args,false) = Basic.printSExpListStr(args,fn t => toString(t,printVar))
            | ppArgs(s,args,true) = doArgs(s,args)
          and doArgs(s,[]) = ""
            | doArgs(s,[t]) = pp(s,t)
            | doArgs(s,t1::t2::more) = pp(s,t1)^Basic.new_line^Basic.spaces(s)^doArgs(s,t2::more)
       in
          pp(start,t)
       end;

fun getOccurences(t1,t2) = 
    let val t2dom = getDom(t2)
        fun test(pos) = termEq(t1,getNthSubterm(t2,pos))
        in
          (List.filter test t2dom)
    end


fun toJson(t as Var(v)) = 
    JSON.OBJECT([("type", JSON.STRING("symTerm")),
	   	 ("subtype", JSON.STRING("variable")),
	  	 ("root", JSON.STRING(Symbol.name v)),
	  	 ("children", JSON.ARRAY([]))])
  | toJson(t as App(f,terms)) = 
    JSON.OBJECT([("type", JSON.STRING("symTerm")),
	   	 ("subtype", JSON.STRING("app")),
	  	 ("root", JSON.STRING(ModSymbol.name f)),
	  	 ("children", JSON.ARRAY(map toJson terms))])

end; (**  of "abstype term with..."  **)


abstype 'a tagged_term = Var of variable * 'a | App of fsymbol * 'a * (('a tagged_term) list)
with

     fun transform _ (t as Var(_))  = t
       | transform fsymTransformer (App(f,tag,args))  = App(fsymTransformer(f),tag,map (transform fsymTransformer) args)

     fun taggedTermToString(Var(v,_)) = Symbol.name(v)
       | taggedTermToString(App(f,_,[])) = ModSymbol.name(f)
       | taggedTermToString(App(f,_,args)) = 
		"("^ModSymbol.name(f)^" "^(Basic.printSExpListStr(args,taggedTermToString))^")";

     fun isTaggedConstant(App(fsym,tag,[])) = SOME(fsym,tag)
       | isTaggedConstant(_) = NONE;

     fun fsymOccursInTagged(f,App(g,tag,args)) = fsymEq(f,g) orelse 
                                                 Basic.exists(args,fn t => fsymOccursInTagged(f,t))
       | fsymOccursInTagged(_,_) = false;

     fun isTaggedApp(App(fsym,tag,args)) = SOME(fsym,tag,args)
       | isTaggedApp(_) = NONE;

     fun isTaggedVar(Var(v,tag)) = SOME(v,tag)
       | isTaggedVar(_) = NONE;

     fun makeTaggedVar(v,tag) = Var(v,tag);

     fun makeTaggedConstant(c,tag) = App(c,tag,[]);

     fun makeTaggedApp(f,tag,term_list) = App(f,tag,term_list);

     fun getNthTaggedSubterm(s,[]) = s
       | getNthTaggedSubterm(App(_,_,args),i::rest) = 
           if i > 0 andalso i <= length(args) then 
              getNthTaggedSubterm(List.nth(args,i-1),rest)
           else raise Subterm 
       | getNthTaggedSubterm(_,_) = raise Subterm 

     fun getTopTag(Var(_,tag)) = tag
       | getTopTag(App(_,tag,_)) = tag;

     fun getTag(t,pos) = getTopTag(getNthTaggedSubterm(t,pos));
    
     fun stripTags(Var(v,_)) = makeVar(v)
       | stripTags(App(f,_,args)) = makeApp(f,map stripTags args);


    fun isTaggedLegal(t,arityOf,isLegalVariable) = 
        let fun check(Var(v,tag)) = if isLegalVariable(v) then NONE else SOME(tag)
              | check(App(f,tag,terms)) =
                     (case arityOf(f) of
                         SOME(n) => if not(n = length(terms)) then
                                       SOME(tag)
                                    else
                                       checkLst(terms)
                       | NONE => SOME(tag))
            and
                checkLst([]) = NONE 
              | checkLst(t::more) = (case check(t) of 
                                        NONE => checkLst(more)
                                      | r => r)
            in
              check(t)
        end                   

    fun isTaggedLegalFlex(t,arityOf,isLegalVariable,flex_fun_name_msym) = 
        let fun check(Var(v,tag)) = if isLegalVariable(v) then NONE else SOME(tag)
              | check(App(f,tag,terms)) =
                     (case arityOf(f) of
                         SOME(n) => if not(n = length(terms)) then
                                       SOME(tag)
                                    else
                                       checkLst(terms)
                       | NONE => if ModSymbol.modSymEq(flex_fun_name_msym,f) then checkLst(terms) else SOME(tag))
            and
                checkLst([]) = NONE 
              | checkLst(t::more) = (case check(t) of 
                                        NONE => checkLst(more)
                                      | r => r)
            in
              check(t)
        end                   

fun areTaggedLegal(terms,arityOf,isLegalVariable) =
      let fun  checkLst([]) = NONE
             | checkLst(t::more) = case isTaggedLegal(t,arityOf,isLegalVariable) of 
                                       NONE => checkLst(more)
                                     | r => r
          in
             checkLst(terms)    
      end


fun taggedTermToJson(t as Var(v,tag),tagToString) = 
    JSON.OBJECT([("type", JSON.STRING("symTerm")),
	   	 ("subtype", JSON.STRING("variable")),
	  	 ("root", JSON.STRING(Symbol.name v)),
		 ("tag",JSON.STRING(tagToString(tag))),
	  	 ("children", JSON.ARRAY([]))])
  | taggedTermToJson(t as App(f,tag,terms),tagToString) = 
    JSON.OBJECT([("type", JSON.STRING("symTerm")),
	   	 ("subtype", JSON.STRING("app")),
	  	 ("root", JSON.STRING(ModSymbol.name f)),
		 ("tag",JSON.STRING(tagToString(tag))),
	  	 ("children", JSON.ARRAY(map (fn t => taggedTermToJson(t,tagToString)) terms))])


end; (**  of "abstype tagged_term with..."  **)

end; (** of SymTerm struct **)
