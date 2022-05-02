structure PrologSolver = 

struct

structure ATV = AthTermVar;
structure AT = AthTerm;
structure MS = ModSymbol;
structure A = AbSyntax;
structure S = Symbol;
structure N = Names;
structure SV = SemanticValues;

(*  
   By default, return up to 1 million results for a given query.
   This can be adjusted downwards or upwards as desired: 
*)

val default_result_limit = 1000000;


(* 
    The standard initial size of all the various hash tables necessary
    for the Athena<-->Prolog communication:
*) 

val standard_init_size = 151;

val file_counter = ref(0);

val var_table: string ATV.htable = ATV.makeHTable()

val var_table': (string,ATV.ath_term_var) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (standard_init_size,Basic.Never);

val constant_table: string MS.htable = MS.makeHTableWithInitialSize(standard_init_size);

val constant_table': (string,MS.mod_symbol) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (standard_init_size,Basic.Never);

val fsym_table: string MS.htable = MS.makeHTableWithInitialSize(standard_init_size);

val predefined_functor_table: string MS.htable = MS.makeHTableWithInitialSize(standard_init_size);

val is_code = ref(0);
val double_equality_code = ref(0);
val double_inequality_code = ref(0);
val write_code = ref(0);
val prolog_var_code = ref(0);
val square_root_code = ref(0);
val bagof_code = ref(0);
val cut_code = ref(0);
val retract_code = ref(0);
val asserta_code = ref(0);
val assertz_code = ref(0);
val fail_code = ref(0);
val setof_code = ref(0);
val findall_code = ref(0);
val arith_eq_code = ref(0);
val arith_uneq_code = ref(0);
val call_code = ref(0);
val cons_code = ref(0);
val pair_code = ref(0);
val nil_code = ref(0);

val nil_fsym = ref(N.mtrue_logical_symbol);
val cons_fsym = ref(N.mtrue_logical_symbol);
val pair_fsym = ref(N.mtrue_logical_symbol);

val fsym_table': (string,MS.mod_symbol) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (standard_init_size,Basic.Never);

val (var_counter,constant_counter,fsym_counter) = (ref(0),ref(0),ref(0));

fun clearTables() = 
  (ATV.clearTable(var_table);HashTable.clear(var_table');MS.clearHTable(constant_table);HashTable.clear(constant_table');
   MS.clearHTable(fsym_table);HashTable.clear(fsym_table'));

fun makeFreshVar() = "V" ^ (Int.toString(Basic.incAndReturn(var_counter)));

fun makeFreshConstant() = "a" ^ (Int.toString(Basic.incAndReturn(constant_counter)));

fun makeFreshFunSym() = "h" ^ (Int.toString(Basic.incAndReturn(fsym_counter)));

fun prologLegal(str) = 
      let val len = String.size(str)
          fun loop(i) = if (i < len) then
                           let val c = String.sub(str,i)
                           in
                              if Char.isAlphaNum(c) orelse c = #"_" then loop(i+1) else false
                           end
                        else true 
      in
          if len > 0 andalso Char.isAlpha(String.sub(str,0)) then loop(1) else false
      end

fun makePrologConstant(t) = 
   (case AT.isNumConstant(t) of
       SOME(A.int_num(i,_)) => if i < 0 then "-" ^ (Int.toString (Int.abs i)) else (Int.toString (Int.abs i))
     | SOME(A.real_num(r,_)) => if r < 0.0 then "-" ^ (A.convertRealStr (Real.fmt (StringCvt.FIX NONE) (Real.abs r))) 
                                else (A.convertRealStr (Real.fmt (StringCvt.FIX NONE) (Real.abs r)))
     | _ => (case AT.isApp(t) of
                 SOME(root,_) => if MS.modSymEq(root,Names.mtrue_logical_symbol) then "true" 
                                 else if MS.modSymEq(root,Names.mfalse_logical_symbol) then "fail"  
                                 else let (* val code = MS.code(root) *)
                                          val str = MS.name(root)
                                      in   
				         (case MS.find(predefined_functor_table,root) of
                                             SOME(str') => str' 
(*************************
                                            if code = !cut_code then "!" 
                                            else if code = !fail_code then "fail"
                                            else if code = !nil_code then "[]"
                                            else 
**************************)
                                        | _ => if prologLegal(str) then ("c" ^ str)
                                               else (case MS.find(constant_table,root) of
                                                        SOME(str') => "k" ^ str'
                                                      | _ => let val str' = makeFreshConstant()
                                                                 val _ = MS.insert(constant_table,root,str')
                                                                 val _ = HashTable.insert constant_table' (str',root)
                                                             in
                                                               "k" ^ str'
                                                             end))
                                     end
               | _ => (case AT.isIdeConstant(t) of
                          SOME(str) => "\"" ^ str ^ "\"")));



fun makePrologConstant(t) = 
   (case AT.isNumConstant(t) of
       SOME(A.int_num(i,_)) => if i < 0 then "-" ^ (Int.toString (Int.abs i)) else (Int.toString (Int.abs i))
     | SOME(A.real_num(r,_)) => if r < 0.0 then "-" ^ (A.convertRealStr (Real.fmt (StringCvt.FIX NONE) (Real.abs r))) 
                                else (A.convertRealStr (Real.fmt (StringCvt.FIX NONE) (Real.abs r)))
     | _ => (case AT.isApp(t) of
                 SOME(root,_) => 
   	             (case MS.find(predefined_functor_table,root) of
                          SOME(str') => str' 
                        | _ => let val str = MS.name(root)
                               in
                                  if prologLegal(str) then ("c" ^ str)
                                  else (case MS.find(constant_table,root) of
                                           SOME(str') => "k" ^ str'
                                         | _ => let val str' = makeFreshConstant()
                                                    val _ = MS.insert(constant_table,root,str')
                                                    val _ = HashTable.insert constant_table' (str',root)
                                                in
                                                    "k" ^ str'
                                                end)
                               end)
              | _ => (case AT.isIdeConstant(t) of
                         SOME(str) => "\"" ^ str ^ "\"")));

fun isNumericOp(f) = let val c = MS.code(f) in c >= MS.code(Names.maddition_symbol) andalso c <= MS.code(Names.mformal_greater_symbol) end;

fun makePrologFunctor(f) = 
(****
   if isNumericOp(f) then MS.name(f) else 
   let (*** val code = MS.code(f)
            val last_name_str = S.name(MS.lastName(f))
       ***)
   in
***)  
      (case MS.find(predefined_functor_table,f) of
          SOME(str) => str
        | _ => let val str = MS.name(f) 
               in
                  if prologLegal(str) then "f" ^ str
                  else (case MS.find(fsym_table,f) of
                           SOME(str') => "g" ^ str'
                         | _ => let val str' = makeFreshFunSym()
                                    val _ = MS.insert(fsym_table,f,str')
                                    val _ = HashTable.insert fsym_table' (str',f)
                                in
                                  "g" ^ str' 
                                end)
               end);


fun strip(s) =   
   let val len = String.size(s)
   in
     if String.sub(s,0) = #"\"" andalso String.sub(s,len-1) = #"\"" then 
        String.substring(s,1,len-2)
     else s
   end;

fun makePrologTerm(t) = 
  (case AT.isVar(t) of
      SOME(v) => let val str = ATV.name(v) 
                 in
                    if prologLegal(str) then "X" ^ str
                    else (case ATV.find(var_table,v) of
                              SOME(str') => "Y" ^ str'
                            | _ => let val str' = makeFreshVar()
                                       val _ = ATV.insert(var_table,v,str')
                                       val _ = HashTable.insert var_table' (str',v)
                                   in
                                      "Y" ^ str' 
                                   end)
                 end  
    | _ => (case AT.isApp(t) of
               SOME(root,args) => if S.name(MS.lastName(root)) = "write" andalso length(args) = 1 
                                  then (case AT.isIdeConstant(hd(args)) of
                                            SOME(s) => "write('" ^ (strip s) ^ "')"
                                          | _ => (makePrologFunctor root) ^ "(" ^ (Basic.printListStr1(map makePrologTerm args,Basic.id, ",")) ^ ")")
                                  else (case args of
                                           [] => makePrologConstant(t)
                                         | _ => (makePrologFunctor root) ^ "(" ^ (Basic.printListStr1(map makePrologTerm args,Basic.id, ",")) ^ ")")
              | _ => ((* print("\nThe term to be translated is NOT an app or a variable...\n"); *)
                      makePrologConstant(t))));


val writeOut = SML_With_C_Interaction.copyIntoCBuffer1;

fun writePrologTerm(p,i,t) = 
  (case AT.isVar(t) of
      SOME(v) => let val str = ATV.name(v) 
                 in
                    if prologLegal(str) then writeOut("X" ^ str,p,i)
                    else (case ATV.find(var_table,v) of
                              SOME(str') => writeOut("Y" ^ str',p,i)
                            | _ => let val str' = makeFreshVar()
                                       val _ = ATV.insert(var_table,v,str')
                                       val _ = HashTable.insert var_table' (str',v)
                                   in
                                      writeOut("Y" ^ str',p,i)
                                   end)
                 end  
    | _ => (case AT.isApp(t) of
               SOME(root,args) => if MS.code(root) = !write_code 
                                  then (case AT.isIdeConstant(hd(args)) of
                                            SOME(s) => writeOut("write('" ^ (strip s) ^ "')",p,i)
                                          | _ => let val i1 = writeOut((makePrologFunctor root) ^ "(",p,i)
                                                     val i2 = writePrologTerms(p,i1,args)
                                                 in
                                                    writeOut(")",p,i2)
                                                 end)
                                  else if MS.code(root) = !prolog_var_code then
                                         (case AT.isIdeConstant(hd(args)) of
                                             SOME(str) =>
                                                 if prologLegal(str) then writeOut("X" ^ str,p,i)
                                                 else let val v = ATV.athTermVar(str)
                                                      in
                                                       (case ATV.find(var_table,v) of
                                                          SOME(str') => writeOut("Y" ^ str',p,i)
                                                        | _ => let val str' = makeFreshVar()
                                                                   val _ = ATV.insert(var_table,v,str')
                                                                   val _ = HashTable.insert var_table' (str',v)
                                                               in
                                                                  writeOut("Y" ^ str',p,i)
                                                               end)
                                                       end)
                                  else (case args of
                                           [] => writeOut(makePrologConstant(t),p,i)
                                         | _ => let val i1 = writeOut((makePrologFunctor root) ^ "(",p,i)
                                                    val i2 = writePrologTerms(p,i1,args)
                                                in
                                                  writeOut(")",p,i2)
                                                end)
              | _ => writeOut(makePrologConstant(t),p,i)))
and writePrologTerms(p,i,[]) = i
  | writePrologTerms(p,i,[t]) = writePrologTerm(p,i,t)
  | writePrologTerms(p,i,t1::(more as (_::_))) = 
       let val i' = writePrologTerm(p,i,t1)
           val i'' = writeOut(",",p,i') 
       in
          writePrologTerms(p,i'',more)
       end;


fun writePrologProp(pointer,i,p) = 
  (case Prop.isAtom(p) of
      SOME(t) => writePrologTerm(pointer,i,t)
    | _ => (case Prop.isCond(p) of
               SOME(p1,p2) => let val i' = writePrologProp(pointer,i,p2)
                                  val i'' = writeOut(" :- ",pointer,i')
                              in
                                 writePrologProp(pointer,i'',p1)
                              end
             | _ => (case Prop.isConj(p) of
                        SOME(props) => writePrologProps(pointer,i,props)
                      | _ => (case Prop.isNeg(p) of
                                 SOME(q) => let val i' = writeOut("not(",pointer,i)
				                val i'' = writePrologProp(pointer,i',q)                         
                                            in
                                               writeOut(")",pointer,i'')
                                            end
                               | _ => (case Prop.isDisj(p) of
                                          SOME(props) => writePrologProps(pointer,i,props)
                                       | _ => (case Prop.isBiCond(p) of
                                                  SOME(p1,p2) => (case Prop.isAtom(p1) of
                                                                     SOME(_) => writePrologProp(pointer,i,Prop.makeConditional(p2,p1))
                                                                   | _ => (case Prop.isAtom(p2) of
                                                                              SOME(_) => writePrologProp(pointer,i,Prop.makeConditional(p1,p2))
                                                                            | _ => i))
                                                | _ => (case Prop.splitVars(p) of
                                                           (SOME(A.forallCon),vars,body) => 
                                                              (case Prop.isCond(body) of
                                                                  SOME(left,right) => (case Prop.splitVars(left) of
                                                                                         (SOME(A.existsCon),vars',body') => 
                                                                                             writePrologProp(pointer,i,Prop.makeConditional(body',right))
                                                                                       | _ => writePrologProp(pointer,i,body))
                                                                | _ => (case Prop.isBiCond(body) of
                                                                           SOME(left,right) => (case Prop.splitVars(left) of
                                                                                                  (SOME(A.existsCon),vars',body') => 
                                                                                                     writePrologProp(pointer,i,Prop.makeConditional(body',right))
                                                                                                | _ => (case Prop.splitVars(right) of
                                                                                                           (SOME(A.existsCon),vars',body') => 
                                                                                                               writePrologProp(pointer,i,
                                                                                                                    Prop.makeConditional(body',left))))
                                                                         | _ => writePrologProp(pointer,i,body)))
                                                         | _ => i)))))))
and writePrologProps(pointer,i,[]) = i
  | writePrologProps(pointer,i,[p]) = writePrologProp(pointer,i,p)
  | writePrologProps(pointer,i,p::(more as (_::_))) = 
     let val i' = writePrologProp(pointer,i,p)  
         val i'' = if i' = i then i else writeOut(",",pointer,i')           
     in
       writePrologProps(pointer,i'',more)
     end;

fun writePrologListVal(buffer,i,v) = 
    (case Semantics.coerceValIntoTerm(v) of
        SOME(t) => let val vars = AT.getVarsInOrder(t)
                       val j = writePrologTerm(buffer,i,t)
                   in
                      (j,vars)
                   end
       | _ => (case v of
                  SV.listVal([SV.unitVal,pv1,pv2]) => 
                       let val i1 = writeOut("'/'(",buffer,i)
                           val (i2,vars) = writePrologListVal(buffer,i1,pv1)
                           val i3 = writeOut(",",buffer,i2)
                           val (i4,vars') = writePrologListVal(buffer,i3,pv2)
                           val i5 = writeOut(")",buffer,i4)
                       in
                          (i5,vars@vars')
                       end
                | SV.listVal([]) => (writeOut("[]",buffer,i),[])
                | SV.listVal(vals as v1::more) => 
                     ((* 
                      print("\nv1: " ^ (SV.prettyValToString v1) ^ "\n");
                      print("\nAnd more: " ^ (Basic.printListStr1(more,SV.prettyValToString,", ")) ^ "\n");
                      *)
                      (case (Semantics.coerceValIntoTermCon v1) of
                        SOME(SV.regFSym(f)) =>  
                           let val i1 = writeOut((makePrologFunctor (Data.fsymName f)) ^ "(",buffer,i)
                               val (i2,vars) = writePrologListVals(buffer,i1,more,[])
                               val i3 = writeOut(")",buffer,i2)
                           in 
                             (i3,vars)    
                           end
                    | _ =>
                     (case v1 of
                       SV.propConVal(A.notCon) => 
                           let val i1 = writeOut("not(",buffer,i)
                               val (i2,vars) = writePrologListVals(buffer,i1,more,[])
                               val i3 = writeOut(")",buffer,i2)
                           in 
                             (i3,AT.weedOutDups(vars))
                           end
                      | _ => 
                       let val i1 = writeOut("[",buffer,i)
                           val (i2,vars) = writePrologListVals(buffer,i1,vals,[])
                           val i3 = writeOut("]",buffer,i2)
                       in
                          (i3,vars)
                       end)))
                | SV.propVal(p) => let val vars = (case Prop.isNeg(p) of
                                                      SOME(q) => (case Prop.isAtom(q) of
                                                                     SOME(t) => AT.getVarsInOrder(t)
                                                                   | _ => [])
                                                    | _ => [])
                                       val j = writePrologProp(buffer,i,p)
                                   in
                                     (j,vars)
                                   end
               ))
and writePrologListVals(buffer,i,[],vars) = (i,AT.weedOutDups(rev(vars)))
  | writePrologListVals(buffer,i,[v],vars) = 
        let val (j,vars') = writePrologListVal(buffer,i,v)
        in
          (j,AT.weedOutDups(vars@vars'))
        end
  | writePrologListVals(buffer,i,v1::(more as (_::_)),vars) = 
          let val (i',vars') = writePrologListVal(buffer,i,v1)      
              val i'' = writeOut(",",buffer,i')
          in
             writePrologListVals(buffer,i'',more,vars@vars')
          end;

fun writeToStream(str,stream) = TextIO.output(stream,str);

fun writeToStream'(str,stream) = if str = "" then false else (TextIO.output(stream,str);true)

fun writePrologTermToStream(stream,t) = 
  (case AT.isVar(t) of 
      SOME(v) => let val str = ATV.name(v) 
                 in
                    if prologLegal(str) then writeToStream'("X" ^ str,stream)
                    else (case ATV.find(var_table,v) of
                              SOME(str') => writeToStream'("Y" ^ str',stream)
                            | _ => let val str' = makeFreshVar()
                                       val _ = ATV.insert(var_table,v,str')
                                       val _ = HashTable.insert var_table' (str',v)
                                   in
                                      writeToStream'("Y" ^ str',stream)
                                   end)
                 end  
    | _ => (case AT.isApp(t) of
               SOME(root,args) => if MS.code(root) = !write_code 
                                  then (case AT.isIdeConstant(hd(args)) of
                                            SOME(s) => writeToStream'("write('" ^ (strip s) ^ "')",stream)
                                          | _ => let val i1 = writeToStream'((makePrologFunctor root) ^ "(",stream)
                                                     val i2 = writePrologTermsToStream(stream,args)
                                                 in
                                                    writeToStream'(")",stream)
                                                 end)
                                  else (case args of
                                           [] => writeToStream'(makePrologConstant(t),stream)
                                         | _ => let val i1 = writeToStream'((makePrologFunctor root) ^ "(",stream)
                                                    val i2 = writePrologTermsToStream(stream,args)
                                                in
                                                  writeToStream'(")",stream)
                                                end)
              | _ => writeToStream'(makePrologConstant(t),stream)))
and writePrologTermsToStream(stream,[]) = false
  | writePrologTermsToStream(stream,[t]) = writePrologTermToStream(stream,t)
  | writePrologTermsToStream(stream,t1::(more as (_::_))) = 
       let val b = writePrologTermToStream(stream,t1)
           val _ = if b then writeToStream'(",",stream) else false
       in
          writePrologTermsToStream(stream,more)
       end;
                      
fun makePrologProp(p) = 
  (case Prop.isAtom(p) of
      SOME(t) => makePrologTerm(t)
    | _ => (case Prop.isCond(p) of
               SOME(p1,p2) => (makePrologProp p2) ^ " :- " ^ (makePrologProp p1)
             | _ => (case Prop.isConj(p) of
                        SOME(props) => Basic.printListStr1(props,makePrologProp,", ")
                      | _ => (case Prop.isNeg(p) of
                                 SOME(q) => "not(" ^ (makePrologProp q) ^ ")"
                               | _ => (case Prop.isDisj(p) of
                                          SOME(props) => Basic.printListStr1(props,makePrologProp," ; ")
                                       | _ => (case Prop.isBiCond(p) of
                                                  SOME(p1,p2) => (case Prop.isAtom(p1) of
                                                                     SOME(_) => makePrologProp(Prop.makeConditional(p2,p1))
                                                                   | _ => (case Prop.isAtom(p2) of
                                                                              SOME(_) => makePrologProp(Prop.makeConditional(p1,p2))
                                                                            | _ => ""))
                                                | _ => (case Prop.splitVars(p) of
                                                           (SOME(A.forallCon),vars,body) => 
                                                              (case Prop.isCond(body) of
                                                                  SOME(left,right) => (case Prop.splitVars(left) of
                                                                                         (SOME(A.existsCon),vars',body') => 
                                                                                             makePrologProp(Prop.makeConditional(body',right))
                                                                                       | _ => makePrologProp(body))
                                                                | _ => (case Prop.isBiCond(body) of
                                                                           SOME(left,right) => (case Prop.splitVars(left) of
                                                                                                  (SOME(A.existsCon),vars',body') => 
                                                                                                     makePrologProp(Prop.makeConditional(body',right))
                                                                                                | _ => (case Prop.splitVars(right) of
                                                                                                           (SOME(A.existsCon),vars',body') => 
                                                                                                               makePrologProp(Prop.makeConditional(body',left))))
                                                                         | _ => makePrologProp(body)))
                                                         | _ => "")))))));



(**********************                      
fun writePrologProp(pointer,i,p) = 
  (case Prop.isAtom(p) of
      SOME(t) => writePrologTerm(pointer,i,t)
    | _ => (case Prop.isCond(p) of
               SOME(p1,p2) => let val i' = writePrologProp(pointer,i,p2)
                                  val i'' = writeOut(" :- ",pointer,i')
                              in
                                 writePrologProp(pointer,i'',p1)
                              end
             | _ => (case Prop.isConj(p) of
                        SOME(props) => writePrologProps(pointer,i,props)
                      | _ => (case Prop.isNeg(p) of
                                 SOME(q) => let val i' = writeOut("not(",pointer,i)
				                val i'' = writePrologProp(pointer,i',q)                         
                                            in
                                               writeOut(")",pointer,i'')
                                            end
                               | _ => (case Prop.isDisj(p) of
                                          SOME(props) => writePrologProps(pointer,i,props)
                                       | _ => (case Prop.isBiCond(p) of
                                                  SOME(p1,p2) => (case Prop.isAtom(p1) of
                                                                     SOME(_) => writePrologProp(pointer,i,Prop.makeConditional(p2,p1))
                                                                   | _ => (case Prop.isAtom(p2) of
                                                                              SOME(_) => writePrologProp(pointer,i,Prop.makeConditional(p1,p2))
                                                                            | _ => i))
                                                | _ => (case Prop.splitVars(p) of
                                                           (SOME(A.forallCon),vars,body) => 
                                                              (case Prop.isCond(body) of
                                                                  SOME(left,right) => (case Prop.splitVars(left) of
                                                                                         (SOME(A.existsCon),vars',body') => 
                                                                                             writePrologProp(pointer,i,Prop.makeConditional(body',right))
                                                                                       | _ => writePrologProp(pointer,i,body))
                                                                | _ => (case Prop.isBiCond(body) of
                                                                           SOME(left,right) => (case Prop.splitVars(left) of
                                                                                                  (SOME(A.existsCon),vars',body') => 
                                                                                                     writePrologProp(pointer,i,Prop.makeConditional(body',right))
                                                                                                | _ => (case Prop.splitVars(right) of
                                                                                                           (SOME(A.existsCon),vars',body') => 
                                                                                                               writePrologProp(pointer,i,
                                                                                                                    Prop.makeConditional(body',left))))
                                                                         | _ => writePrologProp(pointer,i,body)))
                                                         | _ => i)))))))
and writePrologProps(pointer,i,[]) = i
  | writePrologProps(pointer,i,[p]) = writePrologProp(pointer,i,p)
  | writePrologProps(pointer,i,p::(more as (_::_))) = 
     let val i' = writePrologProp(pointer,i,p)  
         val i'' = if i' = i then i else writeOut(",",pointer,i')           
     in
       writePrologProps(pointer,i'',more)
     end;

***********************)

fun writePrologPropToStream(stream,p) = 
  (case Prop.isAtom(p) of
      SOME(t) => writePrologTermToStream(stream,t)
(*******************
                 (case Prop.isEquality(p) of
                     NONE => writePrologTermToStream(stream,t)
                   | _ => false)
***************)
    | _ => (case Prop.isCond(p) of
               SOME(p1,p2) => (case Prop.isEquality(p2) of
                                  SOME(_) => false
                                | _ => let val i' = writePrologPropToStream(stream,p2)
                                           val i'' = writeToStream'(" :- ",stream)
                                       in
                                          writePrologPropToStream(stream,p1)
                                       end)
             | _ => (case Prop.isConj(p) of
                        SOME(props) => writePrologPropsToStream(stream,props,",")
                      | _ => (case Prop.isNeg(p) of
                                 SOME(q) => let val i' = writeToStream'("not(",stream)
				                val i'' = writePrologPropToStream(stream,q)                         
                                            in
                                               writeToStream'(")",stream)
                                            end
                               | _ => (case Prop.isDisj(p) of
                                          SOME(props) => if length(props) > 1 then 
                                                               (writeToStream'("(",stream);
                                                                writePrologPropsToStream(stream,props,";");
                                                                writeToStream'(")",stream))
                                                         else
                                                             writePrologPropsToStream(stream,props,";")
                                       | _ => (case Prop.isBiCond(p) of
                                                  SOME(p1,p2) => (case Prop.isAtom(p1) of
                                                                     SOME(_) => writePrologPropToStream(stream,Prop.makeConditional(p2,p1))
                                                                   | _ => (case Prop.isAtom(p2) of
                                                                              SOME(_) => writePrologPropToStream(stream,Prop.makeConditional(p1,p2))
                                                                            | _ => false))
                                                | _ => (case Prop.splitVars(p) of
                                                           (SOME(A.forallCon),vars,body) => 
                                                              (case Prop.isCond(body) of
                                                                  SOME(left,right) => (case Prop.splitVars(left) of
                                                                                         (SOME(A.existsCon),vars',body') => 
                                                                                             writePrologPropToStream(stream,Prop.makeConditional(body',right))
                                                                                       | _ => writePrologPropToStream(stream,body))
                                                                | _ => (case Prop.isBiCond(body) of
                                                                           SOME(left,right) => (case Prop.splitVars(left) of
                                                                                                  (SOME(A.existsCon),vars',body') => 
                                                                                                     writePrologPropToStream(stream,Prop.makeConditional(body',right))
                                                                                                | _ => (case Prop.splitVars(right) of
                                                                                                           (SOME(A.existsCon),vars',body') => 
                                                                                                               writePrologPropToStream(stream,
                                                                                                                    Prop.makeConditional(body',left))
                                                                                                          | _ => writePrologPropToStream(stream,body)))
                                                                         | _ => writePrologPropToStream(stream,body)))
                                                         | _ => false)))))))
and writePrologPropsToStream(stream,[],_) = false
  | writePrologPropsToStream(stream,[p],_) = writePrologPropToStream(stream,p)
  | writePrologPropsToStream(stream,p::(more as (_::_)),sep) = 
     let val b = writePrologPropToStream(stream,p)  
         val _ = if b then writeToStream'(sep,stream) else false
     in
       writePrologPropsToStream(stream,more,sep)
     end;

val delim_array = Unsafe.Array.create(128,false);

val delims = [#",", #")", #"(", #" ", #"[",  #"]", #"\n"];
 
val _ = List.app (fn c => Unsafe.Array.update(delim_array,Char.ord(c),true)) delims;

fun isDelim(c) = Unsafe.Array.sub(delim_array,Char.ord(c));

fun getString([],res) = (rev(res),[])
  | getString(chars as (c::more),res) = 
       if isDelim(c) then (rev(res),chars) else getString(more,c::res)
       

val standard_sym_table: (string,MS.mod_symbol) HashTable.hash_table = HashTable.mkTable(Basic.hashString,op=)  (13,Basic.Never);

val athena_cons_symbol = Symbol.symbol("::")
val athena_nil_symbol = Symbol.symbol("nil")

val _ = (HashTable.insert standard_sym_table ("+",Names.maddition_symbol);
         HashTable.insert standard_sym_table ("-",Names.msubtraction_symbol);
         HashTable.insert standard_sym_table ("*",Names.mmultiplication_symbol);
         HashTable.insert standard_sym_table ("/",Names.mdivision_symbol);
         HashTable.insert standard_sym_table ("[]",MS.makeModSymbol([],athena_nil_symbol,athena_nil_symbol));
         HashTable.insert standard_sym_table ("'.'",MS.makeModSymbol([],athena_cons_symbol,athena_cons_symbol)));

 
fun getSymbol(chars) =
   (case (HashTable.find standard_sym_table (implode chars)) of 
       SOME(fsym) => fsym
     | _ => (case chars of
                 #"c"::rest => MS.makeModSymbol'([],Symbol.symbol(implode(rest)))
               | #"k"::rest => (HashTable.lookup constant_table' (implode rest))
               | #"f"::rest => MS.makeModSymbol'([],Symbol.symbol(implode(rest)))
               | #"g"::rest => (HashTable.lookup fsym_table' (implode rest))));


fun isFreshVar([#"_"]) = true
  | isFreshVar(_) = false;

fun isVariable(c::_) = Char.isUpper(c) orelse c = #"_"
  | isVariable(_) = false;

fun makePrologList(terms) = 
  let val cons = !cons_fsym
      fun loop([]) = AT.makeConstant(!nil_fsym)
        | loop(t::more) = 
                let val L = loop(more)
                in
                  AT.makeApp(cons,[t,L])        
                end
   in
     loop(terms)
   end

fun parseTerm(chars:char list) = 
   let (* val _ = print("\nCalling parseTerm on this input: " ^ (implode chars) ^  "\n") *)
   in
       #1(getTerm(chars))
   end 
and getTerm(chars) = 
    (case chars of
       #"["::rest => let (* val _ = print("\nParsing in the right place...\n") *)
                     in 
                      (case getTerms(rest,[]) of
                         (args,#"]"::rest') => if null(args) then (AT.makeConstant(!nil_fsym),rest')
                                               else let val fsym = !cons_fsym
(***
					                val _ = print("\nHere are the term args: " ^ (Basic.printListStr1(args,AT.toStringDefault," ")))
					                val _ = print("\nAnd here's the functor to be applied: " ^ (MS.name(fsym)) ^ "\n")
**)
                                                        val res_term = makePrologList(args)
                                                in
                                                    (res_term,rest')
                                                end)
                     end 
     | _ =>
       (case getString(chars,[]) of
           (root,#"("::rest) => (case getTerms(rest,[]) of
                                    (args,#")"::rest') => let val fsym = getSymbol(root)
                                                              val res_term = AT.makeApp(fsym,args)
                                                          in
                                                             (res_term,rest')
                                                          end)
         | (root,rest) => let (* val _ = print("\nHere's the root: " ^ (implode root) ^ "\n") *)
	                  in
                          if isFreshVar(root) then (AT.makeVar(ATV.fresh()),rest)
                          else if isVariable(root) then 
                                   (case root of
                                        #"Y"::more => (AT.makeVar(HashTable.lookup var_table' (implode root)),rest)
                                      | _ => (AT.makeVar(ATV.athTermVar(implode(tl(root)))),rest))
                               else (case root of
                                        #"-"::more => let val (t,more') = getTerm(more@rest)
                                                      in
                                                         (AT.makeApp(Names.msubtraction_symbol,[t]),more')
                                                      end
                                      | _ => (case A.getAthNumber(implode(root)) of
                                                 SOME(n) => (AT.makeNumTerm(n),rest)
                                               | _ => let val res = (AT.makeApp(getSymbol(root),[]),rest) handle _ =>
                                                                    (AT.makeIdeConstant(implode(root)),rest)
                                                       in
                                                         res 
                                                       end))
                        end))
and getTerms(chars,terms) =
      (case getTerm(chars) of 
          (t,#","::rest) => getTerms(rest,t::terms)
        | (t,rest) => (rev(t::terms),rest))
and parseTerms(chars:char list) = getTerms(chars,[]);

(**
val doXSBCommand = _import "doXSBCommand" public: SML_With_C_Interaction.pointer -> SML_With_C_Interaction.pointer
val answerQuery = _import "answerQuery" public: SML_With_C_Interaction.pointer * int -> SML_With_C_Interaction.pointer
**)
fun execXSBCommand(str) = 
      let val res = doXSBCommand(SML_With_C_Interaction.SMLString2CString(str))
          val _ = case SML_With_C_Interaction.makeCharList(res) of 
                       #"!"::rest => Semantics.primError("Error:" ^ (implode rest))
                     | _ => ()
  in
     SML_With_C_Interaction.free(res)
  end;

fun execXSBCommand1(pointer) = 
      let val res = doXSBCommand(pointer)
          val _ = case SML_With_C_Interaction.makeCharList(res) of 
                       #"!"::rest => Semantics.primError("Error:" ^ (implode rest))
                     | _ => ()
  in
     SML_With_C_Interaction.free(pointer)
  end;

fun assertOrRetractProps(props,retract_flag) = 
  let val total_size = Prop.sizeLst(props)
      val allocated = 30 + (15 * total_size)
      val pointer = SML_With_C_Interaction.mallocChars(allocated)
      val _ = if SML_With_C_Interaction.isNullPointer(pointer) then 
                 Semantics.primError("Athena<->C<-->XSB interface error: unable to malloc sufficient memory to write out the asserted Athena sentences.\n")
              else ()
      val cmd = if retract_flag then "retractAll" else "assertAll" 	    
      val i = writeOut(cmd ^ "([",pointer,0)
      val i' = writePrologProps(pointer,i,props)
      val i'' = writeOut("]).",pointer,i')
      val _ = SML_With_C_Interaction.setChar(pointer,i'',SML_With_C_Interaction.null_char)
      val pointer = if i'' < allocated then pointer 
                    else let val allocated = 30 + (30 * total_size)
                             val pointer = SML_With_C_Interaction.mallocChars(allocated)
			     val characterization = if retract_flag then "retracted" else "asserted"
                             val _ = if SML_With_C_Interaction.isNullPointer(pointer) then 
                                        Semantics.primError("Athena<->C<-->XSB interface error: unable to malloc sufficient " ^ 
                                                         "memory to write out the " ^ characterization ^ " Athena sentences.\n")
                                     else ()
                             val i = writeOut(cmd ^ "([",pointer,0)
                             val i' = writePrologProps(pointer,i,props)
                             val i'' = writeOut("]).",pointer,i')
                          in
                             pointer
                          end
  in
     ((execXSBCommand1 pointer) handle Semantics.PrimError(str) => Semantics.primError("\nError: " ^ (if retract_flag then "Retraction" else "Assertion") ^
                                                                                 " failed: " ^ str))
  end

fun makePrologTermPrimUFun(v,env,_) = 
  (case Semantics.coerceValIntoTerm(v) of
       SOME(t) => let val p = SML_With_C_Interaction.mallocChars(1000000)
                      val i = writePrologTerm(p,0,t)
                      val _ = SML_With_C_Interaction.setChar(p,i,SML_With_C_Interaction.null_char)
                      val str = SML_With_C_Interaction.makeSmlString(p)
		      val _ = print("\nTranslated (and written!) Prolog term: " ^ str ^ "\n")
                  in
                     TopEnv.MLStringToAthString(str)
                  end);

fun makePrologPropPrimUFun(v,env,_) = 
  (case Semantics.coerceValIntoProp(v) of
       SOME(p) => let val str = makePrologProp(p)
                  in
                     TopEnv.MLStringToAthString(str)
                  end);

val _ = TopEnv.updateTopValEnvWithNewPrimUFun(Symbol.symbol("mpt"),makePrologTermPrimUFun);
val _ = TopEnv.updateTopValEnvWithNewPrimUFun(Symbol.symbol("mpp"),makePrologPropPrimUFun);

fun assertPropsPrimUFun(v,env,_) = 
    (case v of 
        SV.listVal(vals) =>  
            let val props = Semantics.getProps(vals,"the argument list given to " ^ Names.assertPrologFun_name,env)
	        val _ = assertOrRetractProps(rev(props),false)
            in
               SV.unitVal
            end
      | _ => Semantics.primError(Semantics.wrongArgKind(Names.assertPrologFun_name,1,Semantics.listLCType,v)))

fun retractPropsPrimUFun(v,env,_) = 
    (case v of 
        SV.listVal(vals) =>  
            let val props = Semantics.getProps(vals,"the argument list given to " ^ Names.retractPrologFun_name,env)
	        val _ = assertOrRetractProps(rev(props),true)
            in
               SV.unitVal
            end
      | _ => Semantics.primError(Semantics.wrongArgKind(Names.retractPrologFun_name,1,Semantics.listLCType,v)));


val _ = TopEnv.updateTopValEnvWithNewPrimUFun(Names.assertPrologFun_symbol,assertPropsPrimUFun);
val _ = TopEnv.updateTopValEnvWithNewPrimUFun(Names.retractPrologFun_symbol,retractPropsPrimUFun);

fun pickSyms(L) = 
   let val T = MS.makeHTableWithInitialSize(31)
       fun loop([],res) = res
         | loop((x as (fsym,_))::more,res) = 
               (case MS.find(predefined_functor_table,fsym) of
                    SOME(_) => loop(more,res)
                  | _ => (case MS.find(T,fsym) of
                             SOME(_) => loop(more,res)
                           | _ => (MS.insert(T,fsym,true);loop(more,x::res))))
    in
       loop(L,[])
    end;
     
fun getTabledSyms(v::_) = 
  let val ht = case v of
                   SV.tableVal(ht) => ht
                 | _ => Semantics.primError(Semantics.wrongArgKind(N.loadPrologFun_name,2,Semantics.tableLCType,v))
      val vals = 
              case (HashTable.find ht (SV.termVal(AT.makeIdeConstant("tabled")))) of
                  SOME(SV.listVal(vals)) => vals
                | _ => []
      fun getFSyms([],res) = res
        | getFSyms(v::more,res) = 
              (case (Semantics.coerceValIntoTermCon v) of
                   SOME(SV.regFSym(f)) => 
                           let val (name,arity) = (Data.fsymName(f),Data.fsymArity(f))
                           in
                              getFSyms(more,(name,arity)::res)
                           end
                 | _ => Semantics.primError("Invalid tabled option; a function symbol was expected here instead of " ^ (TopEnv.prettyValToString(v)) ^ "\n"))
           val pred_syms_and_arities = getFSyms(vals,[])
      in 
         pred_syms_and_arities
      end
  | getTabledSyms(_) = [];

fun getFSym(v) = 
      (case (Semantics.coerceValIntoTermCon v) of
          SOME(SV.regFSym(f)) => (Data.fsymName(f),Data.fsymArity(f))
        | _ => Semantics.primError("Invalid option value: a function symbol was expected here instead of " ^ (TopEnv.prettyValToString(v)) ^ "\n"));

fun getOptionVal(ht,option_name,f) = 
        (case (HashTable.find ht (SV.termVal(AT.makeIdeConstant(option_name)))) of
            SOME(v) => SOME(f(v))
          | _ => NONE);

fun getSyms(ht_option,option_name) = 
      (case ht_option of
          SOME(ht) => getOptionVal(ht,option_name,fn Semantics.listVal(vals) => (List.map getFSym vals)
                                                   | _ => Semantics.primError("Invalid type of value given to option " ^ option_name ^ ".\n" ^
                                                                           "A list of function symbols was expected."))
        | _ => NONE);

fun loadFun((v1 as (SV.listVal(vals)))::rest,env,_) = 
            let val ht_option = if null(rest) then NONE else
                                 case hd(rest) of
                                   SV.tableVal(ht) => SOME(ht)
                                 | _ => NONE
                val tabled_syms = getTabledSyms(rest)
                val dynamic_syms = getSyms(ht_option,"dynamic") 
		fun writeListVal(v,stream) = 
                   let val buffer = SML_With_C_Interaction.mallocChars(100000)
                       val (i,vars) = writePrologListVal(buffer,0,v)
                       val _ = SML_With_C_Interaction.setChar(buffer,i,SML_With_C_Interaction.null_char)
                       val str = SML_With_C_Interaction.makeSmlString(buffer)
		       val res = writeToStream'(str,stream)
                       val _ = SML_With_C_Interaction.free(buffer)
                   in
                      res 
                   end
		fun writeAll([],stream) = false
                  | writeAll([v],stream) = 
		    let 
                    in
                     (case Semantics.coerceValIntoProp(v) of 
                         SOME(p) => writePrologPropToStream(stream,p)
                       | _ => (case v of 
                                 SV.listVal(_) => let 
                                                  in
                                                      writeListVal(v,stream)
                                                  end 
                               | _ => raise Basic.Never))
                   end
                 | writeAll(v::more,stream) = 
                     let val b = (case Semantics.coerceValIntoProp(v) of 
                                     SOME(p) => writePrologPropToStream(stream,p)
                                   | _ => (case v of 
                                              SV.listVal(_) => let 
                                                                   val res = writeListVal(v,stream)
                                                                in 
                                                                    res 
                                                                end)
                                            | _ => raise Basic.Never)
                         val _ = if b then writeToStream'(".\n",stream) else false
                     in
                        writeAll(more,stream)
                     end
                val (props,all_props) = ((Semantics.getProps(vals,"the argument list given to " ^ Names.loadPrologFun_name,env),true)
                                           handle _ => ([],false))
           in
            let val pred_syms_and_arities = pickSyms(Prop.predSymbolsLst(props))
 	        val file_name = "./athenaPCode" ^ (Int.toString (Basic.returnAndInc file_counter)) ^ ".P"
                val stream = TextIO.openOut(file_name)
                val tabled_dec_str = Basic.printListStr1(tabled_syms, fn (p,n) => (makePrologFunctor p) ^ "/" ^ (Int.toString n),", ")
		val dynamic_preds = (case dynamic_syms of
                                         NONE => pred_syms_and_arities
                                       | SOME(L) => L)
                val subsumptive_tabled_syms = getSyms(ht_option,"tabled-subsumptive")
		val subsumptive_tabled_preds = 
                                     (case subsumptive_tabled_syms of
                                          NONE => []
                                        | SOME(L) => L)
                val dynamic_dec_str = if null(dynamic_preds) then "" else
                                      let val str = Basic.printListStr1(dynamic_preds, 
                                                                        fn (p,n) => (makePrologFunctor p) ^ "/" ^ (Int.toString n),", ")
                                      in
                                        "\n:- dynamic " ^ str ^ ".\n\n"
                                      end
		val subsumptive_tabled_dec_str = Basic.printListStr1(subsumptive_tabled_preds, fn (p,n) => (makePrologFunctor p) ^ "/" ^ (Int.toString n),", ")
                val _ = TextIO.output(stream,":- set_prolog_flag(unknown,fail).\n")
                val _ = if null(tabled_syms) then ()
                        else (TextIO.output(stream,"\n:- table ");TextIO.output(stream,tabled_dec_str);TextIO.output(stream,".\n"))
                val _ = if null(subsumptive_tabled_preds) then ()
                        else (TextIO.output(stream,"\n:- table ");TextIO.output(stream,subsumptive_tabled_dec_str);
                              TextIO.output(stream," as subsumptive.\n\n"))
                val _ = TextIO.output(stream,dynamic_dec_str)
		val b = writeAll(vals,stream)
		val _ = if b then writeToStream(".\n",stream) else ()
		val _ = TextIO.closeOut(stream)
		val load_command = "consult('" ^ file_name ^ "')."
	        val ok = execXSBCommand(load_command)
(*
                val _ = OS.FileSys.remove(file_name)
*)
            in
                SV.unitVal
            end
      end 
  | loadFun(v::rest,env,_) = Semantics.primError(Semantics.wrongArgKind(Names.loadPrologFun_name,1,Semantics.listLCType,v));

val _ = TopEnv.updateTopValEnvLstOldAndFast([(N.loadPrologFun_symbol,SV.funVal(loadFun,N.loadPrologFun_name,TopEnv.default_fv_pa_for_procs 0))]);

fun getQueryVars(p) = 
   let val L:ATV.ath_term_var list = []
   in
       L
   end                   

fun getTuple([],terms) = rev(terms)
  | getTuple(chars,terms) = 
        let val (chunk,rest) = Basic.skipUntil1(chars,fn c => c = #"|")
            val t = parseTerm(chunk)
            val rest' = if null(rest) then rest else tl(rest)
        in
           getTuple(rest',t::terms)
        end;

fun getAnswerTuples(chars) = 
  let fun getAll([],tuples) = tuples
        | getAll(chars,tuples) = 
             let val (chunk,rest) = Basic.skipUntil1(chars,fn c => c = #"\n")
	         val tuple = getTuple(chunk,[])
		 val rest' = if null(rest) then rest else tl(rest)
             in
               getAll(rest',tuple::tuples)
             end
(***
      val _ = print("\nAbout to call getAnswerTuples on this list of characters: " ^ (implode chars) ^ "\n")
***)
  in
    getAll(chars,[])
  end

fun makeSub(var_term_pairs) = 
   let fun loop([],sub) = sub
         | loop((v,t)::rest,sub) = loop(rest,AthTerm.composeSubs(sub,TopEnv.getLegalBinding(v,t)))
   in
     SV.subVal(loop(var_term_pairs,AthTerm.empty_sub))
   end;

fun getSubs(query_vars,chars) = 
  (case chars of
      #"%"::_ => SV.listVal([SV.false_val,SV.listVal([])])
    | _ => 
        let val answer_tuples = getAnswerTuples(chars)
            fun makeSubFromTuple(tuple) = makeSub(Basic.zip(query_vars,tuple))
            val sub_vals = map makeSubFromTuple answer_tuples
(***
	    val _ = print("\nQuery vars: " ^ (Basic.printListStr1(query_vars,ATV.toStringDefault,",")) ^ "\n")
            val _ = print("\nAnswer subs: " ^ (Basic.printListStr1(sub_vals,SV.prettyValToString,"\n")) ^ "\n")
***)
        in
           SV.listVal([SV.true_val,SV.listVal(sub_vals)])
        end);

fun predefinedPrologSymbolsPrimUFun(v,env,_) = 
   (case v of
       SV.listVal(vals) => 
          let val c = ref(0)
              fun f(v) =  
                   let val i = Basic.incAndReturn(c)
                   in
                     (case (Semantics.coerceValIntoTermCon v) of
                         SOME(SV.regFSym(g)) => 
                             let val msym = Data.fsymName(g)
                                 val code = MS.code(msym)
                               (* val _ = print("\nTranslating this symbol: " ^ (MS.name msym) ^ "\n") *)
			         val last_name = if code = MS.code(N.mformal_leq_symbol) then "=<" else
                                                 if code = MS.code(N.mformal_geq_symbol) then ">=" else
                                                 if code = MS.code(Names.mfalse_logical_symbol) then "fail" else
                                                 if code = MS.code(Names.mtrue_logical_symbol) then "true" else
                                                 let val str = S.name(MS.lastName(msym))
                                                 in
                                                   if str = "arith-eq" then "=:=" 
                                                   else if str = "arith-uneq" then "=\\="
                                                   else if str = "square-root" then "sqrt"
                                                   else if str = "prolog_member" then "basics:member"
                                                   else if str = "Cons" then "'.'"
                                                   else if str = "Nil" then "[]"
                                                   else if str = "Pair" then "'/'"
                                                   else if str = "cut" then "!"
                                                   else str 
                                                 end
				 val _ = if last_name = "cut" then cut_code := code else
                                         if last_name = "fail" then fail_code := code else
                                         if last_name = "prolog-retract" then retract_code := code else
                                         if last_name = "asserta" then asserta_code := code else
                                         if last_name = "assertz" then assertz_code := code else
                                         if last_name = "setof" then setof_code := code else
                                         if last_name = "bagof" then bagof_code := code else
                                         if last_name = "square-root" then square_root_code := code else
                                         if last_name = "findall" then findall_code := code else
                                         if last_name = "call" then call_code := code else
                                         if last_name = "write" then write_code := code else
                                         if last_name = "prolog-var" then prolog_var_code := code else
                                         if last_name = "'/'" then (pair_fsym := msym; pair_code := code;
                                                                    HashTable.insert standard_sym_table ("'/'",msym)) else
                                         if last_name = "'.'" then (cons_fsym := msym;cons_code := code) else
                                         if last_name = "[]" then (nil_fsym := msym;nil_code := code) else
                                         if last_name = "is" then is_code := code else ()
                             in
                                MS.insert(predefined_functor_table,msym,last_name)
                             end
                       | _ => Semantics.primError("Wrong kind of value found in the "^
                                               (Semantics.ordinal i)^" element of the list argument to load-predefined-syms" ^ 
                                               "---"^(Semantics.expect(Semantics.termConLCType,v))))
                   end
               val _ = List.app f vals
          in
            Semantics.unitVal
          end
    | _ => Semantics.primError(Semantics.wrongArgKind("load-predefined-syms",1,Semantics.listLCType,v)));

val _ = TopEnv.updateTopValEnvWithNewPrimUFun(S.symbol("load-predefined-syms"),predefinedPrologSymbolsPrimUFun);

fun prologQueryFun(vals,env,_) = 
  let val limit = (case vals of
                    _::v2::_ => (case v2 of
                                    SV.tableVal(ht) => (case (HashTable.find ht (SV.termVal(AT.makeIdeConstant("result-limit")))) of
                                                           SOME(SV.termVal(t)) => 
                                                                (case AT.getNumVal(t) of
                                                                    SOME(A.int_num(i,_),neg1) => TopEnv.getSignedInt(i,neg1)
                                                                  | _ => default_result_limit)
                                                         | _ => default_result_limit)
                                  | _ => default_result_limit)
                 | _ => default_result_limit)
  in
    if null(vals) then
       Semantics.primError(Semantics.wrongArgNumber(N.queryPrologFun_name,0,1))
    else 
    let val v1 = hd(vals)
    in
      (case Semantics.coerceValIntoTerm(v1) of
          SOME(t) => let 
(************
                         val t0 = Time.toReal(Time.now())
                         val term_size = AT.size(t)                         
                         val _ = print("\nTime taken to calculate the term size: " ^ (Real.toString(Time.toReal(Time.now()) - t0)) ^ "\n")
	                 val t1 = (print("\nAbout to make a Prolog term from the given Athena query term...\n");
                                    Time.toReal(Time.now()))                  
                         val t0 = Time.toReal(Time.now())                                     
**********)
	                 val tp = SML_With_C_Interaction.mallocChars(10000000)
(**
                         val _ = print("\nTime taken for the malloc: " ^ (Real.toString(Time.toReal(Time.now()) - t0)) ^ "\n")
***)
                         val _ = if SML_With_C_Interaction.isNullPointer(tp) then 
                                 Semantics.primError("Athena<->C<-->XSB interface error: unable to malloc sufficient memory\n"^
                                                  "to write out the given query term.\n")
                                 else ()
                         val t1 = Time.toReal(Time.now())                                     
                         val i = writePrologTerm(tp,0,t)
                         val i' = writeOut(".",tp,i); 
                         val _ = SML_With_C_Interaction.setChar(tp,i',SML_With_C_Interaction.null_char)
			 val term_str = SML_With_C_Interaction.makeSmlString(tp)
(***)
			 val _ = print("\nAbout to issue the following query: " ^ term_str ^ "\n")
(***)

(***
	                 val t2 = (print("\nTerm writing done...\n");
                                    Time.toReal(Time.now()))
                         val elapsed = Real.-(t2,t1)
                         val _ = print("\nTerm writing took " ^ (Real.toString elapsed) ^ " seconds...")			 
	                 val t1 = (print("\nStarting actual query answering...\n");
                                    Time.toReal(Time.now()))
***)
                         val p = answerQuery(tp,limit)
(***
	                 val t2 = (print("\nActual query answering done...\n");
                                    Time.toReal(Time.now()))
                         val elapsed = Real.-(t2,t1)
                         val _ = print("\nQuery answering took " ^ (Real.toString elapsed) ^ " seconds...")
***)
                         val _ = SML_With_C_Interaction.free(tp)
                         val chars = SML_With_C_Interaction.makeCharList(p) 
                         val _ = SML_With_C_Interaction.free(p)
                     in
                         (case chars of
                              #"%"::_ => SV.listVal([SV.false_val,SV.listVal([])])
                           |  #"!"::rest => Semantics.primError(implode rest)
                           | _ => if (limit > 0) then
                                     let val vars = AT.getVarsInOrder(t)
(***
                                      val t1 = Time.toReal(Time.now())
***)
			              val res = getSubs(vars,chars)
(***
                                      val elapsed = Real.-(Time.toReal(Time.now()),t1)
                                      val _ = print("\nMaking the substitution result took " ^ (Real.toString elapsed) ^ " seconds...")
***)
                                  in
                                     res
                                  end
                                else SV.listVal([SV.true_val,SV.listVal([])])
                                  )
                     end
        | _ => (case v1 of 
                   SV.listVal(L) => 
                    (case (SOME(Semantics.getTermsNoPos(L,"query")) handle _ => NONE) of
                      SOME(terms) => let 
		                        val count = (AT.sizeLst terms) * 30
		                        val buffer = SML_With_C_Interaction.mallocChars(count)
                                        val _ = if SML_With_C_Interaction.isNullPointer(buffer) then 
                                                    Semantics.primError("Athena<->C<-->XSB interface error: unable to malloc sufficient memory\n"^
                                                                     "to write out the given query terms")
                                                else ()
					val i = writePrologTerms(buffer,0,terms)
					val i' = writeOut(".",buffer,i)
					val buffer = if i' < count then buffer else
                                                        let val _ = SML_With_C_Interaction.free(buffer)
                                                            val count = (AT.sizeLst terms) * 100
                                                            val buffer =  SML_With_C_Interaction.mallocChars(count)
 	         		        	    	    val i = writePrologTerms(buffer,0,terms)
					                    val i' = writeOut(".",buffer,i)
                                                            val _ = if SML_With_C_Interaction.isNullPointer(buffer) then 
                                                                        Semantics.primError("Athena<->C<-->XSB interface error: unable to malloc sufficient memory\n"^
                                                                        "to write out the given query terms")
                                                                    else ()
                                                        in
                                                           buffer
                                                        end
                                        val _ = SML_With_C_Interaction.setChar(buffer,i',SML_With_C_Interaction.null_char)
					val term_str = SML_With_C_Interaction.makeSmlString(buffer)
(***
 			                val _ = print("\nAbout to issue the following query: " ^ term_str ^ "\n")
***)
   	                                val p = answerQuery(buffer,limit)
					val _ = SML_With_C_Interaction.free(buffer)
                                        val chars = SML_With_C_Interaction.makeCharList(p)
(***
					val _ = print("\nRaw XSB answer to this query: " ^ (implode chars) ^ "\n")
***)
                    	  	        val _ = SML_With_C_Interaction.free(p)
                                        val vars = AT.getVarsInOrderLst(terms)
                                    in
                                      (case chars of
                                         #"!"::rest => Semantics.primError(implode rest)
                                       | _ =>  if (limit < 1) then SV.listVal([SV.true_val,SV.listVal([])]) else getSubs(vars,chars))
                                    end
                   | _ => let val buffer = SML_With_C_Interaction.mallocChars(1000000)
                              val (i,vars) = writePrologListVal(buffer,0,v1)
(**
			      val _ = print("\nQuery vars in order: " ^ (Basic.printListStr1(vars,ATV.toStringDefault,",")) ^ "\n")
**)
 			      val i' = writeOut(".",buffer,i)
                              val _ = SML_With_C_Interaction.setChar(buffer,i',SML_With_C_Interaction.null_char)
(**
 			      val term_str = SML_With_C_Interaction.makeSmlString(buffer)
			      val _ = print("\nAbout to issue the following query: " ^ term_str ^ "\n")
***)
                              val p = answerQuery(buffer,limit)
 			      val _ = SML_With_C_Interaction.free(buffer)
                              val chars = SML_With_C_Interaction.makeCharList(p)
(***
			      val _ = print("\nRaw query answer: " ^ (implode chars) ^ "\n")
***)
                    	      val _ = SML_With_C_Interaction.free(p)
                          in
                             (case chars of
                                 #"!"::rest => Semantics.primError(implode rest)
                              | _ => if (limit < 1) then SV.listVal([SV.true_val,SV.listVal([])])  else getSubs(vars,chars))
                          end
                 )
                 | _ => Semantics.primError(Semantics.wrongArgKind(N.queryPrologFun_name,1,Semantics.listLCType,v1))))
    end
  end;


(***
val _ = TopEnv.updateTopValEnvWithNewPrimBFun(Symbol.symbol("query"),prologQueryPropsPrimBFun);
***)

val _ = TopEnv.updateTopValEnvLstOldAndFast([(N.queryPrologFun_symbol,SV.funVal(prologQueryFun,N.queryPrologFun_name,
                                             TopEnv.default_fv_pa_for_procs 1))]);


fun execPrologCommandPrimUFun(v,env,_) = 
  (case SV.isStringValConstructive(v) of
       SOME(cmd) => (execXSBCommand(cmd);print("\nOK.\n");SV.unitVal)
     | _ => Semantics.primError(Semantics.wrongArgKind("exec-cmd",1,Semantics.stringLCType,v)));

val _ = TopEnv.updateTopValEnvWithNewPrimUFun(S.symbol("exec-cmd"),execPrologCommandPrimUFun);

end;
