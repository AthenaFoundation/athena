(*======================================================================

Satisfiability-related code, particularly code needed for converting to
CNF and to/from the data formats used by SOTA SAT solvers (e.g., DIMACS).

=======================================================================*)

structure Sat = 

struct

structure S = Symbol

datatype prop = atom of S.symbol
              | neg of prop
	      | conj of prop * prop
	      | disj of prop * prop  
              | cond of prop * prop
	      | equiv of prop * prop

fun disjLst([p1,p2]) = disj(p1,p2)
  | disjLst(p1::p2::rest) = disj(p1,disjLst(p2::rest))

fun conjLst([p1,p2]) = conj(p1,p2)
  | conjLst(p1::p2::rest) = conj(p1,conjLst(p2::rest))

fun propToString(atom(sym)) = S.name(sym)
  | propToString(neg(p)) = "not("^(propToString p)^")"
  | propToString(conj(p1,p2)) = "and("^(propToString p1)^","^(propToString p2)^")"
  | propToString(disj(p1,p2)) = "or("^(propToString p1)^","^(propToString p2)^")"
  | propToString(cond(p1,p2)) = "if("^(propToString p1)^","^(propToString p2)^")"
  | propToString(equiv(p1,p2)) = "iff("^(propToString p1)^","^(propToString p2)^")"

val (comma,lp,rp,var_prefix) = (",","(",")","C")

val sat_solver = ref "rsat"

val cnf_converter = ref "E"

fun setSatSolver(str) = sat_solver := str

fun getSatSolver() = !sat_solver

fun setCnfConverter(str) = cnf_converter := str

fun getCnfConverter() = !cnf_converter

fun makeCommand(in_file_name,out_file_name) = 
      if ((!sat_solver) = "minisat") then  
         "minisat -verb=0 "^in_file_name^" "^out_file_name
      else
         "rsat "^in_file_name^" -s > "^out_file_name

fun makeSpassProps(props) = 
 let val index = ref 1
     val atom_count = ref 0
     val hash_table: string S.htable = S.makeHTable()
     val inverse_hash_table: S.symbol S.htable = S.makeHTable()
     fun makeBoolVar() = let val res = var_prefix^(Int.toString(!index))
                             val _ = Basic.inc(index)
                         in
                            res
                         end
     fun f(atom(sym),slist) = (case S.find(hash_table,sym) of 
                                       SOME(bool_var) => 
                                         (bool_var,slist)
                                     | _ => let val _ = Basic.inc(atom_count)
           					val bvar = makeBoolVar()
                                                val _ = S.insert(hash_table,sym,bvar)
                                                val _ = S.insert(inverse_hash_table,S.symbol(bvar),sym)
                                            in
                                               (bvar,bvar::slist)
                                            end)
       | f(neg(p),slist) = let val (p_str,slist') = f(p,slist)
                           in
                             ("not("^p_str^")",slist')
                           end
       | f(conj(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                    val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("and("^p1_str^comma^p2_str^")",slist2)
                                end
       | f(disj(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                    val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("or("^p1_str^comma^p2_str^")",slist2)
                                end
       | f(cond(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                    val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("implies("^p1_str^comma^p2_str^")",slist2)
                                end
       | f(equiv(p1,p2),slist) = f(conj(cond(p1,p2),cond(p2,p1)),slist)
 and  fLst([],slist,res) = (res,slist)
    | fLst(p::more,slist,res) = let val (p_str,slist') = f(p,slist)
                                in
                                   fLst(more,slist',p_str::res)
                                end
 val (res,slist) = fLst(props,[],[])
 in

    {p_strings=res,sym_list=slist,htable=hash_table,
    inverse_htable = inverse_hash_table,leaf_count=(!atom_count)}

 end

fun makeTPTPFormulas(props) = 
 let val index = ref 1
     val atom_count = ref 0
     val hash_table: string S.htable = S.makeHTable()
     val inverse_hash_table: S.symbol S.htable = S.makeHTable()
     fun makeBoolVar() = let val res = var_prefix^(Int.toString(!index))
                             val _ = Basic.inc(index)
                         in
                            res
                         end
     fun f(atom(sym),slist) = (case S.find(hash_table,sym) of 
                                       SOME(bvar) => 
                                         (bvar^"()",slist)
                                     | _ => let val _ = Basic.inc(atom_count)
           					val bvar = makeBoolVar()
                                                val _ = S.insert(hash_table,sym,bvar)
                                                val _ = S.insert(inverse_hash_table,S.symbol(bvar),sym)
                                            in
                                               (bvar^"()",bvar::slist)
                                            end)
       | f(neg(p),slist) = let val (p_str,slist') = f(p,slist)
                           in
                             (" ~ ("^p_str^")",slist')
                           end
       | f(conj(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                    val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("("^p1_str^" & "^p2_str^")",slist2)
                                end
       | f(disj(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                    val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("("^p1_str^" | "^p2_str^")",slist2)
                                end
       | f(cond(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                    val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("("^p1_str^" => "^p2_str^")",slist2)
                                end
       | f(equiv(p1,p2),slist) = let val (p1_str,slist1) = f(p1,slist)
                                     val (p2_str,slist2) = f(p2,slist1)
                                in
 				   ("("^p1_str^" <=> "^p2_str^")",slist2)
                                end
 and  fLst([],slist,res) = (res,slist)
    | fLst(p::more,slist,res) = let val (p_str,slist') = f(p,slist)
                                in
                                   fLst(more,slist',p_str::res)
                                end
 val (res,slist) = fLst(props,[],[])
 in
    {p_strings=res,sym_list=slist,htable=hash_table,
    inverse_htable = inverse_hash_table,leaf_count=(!atom_count)}

 end

fun findAndSkipLine(in_stream,l) = let fun loop() = 
           	  		         let val line =  TextIO.inputLine(in_stream)
			                 in
                                            if line = "" orelse line = l then ()
	   			            else loop()
 				         end
			           in 
				      loop()
			           end

fun isSkolemConstant(str)  = (if String.substring(str,0,2) = "Sk" then true else false) handle _ => false

fun makeAssignment(asgn_line,inverse_htable) = 
              let val ht_asgn: bool S.htable = S.makeHTable()
                  val minus_sign = #"-"
                  fun processStingVal(str) = 
                         let val (var_index,value) = 
                                     if String.sub(str,0) = minus_sign then 
                                        (var_prefix^(String.substring(str,1,String.size(str)-1)),false)
                                     else (var_prefix^str,true)
                         in
                            (case S.find(inverse_htable,S.symbol(var_index)) of 
                                SOME(sym) => S.insert(ht_asgn,sym,value)
                              | _ => ())
                         end
                 fun pred(c) = c = #" " orelse c = #"\n"
                 val strings = String.tokens pred asgn_line
                 val _ = List.app processStingVal strings
              in
                 ht_asgn
              end

fun getMiniSatResult(minisat_file_stream,inverse_htable) = 
  let val first_line = TextIO.inputLine(minisat_file_stream)
  in
     (case (String.tokens (fn c => c = #" " orelse c = #"\n") first_line) of 
        ("UNSAT"::_) => NONE
       | _ => let val asgn_line = TextIO.inputLine(minisat_file_stream)
              in 
                 SOME(makeAssignment(asgn_line,inverse_htable))
              end)
  end

fun firstElement(str) = String.substring(str,0,1)

fun printFile(stream) = 
   let val l =  TextIO.inputLine(stream)
   in 
      if l = "" then () else (print("\nLine: "^l);printFile(stream))
   end

fun getRSatResult(rsat_file_stream,inverse_htable) = 
  let val line = ref ""
      val (done,sat,res) = (ref false,ref false,ref NONE)
      fun allButTheFirstTwo(str) = String.substring(str,2,String.size(str)-2);
      val _ = while (line := TextIO.inputLine(rsat_file_stream);not((!line) = "") andalso not(!done)) do 
               ((case firstElement(!line) of 
                   "s" => let val _::rest = String.tokens (fn c => c = #" " orelse c = #"\n") (!line)
                          in 
                            if hd(rest) = "UNSATISFIABLE" then 
                               (done := true) else ()
                          end
                 | "v" => (res := SOME(makeAssignment(allButTheFirstTwo(!line),inverse_htable));
                           sat := true)
                 | _ => ()))
  in
     if !sat then !res else NONE
  end

fun getSkolemCount(spass_cnf_stream) = 
      let fun debugPrint(s) = ()
          fun continue() = ()
          fun countSkolemConstants(toks) = Basic.countAll(toks,isSkolemConstant)
          fun loop(res,line_num) = 
		 let val line = TextIO.inputLine(spass_cnf_stream)
                     val _ = debugPrint("\nHere's line #"^(Int.toString(line_num))^":\n"^line^"\n")
                 in 
                    if line = "end_of_line.\n" then res
                    else let val toks = String.tokens 
					   (fn c => Basic.isMember(c,[#" ",#"\n",
                                                                      #",",#"(",#")",#"[",#"]"])) line
                             val tokens = if line_num = 1 then tl toks else toks 
                             val _ = (debugPrint("\nHere are the symbol tokens on line #"^
			  	                (Int.toString(line_num))^":\n");
                                      debugPrint(Basic.printListStr(tokens,Basic.id," / ")))
                             val _ = continue()
                             val res' = res+(countSkolemConstants tokens)
                             val next_to_last_tok = List.nth(tokens,List.length(tokens)-2)
                             val _ = debugPrint("\nLast token: "^next_to_last_tok)
                         in 
                            if not(isSkolemConstant(next_to_last_tok)) then res'
                            else loop(res',line_num+1)
                         end
                 end
      in
         loop(0,1)
      end

fun makeAndProcessDimacsFile(cnf_stream:TextIO.instream,dimacs_stream, 
                             dimacs_file_name,minisat_out_file_name,rsat_out_file_name,
                             htable,inverse_htable,leaf_count) = 

  let fun debugPrint(s) = print(s) 
      fun writeDimacsFile(str) = TextIO.output(dimacs_stream,str)
      fun makeDimacsFileFromTPTPCnf() = 
           let fun isClause(line) = (String.substring(line,0,3) = "cnf") handle _ => false  
               fun negativeLiteral(str) = (String.sub(str,0) = #"~") handle _ => false
               val max_evar_index = ref(0)
               fun isELiteral(str) = 
                 let fun pred(c) =  Basic.isMember(c,[#"~",#"_"])
                     val s::_ = String.tokens pred str
                 in
                    if (String.substring(s,0,5) = "epred") then 
                       Int.fromString(String.substring(s,5,String.size(s)-5))
                    else NONE
                 end handle _ => NONE
               fun processLiteral(l) = 
                  let val is_negative = negativeLiteral(l)
                      fun index(i) = String.substring(l,i,String.size(l)-i)
                  in
                     (case isELiteral(l) of
                         SOME(index) =>
                           let val _ = if Int.>(index,(!max_evar_index)) then 
                                          max_evar_index := index
                                       else ()
                               val index' = index + leaf_count
                               val index_str = Int.toString(index')
                           in
                              if is_negative then "-"^index_str^" "
                              else index_str^" "
                           end 
                       | _ => if negativeLiteral(l) then "-"^(index 2)^" " 
                              else (index 1)^" ")
                  end
               fun makeDimacsClauses(res,count) = 
                      let val line = TextIO.inputLine(cnf_stream)
                      in 
                        if line = "" then (res,count)
                        else if not(isClause(line)) then makeDimacsClauses(res,count)
                             else let val toks = String.tokens (fn c => 
					            Basic.isMember(c,[#",",#"|",#")",#"(",#".",#" ",#"\n"]))
                                                    line
                                      val tokens = List.drop(toks,3)
                                      fun loop([],str) = str^" 0\n"
                                        | loop(l::more,str) = loop(more,(processLiteral l)^str)
                                      val clause = loop(tokens,"")
                                  in
                                     makeDimacsClauses(clause::res,count+1)
                                  end
                      end 
               val (clauses,clause_count) = makeDimacsClauses([],0)
               val _ = debugPrint("\nEPROVER introduced "^(Int.toString(!max_evar_index))^" variables...\n")
               val new_leaf_count = leaf_count + (!max_evar_index)               
               val (rsat_bogus_var1,rsat_bogus_var2) = (Int.toString(new_leaf_count+1),
		  		                        Int.toString(new_leaf_count+2))
               val _ = (writeDimacsFile("p cnf "^(Int.toString(new_leaf_count+2))^" "^
                                                 (Int.toString(clause_count+1))^"\n");
                          writeDimacsFile(rsat_bogus_var1^" "^rsat_bogus_var2^" 0\n");
                          List.app writeDimacsFile clauses)
           in
             TextIO.closeOut(dimacs_stream)
           end
      fun makeDimacsFileFromSpassCNF() = 
             let val _ = findAndSkipLine(cnf_stream,"list_of_symbols.\n")     
                 val skolem_count = getSkolemCount(cnf_stream)
                 val _ = debugPrint("\nSKOLEM COUNT: "^(Int.toString(skolem_count))^"\n")
                 val _ = findAndSkipLine(cnf_stream,"list_of_clauses(axioms, cnf).\n")
                 val leaf_count' = leaf_count + 1
                 val new_leaf_count = leaf_count + skolem_count
                 val clause_count = ref 0
                 val offset = new_leaf_count + 2
                 val (rsat_bogus_var1,rsat_bogus_var2) = (Int.toString(new_leaf_count+1),
		 			                  Int.toString(new_leaf_count+2))
                     (* Two slack variables necessary to get around Rsat bug ... *)
                 fun loop([],res) = res^"0\n"
                   | loop([_],res) = res^"0\n"
                   | loop([_,_],res) = res^"0\n"
                   | loop("not"::bvar::more,res) = 
				   if not(isSkolemConstant(bvar)) then 
                                      let val bvar_index = String.substring(bvar,1,String.size(bvar)-1)
                                          val bvar_str = "-"^bvar_index^" "
                                      in
                                         loop(more,bvar_str^res)
                                      end
                                   else  
                                      let val sk_index = String.substring(bvar,3,String.size(bvar)-3)
                                          val bvar_index = (getOpt(Int.fromString(sk_index),0))+leaf_count'
                                          val bvar_str = "-"^(Int.toString(bvar_index))^" "
                                      in
                                         loop(more,bvar_str^res)
                                      end
                   | loop(bvar::more,res) = 
                                   if not(isSkolemConstant(bvar)) then 
                                      let val bvar_index = String.substring(bvar,1,String.size(bvar)-1)
                                          val bvar_str = bvar_index^" "
                                      in
                                         loop(more,bvar_str^res)
                                      end
                                   else  
                                      let val sk_index = String.substring(bvar,3,String.size(bvar)-3)
                                          val bvar_index = (getOpt(Int.fromString(sk_index),0))+leaf_count'
                                          val bvar_str = (Int.toString(bvar_index))^" "
                                      in
                                         loop(more,bvar_str^res)
                                      end
                 fun processClauses(res,count) = 
                             let val line = TextIO.inputLine(cnf_stream)
                             in 
                               if line = "" then (res,count)
                               else let fun pred(c) = c = #"," orelse c = #"(" 
                                                      orelse c = #" " orelse c = #")" orelse c = #"."
                                        val s1::rest = String.tokens pred line
                                    in 
                                      if not(s1 = "clause") then (res,count) else 
                                         let val str = loop(tl(rest),"")
                                         in 
                                            processClauses(str::res,count+1)
                                         end
                                    end
                             end
                 val (clause_lines,clause_count) = processClauses([],0)
                 val _ = (writeDimacsFile("p cnf "^(Int.toString(new_leaf_count+2))^" "^
                                                   (Int.toString(clause_count+1))^"\n");
                          writeDimacsFile(rsat_bogus_var1^" "^rsat_bogus_var2^" 0\n");
                          List.app writeDimacsFile clause_lines)
             in
                TextIO.closeOut(dimacs_stream)
             end
      val out_file_name = if !sat_solver = "rsat" then rsat_out_file_name else minisat_out_file_name
      val _ = if !cnf_converter = "flotter" then makeDimacsFileFromSpassCNF()
              else makeDimacsFileFromTPTPCnf()
      val _ = debugPrint("\nCalling the sat solver...\n")
      val _ = OS.Process.system(makeCommand(dimacs_file_name,out_file_name))
      val out_stream = if !sat_solver = "rsat" then TextIO.openIn(rsat_out_file_name) 
                       else TextIO.openIn(minisat_out_file_name)
      val res = if !sat_solver = "rsat" then getRSatResult(out_stream,inverse_htable)
                else getMiniSatResult(out_stream,inverse_htable)
      val _ = TextIO.closeIn(out_stream)
  in 
     res 
  end
  
fun sat(props) = 
  let fun debugPrint(s) = ()
      val {p_strings,sym_list,htable,inverse_htable,leaf_count} = 
               if !cnf_converter = "flotter" then makeSpassProps(props) 
               else makeTPTPFormulas(props)
      val in_file_name = if !cnf_converter = "flotter" then "input_file.spass" else "input_file.tptp"
      val cnf_file_name = if !cnf_converter = "flotter" then "cnf_output.spass" else "cnf_output.tptp"
      val (dimacs_file,minisat_out_file,rsat_out_file) = 
              ("dimacs_file","minisat_out_file","rsat_out_file")
      val (stream,dimacs_stream) =  (TextIO.openOut(in_file_name),TextIO.openOut(dimacs_file))
      fun writeStream(str) = TextIO.output(stream,str)
      fun writeSpassInputFile() = 
             let val _ = writeStream "begin_problem(convertToCNF).\n\n"       
                 fun writeSymList() =  (writeStream("list_of_symbols.\n");
                                        writeStream("  predicates[");
                                        writeStream(Basic.printListStrCommas(sym_list,fn x => "("^x^",0)"));
                                        writeStream("].\n");
	                                writeStream("end_of_list.\n\n"))
                 val _ = (writeStream("list_of_descriptions.\n");
                          writeStream("name({*Hilbert's eleventh problem*}).\n");
                          writeStream("author({*David Hilbert*}).\n");
	                  writeStream("status(unsatisfiable).\n");
	                  writeStream("description({*LL*}).\n");writeStream("end_of_list.\n\n"))
                val _ = writeSymList()
                val _ = writeStream("list_of_formulae(axioms).\n\n")
                val _ = List.app (fn prop_str => writeStream("\nformula("^prop_str^").")) p_strings
                val _ = (writeStream("\n\nend_of_list.");writeStream("\nend_problem."))
             in
                TextIO.closeOut(stream)
             end
      fun writeTPTPInputFile() = 
           let val axiom_index = ref(0)
               val _ = List.app (fn prop_str => (Basic.inc(axiom_index); 
                                                 writeStream("\nfof(A"^(Int.toString(!axiom_index))^
                                                             ",axiom,"^prop_str^")."))) 
                                p_strings
           in
              TextIO.closeOut(stream)
           end
      val _ = if !cnf_converter = "flotter" then writeSpassInputFile() 
	      else writeTPTPInputFile()
      val _ = debugPrint("\nin_file_name: "^in_file_name^"\ncnf_file_name: "^cnf_file_name^"\n")
      fun makeCommand() = if !cnf_converter = "flotter" then                
                             "SPASS -Flotter "^in_file_name^" > "^cnf_file_name
                          else
                              "eprover --cnf --tstp-format "^in_file_name^" > "^cnf_file_name
      val _ = OS.Process.system(makeCommand())
      val cnf_stream = TextIO.openIn(cnf_file_name)
      val res = makeAndProcessDimacsFile(cnf_stream,dimacs_stream,
					 dimacs_file,minisat_out_file,rsat_out_file,
		  	         htable,inverse_htable,leaf_count)
      val _ = TextIO.closeIn(cnf_stream)
  in
    res
  end

fun showAsgn(asgn_ht) = 
	let val l = S.listItemsi(asgn_ht)
        in 
          "\n"^(Basic.printListStr(l,fn (sym,b) => (S.name(sym))^" --> "^(Basic.boolToString b),"\n")^"\n\n")
         end

fun test(props) = 
     (case sat(props) of 
          NONE => "\nUnsatisfiable.\n" 
        | SOME(asgn_ht) => showAsgn(asgn_ht))

fun testBoolean(props) = 
     (case sat(props) of 
          NONE => false 
        | SOME(asgn_ht) => true)
	
fun isSat(props) = 
     (case sat(props) of 
          NONE => false 
        | SOME(asgn_ht) => true)

end (* Of structure Sat *)
