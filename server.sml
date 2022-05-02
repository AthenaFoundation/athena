(*======================================================================

A function (Server.makeServerFun) that creates an Athena TCP server, which
can be hit by any TCP client (written in any language), local or remote. 

=======================================================================*)

structure Server = 

struct 

open Semantics

fun makeServerFun([termVal(t),cv],env,ab) = 
     (case AthTerm.getNumVal(t) of                  
       SOME(A.int_num(input_buffer_size,_),_) => 
        (case cv of
          closUFunVal(_) => 
            let fun processString(str) = let val ath_str = MLStringToAthString(str)
                                             val ath_result = evalClosure(cv,[ath_str],ab,NONE)
                                         in       
                                           (case isStringValConstructive(ath_result) of
                                               SOME(str') => str'
                                             | _ => primError("Wrong type of procedure given as argument to "^Names.makeServerFun_name^
                                                              ".\nThe procedure must take a string and return a string."))
                                         end   
                fun runServerFun([termVal(pt)],env,ab) = 
                      let val serverFun = Socket.makeServer(input_buffer_size,processString) 
                          val port = (case AthTerm.getNumVal(pt) of
                                         SOME(A.int_num(p,_),_) => p
                                       | _ => primError("A port number (numeral) was expected here"))
                          val _ = serverFun(port)
                      in
                         unitVal 
                      end handle _ => primError("Socket connection error")
            in 
               funVal(runServerFun,"run-server",default_fv_pa_for_procs 1)
            end
       | _ =>  primError(wrongArgKind(Names.makeServerFun_name,2,closUFunLCType,cv)))
       | _  => primError("A positive numeral was expected here"))
 | makeServerFun([v1,v2],env,ab) = 
    primError("Wrong types of values given as arguments to "^Names.makeServerFun_name^
              ".\nThe first argument must be a positive numeral and the second a unary closure.")
 | makeServerFun(vals,env,ab) = 
      primError(wrongArgNumber(N.makeServerFun_name,length(vals),2))

end