(*======================================================================

This file defines the main Parse structure based on the Yacc and Lex specs. 

=======================================================================*)

structure Parse : sig val parse: string -> AbstractSyntax.user_input list   
                      val parse_from_stream: TextIO.instream -> AbstractSyntax.user_input list    
                      val setLinePos: int * int -> unit 
                      val parse_from_string: string -> AbstractSyntax.user_input list   
                      end  =
struct 
structure AthenaLrVals = AthenaLrValsFun(structure Token = LrParser.Token)
structure Lex = AthenaLexFun(structure Tokens = AthenaLrVals.Tokens)
structure AthenaP = Join(structure ParserData = AthenaLrVals.ParserData
                         structure Lex=Lex
                         structure LrParser = LrParser)

fun setLinePos(l,p) = (Lex.UserDeclarations.lines := l;Lex.UserDeclarations.pos := p)

fun parse filename =
      let val _ = (ErrorMsg.reset(); ErrorMsg.file_name := filename)
          val file = TextIO.openIn filename
          fun get _ = TextIO.input file
          val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
          fun parseerror(s,p1,p2) = ErrorMsg.error(s,p1,p2)
          val (pre_exp, _) = AthenaP.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
          pre_exp
      end handle LrParser.ParseError => raise ErrorMsg.Error

fun parse_from_stream(is) = 
      let val _ = ErrorMsg.reset();
          fun get _ = TextIO.input is
          fun parseerror(s,p1,p2) = ErrorMsg.error(s,p1,p2)
          val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
          val (pre_exp,_) = AthenaP.parse(30,lexer,parseerror,())
      in
           pre_exp
      end handle LrParser.ParseError => raise ErrorMsg.Error

fun parse_from_string(str) = parse_from_stream(TextIO.openString(str))
  
end

structure InfixParse =
struct

open AbstractSyntax

datatype tok = LPAREN | RPAREN | LBRACK | RBRACK | COLON | SQUOTE | exp_tok of AbstractSyntax.expression | LOGICAL_AND | LOGICAL_OR | 
               SENT_CON of Symbol.symbol | QUANT of Symbol.symbol | ID of Symbol.symbol 

fun unparseExp(unitExp(_)) = [LPAREN,RPAREN]
  | unparseExp(logicalAndExp({args,...})) = 
     let val L = map unparsePhrase args
         val toks = Basic.foldr(op@,[],L)
     in 
        (LPAREN::LOGICAL_AND::toks)@[RPAREN]
     end
  | unparseExp(logicalOrExp({args,...})) = 
     let val L = map unparsePhrase args
         val toks = Basic.foldr(op@,[],L)
     in 
        (LPAREN::LOGICAL_OR::toks)@[RPAREN]
     end
  | unparseExp(appExp({proc,args,...})) = 
     let val toks = Basic.foldr(op@,[],map unparsePhrase args)
     in
        [LPAREN]@(unparsePhrase proc)@toks@[RPAREN]
     end
  | unparseExp(listExp({members,...})) = 
     let val toks = Basic.foldr(op@,[],map unparsePhrase members)
     in
       [LBRACK]@toks@[RBRACK]
     end
 | unparseExp(e) = [exp_tok(e)]
and unparseDed(_) = []
and unparsePhrase(exp(e)) = unparseExp(e)
  | unparsePhrase(ded(d)) = unparseDed(d)

exception LexError of string

fun lexError(str) = raise LexError(str)

fun getKwd(#"("::rest) = SOME(LPAREN,rest)
  | getKwd(#")"::rest) = SOME(RPAREN,rest)
  | getKwd(#"["::rest) = SOME(LBRACK,rest)
  | getKwd(#"]"::rest) = SOME(RBRACK,rest)
  | getKwd(#":"::rest) = SOME(COLON,rest)
  | getKwd(#"'"::rest) = SOME(SQUOTE,rest)
  | getKwd(_) = NONE

fun legalIdChar(_) = true

fun getId(clist) = 
  let fun loop([],res) = SOME(Symbol.symbol(implode(rev res)),[])
        | loop(clist as c::more,res) = if legalIdChar(c) then loop(more,c::res) else SOME(Symbol.symbol(implode(rev res)),clist)
  in
     (case clist of 
         [] => lexError("An identifier was expected here.")
       | c::more => if legalIdChar(c) then loop(clist,[]) else lexError("An identifier was expected here."))
  end

datatype tt = tttt of AbstractSyntax.expression

fun buildSort(_) = raise Basic.Never
                   
fun getAVar((#"?")::rest) = (case getId(rest) of 
                                SOME(sym,rest') => SOME(AthTermVar.athTermVar(Symbol.name(sym)),rest')
                              | _ => NONE)
  | getAVar(_) = NONE

end