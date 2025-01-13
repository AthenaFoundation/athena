functor AthenaLexFun(structure Tokens:Athena_TOKENS)  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
STRING | EOL_COMMENT | tates | INITIAL
    structure UserDeclarations = 
      struct

(*==================================================

Athena's lexer.

===================================================*)

type svalue = Tokens.svalue 

type pos = int * int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val open_comments =  ref 0

val pos = ref 1
val lines = ref 1

fun resetLines() = (lines := 1;pos := 0)
fun incLines() = (lines := !lines + 1; pos := 0)
fun incPos(i) = pos := !pos + i
fun currentPos() = (!lines,!pos)
fun currentPosWithFileInfo() = {line=(!lines),file=(!Paths.current_file),pos=(!pos)}
fun dxCurrentPos(x) = (!lines,!pos+x)
val code_string = ref ""
val char_code_list: int list ref = ref []
val temp_string = ref ""
val begin_string_pos = ref (0,0)
val open_string = ref false

val _ = Position.init()

fun isReserved(str,leftp:pos as (l,p)) = 
    let fun getPos(count) = (leftp,(l,p+count-1))
        fun doReserved "assume" = (true,Tokens.ASSUME(getPos(6))) |
            doReserved "private" = (true,Tokens.PRIVATE(getPos(7))) |
            doReserved "bind" = (true,Tokens.NAME(getPos(4))) |
            doReserved "as" = (true,Tokens.NAME(getPos(2))) |
            doReserved "check" = (true,Tokens.CHECK(getPos(5))) |
            doReserved "dcheck" = (true,Tokens.DCHECK(getPos(6))) |
            doReserved "the" = (true,Tokens.THE(getPos(3))) |
            doReserved "Fun" = (true,Tokens.FUN(getPos(3))) |
            doReserved "over" = (true,Tokens.OVER(getPos(4))) |
            doReserved "for" = (true,Tokens.FOR(getPos(3))) |
            doReserved "set-precedence" = (true,Tokens.SET_PRECEDENCE(getPos(14))) | 
            doReserved "open" = (true,Tokens.OPEN_MODULE(getPos(4))) | 
            doReserved "open-module" = (true,Tokens.OPEN_MODULE(getPos(11))) | 
            doReserved "extend-module" = (true,Tokens.EXTEND_MODULE(getPos(13))) | 
            doReserved "left-assoc" = (true,Tokens.LEFT_ASSOC(getPos(10))) | 
            doReserved "right-assoc" = (true,Tokens.RIGHT_ASSOC(getPos(11))) | 
            doReserved "assert" = (true,Tokens.ASSERT(getPos(6))) | 
            doReserved "assert*" = (true,Tokens.ASSERT_CLOSE(getPos(7))) | 
            doReserved "retract" = (true,Tokens.RETRACT(getPos(7))) | 
            doReserved "load-file" = (true,Tokens.LOAD_FILE(getPos(9))) |
            doReserved "load" = (true,Tokens.LOAD_FILE(getPos(4))) |
            doReserved "overload" = (true,Tokens.OVERLOAD(getPos(8))) |
            doReserved "overload-inv" = (true,Tokens.OVERLOAD_INV(getPos(12))) |
            doReserved "expand-input" = (true,Tokens.EXPAND_INPUT(getPos(12))) |
            doReserved "transform-output" = (true,Tokens.TRANSFORM_OUTPUT(getPos(16))) |
            doReserved "START_LOAD" = (true,Tokens.START_LOAD(getPos(10))) |
            doReserved "END_LOAD" = (true,Tokens.END_LOAD(getPos(8))) |
            doReserved "exit-athena" = (true,Tokens.EXIT_ATHENA(getPos(11))) |
            doReserved "expand-next-proof" = (true,Tokens.EXPAND_NEXT_PROOF(getPos(17))) |
            doReserved "print-call-stack" = (true,Tokens.PRINT_STACK_TRACE(getPos(16))) |
            doReserved "add-demon" = (true,Tokens.ADD_DEMON(getPos(9))) |
            doReserved "add-demons" = (true,Tokens.ADD_DEMONS(getPos(10))) |
            doReserved "set-flag" = (true,Tokens.SET_FLAG(getPos(8))) |
            doReserved "define-symbol" = (true,Tokens.DEFINE_SYMBOL(getPos(13))) | 
            doReserved "define-sort" = (true,Tokens.DEFINE_SORT(getPos(11))) | 
            doReserved "clear-assumption-base" = (true,Tokens.CLEAR(getPos(21))) |
            doReserved "assume-let" = (true,Tokens.ASSUME_LET(getPos(10))) | 
            doReserved "lambda" = (true,Tokens.FUNCTION(getPos(6))) | 
            doReserved "provided" = (true,Tokens.PROVIDED(getPos(8))) | 
            doReserved "method" = (true,Tokens.METHOD(getPos(6))) | 
            doReserved "define" = (true,Tokens.DEFINE(getPos(3))) | 
            doReserved "define*" = (true,Tokens.DEFINE_STAR(getPos(11))) | 
            doReserved "define-memoized" = (true,Tokens.DEFINE_MEMOIZED(getPos(15))) | 
            doReserved "primitive-method" = (true,Tokens.RULE(getPos(16))) | 
            doReserved "structure" = (true,Tokens.STRUCTURE(getPos(9))) | 
            doReserved "structures" = (true,Tokens.STRUCTURES(getPos(10))) | 
            doReserved "datatype" = (true,Tokens.DATATYPE(getPos(8))) | 
            doReserved "datatypes" = (true,Tokens.DATATYPES(getPos(9))) | 
            doReserved "domain" = (true,Tokens.DOMAIN(getPos(6))) | 
            doReserved "domains" = (true,Tokens.DOMAINS(getPos(7))) | 
            doReserved "subsort" = (true,Tokens.SUBSORT(getPos(7))) | 
            doReserved "subsorts" = (true,Tokens.SUBSORTS(getPos(8))) | 
            doReserved "true-introduction" = (true,Tokens.TRUE_INTRODUCTION(getPos(17))) | 
            doReserved "declare" = (true,Tokens.DECLARE(getPos(7))) | 
            doReserved "ddeclare" = (true,Tokens.DDECLARE(getPos(8))) | 
            doReserved "val-of" = (true,Tokens.VAL_OF(getPos(6))) | 
            doReserved "suppose-absurd" = (true,Tokens.SUPPOSE_ABSURD(getPos(14))) |
            doReserved "suppose-absurd-let" = (true,Tokens.SUPPOSE_ABSURD_LET(getPos(18))) |
            doReserved "dmatch" = (true,Tokens.DMATCH(getPos(6))) |
            doReserved "match" = (true,Tokens.MATCH(getPos(5))) | 
            doReserved "let:" = (true,Tokens.LET_UPPER(getPos(3))) | 
            doReserved "let" = (true,Tokens.LET(getPos(3))) | 
            doReserved "letrec" = (true,Tokens.LETREC(getPos(6))) |
            doReserved "dlet" = (true,Tokens.DLET(getPos(4))) |
            doReserved "dletrec" = (true,Tokens.DLETREC(getPos(7))) |
            doReserved "apply-method" = (true,Tokens.APPLY_METHOD(getPos(12))) |
            doReserved "begin" = (true,Tokens.BEGIN(getPos(5))) |
            doReserved "{" = (true,Tokens.BEGIN(getPos(1))) |
            doReserved "PROVE" = (true,Tokens.PROVE(getPos(5))) |
            doReserved "seq" = (true,Tokens.SEQ(getPos(3))) |
            doReserved "dseq" = (true,Tokens.DSEQ(getPos(4))) |
            doReserved "end" = (true,Tokens.END(getPos(3))) |
            doReserved "}" = (true,Tokens.END(getPos(1))) |
            doReserved "on" = (true,Tokens.ON(getPos(2))) |
            doReserved "while" = (true,Tokens.WHILE(getPos(5))) |
            doReserved "where" = (true,Tokens.WHERE(getPos(5))) |
            doReserved "by-induction" = (true,Tokens.INDUCTION(getPos(12))) |
            doReserved "use-term-parser" = (true,Tokens.USE_TERM_PARSER(getPos(15))) |
            doReserved "use-prop-parser" = (true,Tokens.USE_PROP_PARSER(getPos(15))) |
            doReserved "datatype-cases" = (true,Tokens.DATATYPE_CASES(getPos(14))) |
            doReserved "datatype-cases-on-term" = (true,Tokens.DATATYPE_CASES_ON_TERM(getPos(14))) |
            doReserved "structure-cases" = (true,Tokens.STRUCTURE_CASES(getPos(15))) |
            doReserved "meta-id" = (true,Tokens.META_ID(getPos(7))) |
            doReserved "try" = (true,Tokens.TRY(getPos(3))) |
            doReserved "dtry" = (true,Tokens.DTRY(getPos(3))) |
            doReserved "define-fun" = (true,Tokens.DEFINE_FUN(getPos(10))) |
            doReserved "BY" = (true,Tokens.BY(getPos(2))) |
            doReserved "by" = (true,Tokens.BY(getPos(2))) |
            doReserved "conclude" = (true,Tokens.CONCLUDE(getPos(8))) |
            doReserved "applying" = (true,Tokens.APPLYING(getPos(8))) |
            doReserved "from" = (true,Tokens.FROM(getPos(4))) |
            doReserved "pick-any" = (true,Tokens.PICK_ANY(getPos(8))) |
            doReserved "pick-witness" = (true,Tokens.PICK_WITNESS(getPos(12))) |
            doReserved "pick-witnesses" = (true,Tokens.PICK_WITNESSES(getPos(14))) |
            doReserved "_" = (true,Tokens.ANY_PAT(getPos(5))) |
            doReserved "else" = (true,Tokens.ELSE(getPos(4))) |
            doReserved "list-of" = (true,Tokens.LIST(getPos(7))) |
            doReserved "by-cases" = (true,Tokens.BY_CASES(getPos(8))) |
            doReserved "cell-of" = (true,Tokens.CELL(getPos(7))) |
            doReserved "cell" = (true,Tokens.MAKE_CELL(getPos(4))) |
            doReserved "ref" = (true,Tokens.REF(getPos(3))) |
            doReserved "split" = (true,Tokens.SPLIT_PAT(getPos(5))) |
            doReserved "re-?" = (true,Tokens.RE_OPTIONAL(getPos(4))) |
            doReserved "re-*" = (true,Tokens.RE_STAR(getPos(4))) |
            doReserved "re-+" = (true,Tokens.RE_PLUS(getPos(4))) |
            doReserved "re-lit" = (true,Tokens.RE_LIT(getPos(6))) |
            doReserved "re-range" = (true,Tokens.RE_RANGE(getPos(8))) |
            doReserved "re-rep" = (true,Tokens.RE_REP(getPos(6))) |
            doReserved "set!" = (true,Tokens.SET(getPos(4))) |
            doReserved "BOP" = (true,Tokens.BIN_OP(getPos(3))) |
            doReserved "OP" = (true,Tokens.OP(getPos(2))) |
            doReserved "module" = (true,Tokens.MODULE(getPos(6))) |
            doReserved "vector-set!" = (true,Tokens.VECTOR_SET(getPos(11))) |
            doReserved "vector-sub" = (true,Tokens.VECTOR_SUB(getPos(10))) |
            doReserved "make-vector" = (true,Tokens.VECTOR_INIT(getPos(11))) |
            doReserved "generalize-over" = (true,Tokens.GEN_OVER(getPos(15))) |
            doReserved "specialize" = (true,Tokens.SPECIALIZE(getPos(10))) |
            doReserved "ex-generalize" = (true,Tokens.EX_GENERALIZE(getPos(13))) |
            doReserved "with-witness" = (true,Tokens.WITH_WITNESS(getPos(12))) |
            doReserved "with-predicate" = (true,Tokens.WITH_PREDICATE(getPos(14))) |
            doReserved "with-keys" = (true,Tokens.WITH_KEYS(getPos(9))) |
            doReserved "some-var" = (true,Tokens.SOME_VAR(getPos(8))) |
            doReserved "some-sentence" = (true,Tokens.SOME_PROP(getPos(13))) |
            doReserved "some-list" = (true,Tokens.SOME_LIST(getPos(9))) |
            doReserved "some-cell" = (true,Tokens.SOME_CELL(getPos(9))) |
            doReserved "some-quant" = (true,Tokens.SOME_QUANT(getPos(10))) |
            doReserved "some-sent-con" = (true,Tokens.SOME_PROP_CON(getPos(15))) |
            doReserved "some-term" = (true,Tokens.SOME_TERM(getPos(9))) |
            doReserved "some-atom" = (true,Tokens.SOME_ATOM(getPos(9))) |
            doReserved "some-sent" = (true,Tokens.SOME_PROP(getPos(9))) |
            doReserved "some-proc" = (true,Tokens.SOME_FUNCTION(getPos(9))) |
            doReserved "some-method" = (true,Tokens.SOME_METHOD(getPos(11))) |
            doReserved "some-symbol" = (true,Tokens.SOME_SYMBOL(getPos(11))) |
            doReserved "some-sub" = (true,Tokens.SOME_SUB(getPos(8))) |
            doReserved "some-table" = (true,Tokens.SOME_TABLE(getPos(10))) |
            doReserved "some-map" = (true,Tokens.SOME_MAP(getPos(8))) |
            doReserved "some-char" = (true,Tokens.SOME_CHAR(getPos(9))) |
            doReserved "some-vector" = (true,Tokens.SOME_VECTOR(getPos(11))) |
            doReserved "add-path" = (true, Tokens.ADD_PATH(getPos(8))) |
            doReserved _ = (false,Tokens.ASSUME((0,0),(0,0)))
      in
          doReserved(str) 
    end

fun doId(str,left_pos:pos as (l,p)) =  
                           let val (flag,tok) = isReserved(str,left_pos) 
                               fun isPrivateID(str) = (str = Names.lookUpEnvBindingFun_name)
                           in
                               if flag then tok else 
					 if isPrivateID(str) then Tokens.PRIVATE_ID(str,left_pos,(l,p+size(str)-1))
 				         else Tokens.ID(str,left_pos,(l,p+size(str)-1))
                          end                        

fun doAnyID(str,left_pos:pos as (l,p)) =  Tokens.ID(str,left_pos,(l,p+size(str)-1))

local
open Int

fun intExp(a:int,b:int) = if (b <= 0) then 1 else a*intExp(a,b-1)

fun digit_val(c) = ord(c) - ord(#"0")

fun conv([],_,sum) = sum |
    conv(c::rest,pos,sum) = conv(rest,pos-1,sum+(digit_val(c)*intExp(10,pos)))
in
   fun str2int(str) = 
       conv(explode(str),size(str)-1,0)
end

fun getEscChar(char_list) =
     let val tail = tl(char_list)
         val first = ord(hd(tail))
     in
        if (first >= 48) andalso (first <= 57) then
           (case Int.fromString(implode(tail)) of SOME(i) => i | _ => ~1)
        else 
           if first = 94 then
              let val c = ord(hd(tl(tail))) in
                 (case c of
                     64 => 0
                   | 91 => 27
                   | 93 => 29
                   | 47 => 28
                   | 94 => 30
                   | 95 => 31
                   | _ => (if ((c >= 65) andalso (c <= 90)) then 
                               c - 64
                           else ~1))
              end
           else
           (case first of 
               92 => 92
             | 34 => 34
             | 97 => 7
             | 98 => (if null(tl(tail)) then 8 else 32)
             | 102 => 12
             | 110 => 10
             | 114 => 13
             | 116 => 9
             | 118 => 11
             | _ => ~1)
     end

fun error(str,pos_opt) = (open_comments:= 0;open_string := false;pos := 0; lines := 1;
                          raise AbstractSyntax.LexError(str,pos_opt))

fun inc(i) = i := !i + 1

fun dec(i) = i := !i - 1

fun eof() = (if ((!open_comments) > 0) then (open_comments := 0;
                                             error("unclosed comment.",NONE))
                                 else ();
             if !open_string then 
                  (open_string := false; 
                  error("unclosed string",NONE)) 
             else ();
             pos := 0;
             lines := 1;
             Tokens.EOF((0,0),(0,0)))


      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
Vector.fromList []
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ()) = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = List.map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (incPos(size(yytext));continue())
      end
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incLines();continue()))
fun yyAction2 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);begin_string_pos := (!lines,!pos);
                 open_string := true;temp_string := "";
                  YYBEGIN STRING; continue()))
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(4);resetLines();Tokens.EOF(currentPos(),dxCurrentPos(3))))
fun yyAction4 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(2);Tokens.MAP_BEGIN(currentPos(),dxCurrentPos(1))))
fun yyAction5 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(2);Tokens.MAP_END(currentPos(),dxCurrentPos(1))))
fun yyAction6 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(2);Tokens.EOF(currentPos(),dxCurrentPos(1))))
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(3);resetLines();Tokens.EOF(currentPos(),dxCurrentPos(2))))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(8);Tokens.EOF(currentPos(),dxCurrentPos(7))))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.LPAREN(currentPos(),dxCurrentPos(0))))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.RPAREN(currentPos(),dxCurrentPos(0))))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.LEFT_BRACKET(currentPos(),dxCurrentPos(0))))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.RIGHT_BRACKET(currentPos(),dxCurrentPos(0))))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.LEFT_CURLY_BRACE(currentPos(),dxCurrentPos(0))))
fun yyAction14 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.RIGHT_CURLY_BRACE(currentPos(),dxCurrentPos(0))))
fun yyAction15 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(2);Tokens.LOGICAL_AND(currentPos(),dxCurrentPos(1))))
fun yyAction16 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (let val res = doId(yytext,dxCurrentPos(1))
                          in
                             (incPos(size(yytext));res) 
                          end)
      end
fun yyAction17 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(2);Tokens.ID("::",currentPos(),dxCurrentPos(0))))
fun yyAction18 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.COLON(currentPos(),dxCurrentPos(0))))
fun yyAction19 (strm, lastMatch : yymatch) = (yystrm := strm;
      (let val res = Tokens.LOGICAL_OR(currentPos(),dxCurrentPos(1))
                     in (incPos(1);res) end))
fun yyAction20 (strm, lastMatch : yymatch) = (yystrm := strm;
      (let val res = Tokens.ASGN(currentPos(),dxCurrentPos(1))
                  in (incPos(2);res) end))
fun yyAction21 (strm, lastMatch : yymatch) = (yystrm := strm;
      (let val res = Tokens.ARROW(currentPos(),dxCurrentPos(1))
                  in (incPos(2);res) end))
fun yyAction22 (strm, lastMatch : yymatch) = (yystrm := strm;
      (let val res = Tokens.FUN_ARROW(currentPos(),dxCurrentPos(1))
                  in (incPos(2);res) end))
fun yyAction23 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.QMARK(currentPos(),dxCurrentPos(0))))
fun yyAction24 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.SEMI_COLON(currentPos(),dxCurrentPos(0))))
fun yyAction25 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.EXCL_MARK(currentPos(),dxCurrentPos(0))))
fun yyAction26 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.QUOTE_SYMBOL(currentPos(),dxCurrentPos(0))))
fun yyAction27 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.ID("~",currentPos(),dxCurrentPos(0))))
fun yyAction28 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);Tokens.COMMA(currentPos(),dxCurrentPos(0))))
fun yyAction29 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (let val res = doId(yytext,dxCurrentPos(1))
                          in
                             (incPos(size(yytext));res) 
                          end)
      end
fun yyAction30 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (incPos(1);
                          let val res = Tokens.CHARACTER(ord(hd(tl(explode(yytext)))),
                                                         currentPos(),dxCurrentPos(1))
                              val _ = incPos(1) 
                          in res 
                          end)
      end
fun yyAction31 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (let val code = getEscChar(tl(explode(yytext)))
                             val res = Tokens.CHARACTER(code,dxCurrentPos(1),
                                                        dxCurrentPos(size(yytext)))
                             val _ = incPos(size(yytext)) in res end)
      end
fun yyAction32 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incPos(1);YYBEGIN EOL_COMMENT; continue()))
fun yyAction33 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (incPos(size(yytext));
               if ord(hd(explode(yytext))) = 96 then 
                  error("Illegal character constant: "^yytext,SOME(currentPosWithFileInfo()))
               else error("Illegal character found and ignored: "^yytext,SOME(currentPosWithFileInfo()));
               continue())
      end
fun yyAction34 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN INITIAL; 
                           let val _ = incPos(1)
                               val _ = temp_string := !code_string
                               val _ = code_string := ""
                               val _ = open_string := false;
                               val res = Tokens.STRING(rev(!char_code_list),
                                                      !begin_string_pos,
                                                      (!lines,!pos))
                               val _ = char_code_list := []
                           in
                              res
                           end))
fun yyAction35 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (code_string := !code_string^yytext;
       incPos(size(yytext));
       char_code_list := ord(hd(explode(yytext)))::(!char_code_list);
       continue())
      end
fun yyAction36 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (code_string := !code_string^yytext;
       incPos(size(yytext));
       char_code_list := getEscChar(explode(yytext))::(!char_code_list);
       continue())
      end
fun yyAction37 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (code_string := !code_string^yytext;
       incPos(1);
       char_code_list := 32::(!char_code_list);
       continue())
      end
fun yyAction38 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (code_string := !code_string^yytext; 
                incLines(); 
                continue())
      end
fun yyAction39 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (incPos(size(yytext));
              error("Illegal character found inside string constant: "^yytext,
                    SOME(currentPosWithFileInfo()));
              continue())
      end
fun yyAction40 (strm, lastMatch : yymatch) = (yystrm := strm;
      (incLines();YYBEGIN INITIAL;continue()))
fun yyAction41 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (incPos(size(yytext));continue())
      end
fun yyQ48 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ49 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction5(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction5(strm, yyNO_MATCH)
      (* end case *))
fun yyQ47 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"|"
              then yyQ49(strm', yyMATCH(strm, yyAction14, yyNO_MATCH))
              else yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ55 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction16(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction16(strm, yyNO_MATCH)
      (* end case *))
fun yyQ54 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyQ55(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ51 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #";"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #";"
                  then if inp = #":"
                      then yyQ54(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
and yyQ50 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ53 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction19(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction19(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                          else yyAction19(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp = #","
                  then yyAction19(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction19(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                      else yyAction19(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction19(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction19(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
              else yyAction19(strm, yyNO_MATCH)
      (* end case *))
fun yyQ52 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ46 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ53(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyQ52(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ45 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ58 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ64 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"k"
              then yyQ58(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ63 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"n"
              then yyQ64(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ62 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ63(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ61 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"l"
              then yyQ62(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
              else yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ60 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ58(strm', lastMatch)
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ58(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"]"
              then yyQ58(strm', lastMatch)
            else if inp < #"]"
              then if inp = #"\\"
                  then yystuck(lastMatch)
                  else yyQ58(strm', lastMatch)
            else if inp <= #"_"
              then yyQ58(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ65 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ58(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
            else if inp < #"0"
              then yyAction31(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ58(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
              else yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ59 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ65(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
            else if inp < #"0"
              then yyAction31(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ65(strm', yyMATCH(strm, yyAction31, yyNO_MATCH))
              else yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ57 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"c"
              then yystuck(lastMatch)
            else if inp < #"c"
              then if inp = #"\\"
                  then yyQ58(strm', lastMatch)
                else if inp < #"\\"
                  then if inp = #"#"
                      then yystuck(lastMatch)
                    else if inp < #"#"
                      then if inp = #"\""
                          then yyQ58(strm', lastMatch)
                          else yystuck(lastMatch)
                    else if inp = #"0"
                      then yyQ59(strm', lastMatch)
                    else if inp < #"0"
                      then yystuck(lastMatch)
                    else if inp <= #"9"
                      then yyQ59(strm', lastMatch)
                      else yystuck(lastMatch)
                else if inp = #"_"
                  then yystuck(lastMatch)
                else if inp < #"_"
                  then if inp = #"]"
                      then yystuck(lastMatch)
                      else yyQ60(strm', lastMatch)
                else if inp = #"a"
                  then yyQ58(strm', lastMatch)
                else if inp = #"b"
                  then yyQ61(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"r"
              then yyQ58(strm', lastMatch)
            else if inp < #"r"
              then if inp = #"g"
                  then yystuck(lastMatch)
                else if inp < #"g"
                  then if inp = #"f"
                      then yyQ58(strm', lastMatch)
                      else yystuck(lastMatch)
                else if inp = #"n"
                  then yyQ58(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"u"
              then yystuck(lastMatch)
            else if inp < #"u"
              then if inp = #"s"
                  then yystuck(lastMatch)
                  else yyQ58(strm', lastMatch)
            else if inp = #"v"
              then yyQ58(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ56 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction30(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction30(strm, yyNO_MATCH)
      (* end case *))
fun yyQ44 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction33(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\\"
              then yyQ57(strm', yyMATCH(strm, yyAction33, yyNO_MATCH))
            else if inp < #"\\"
              then if inp <= #" "
                  then yyAction33(strm, yyNO_MATCH)
                  else yyQ56(strm', yyMATCH(strm, yyAction33, yyNO_MATCH))
            else if inp <= #"\127"
              then yyQ56(strm', yyMATCH(strm, yyAction33, yyNO_MATCH))
              else yyAction33(strm, yyNO_MATCH)
      (* end case *))
fun yyQ43 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction12(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction12(strm, yyNO_MATCH)
      (* end case *))
fun yyQ42 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction11(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction11(strm, yyNO_MATCH)
      (* end case *))
fun yyQ68 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction3(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction3(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                          else yyAction3(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                else if inp = #","
                  then yyAction3(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction3(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                      else yyAction3(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction3(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction3(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
              else yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ67 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"P"
                  then yyQ68(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ66 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"O"
                  then yyQ67(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ41 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"T"
                  then yyQ66(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ71 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction7(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction7(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction7(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
                          else yyAction7(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
                else if inp = #","
                  then yyAction7(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction7(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
                      else yyAction7(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction7(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction7(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction7, yyNO_MATCH))
              else yyAction7(strm, yyNO_MATCH)
      (* end case *))
fun yyQ70 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"F"
                  then yyQ71(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ77 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction8(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction8(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction8(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                          else yyAction8(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                else if inp = #","
                  then yyAction8(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction8(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                      else yyAction8(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction8(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction8(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
              else yyAction8(strm, yyNO_MATCH)
      (* end case *))
fun yyQ76 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"D"
                  then yyQ77(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ75 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"A"
                  then yyQ76(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ74 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"O"
                  then yyQ75(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ73 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"L"
                  then yyQ74(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ72 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"_"
              then yyQ73(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ69 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"D"
                  then yyQ72(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ40 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #":"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #":"
              then if inp = #"*"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"*"
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                    else if inp <= #"'"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"-"
                  then if inp = #","
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"."
                  then yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"N"
                  then yyQ69(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"N"
                  then if inp <= #";"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"O"
                  then yyQ70(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ39 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction23(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction23(strm, yyNO_MATCH)
      (* end case *))
fun yyQ78 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction21(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction21(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction21(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
                          else yyAction21(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
                else if inp = #","
                  then yyAction21(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction21(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
                      else yyAction21(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction21(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction21(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction21, yyNO_MATCH))
              else yyAction21(strm, yyNO_MATCH)
      (* end case *))
fun yyQ38 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #">"
                  then yyQ78(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ79 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ37 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction24(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #";"
              then yyQ79(strm', yyMATCH(strm, yyAction24, yyNO_MATCH))
              else yyAction24(strm, yyNO_MATCH)
      (* end case *))
fun yyQ81 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction20(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction20(strm, yyNO_MATCH)
      (* end case *))
fun yyQ80 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ36 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction18(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #";"
              then yyAction18(strm, yyNO_MATCH)
            else if inp < #";"
              then if inp = #":"
                  then yyQ80(strm', yyMATCH(strm, yyAction18, yyNO_MATCH))
                  else yyAction18(strm, yyNO_MATCH)
            else if inp = #"="
              then yyQ81(strm', yyMATCH(strm, yyAction18, yyNO_MATCH))
              else yyAction18(strm, yyNO_MATCH)
      (* end case *))
fun yyQ82 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction22(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction22(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction22(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                          else yyAction22(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                else if inp = #","
                  then yyAction22(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction22(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
                      else yyAction22(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction22(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction22(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction22, yyNO_MATCH))
              else yyAction22(strm, yyNO_MATCH)
      (* end case *))
fun yyQ35 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"/"
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"-"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #">"
                  then yyQ82(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ34 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ33 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ32 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction9(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction9(strm, yyNO_MATCH)
      (* end case *))
fun yyQ31 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction26(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction26(strm, yyNO_MATCH)
      (* end case *))
fun yyQ83 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction15(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction15(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
                          else yyAction15(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
                else if inp = #","
                  then yyAction15(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction15(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
                      else yyAction15(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction15(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction15(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction15, yyNO_MATCH))
              else yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ30 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"-"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"-"
              then if inp = #"&"
                  then yyQ83(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"&"
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #"*"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"*"
                  then if inp = #"'"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"]"
              then yyAction29(strm, yyNO_MATCH)
            else if inp < #"]"
              then if inp = #":"
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp = #"."
                      then yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp <= #";"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ29 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"."
              then yyQ51(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"."
              then if inp = #"("
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"\""
                      then yyAction29(strm, yyNO_MATCH)
                    else if inp < #"\""
                      then if inp = #"!"
                          then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                          else yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp = #","
                  then yyAction29(strm, yyNO_MATCH)
                else if inp < #","
                  then if inp <= #")"
                      then yyAction29(strm, yyNO_MATCH)
                      else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"^"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"^"
              then if inp = #"<"
                  then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                else if inp < #"<"
                  then if inp <= #"9"
                      then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
                      else yyAction29(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp = #"|"
              then yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction29(strm, yyNO_MATCH)
                  else yyQ50(strm', yyMATCH(strm, yyAction29, yyNO_MATCH))
              else yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ28 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction32(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction32(strm, yyNO_MATCH)
      (* end case *))
fun yyQ27 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ26 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction25(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction25(strm, yyNO_MATCH)
      (* end case *))
fun yyQ24 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ25 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyQ24(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
              else yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ84 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction0(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp <= #"\a"
                  then yyAction0(strm, yyNO_MATCH)
                  else yyQ84(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp = #" "
              then yyQ84(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
              else yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ23 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction0(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp <= #"\a"
                  then yyAction0(strm, yyNO_MATCH)
                  else yyQ84(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if inp = #" "
              then yyQ84(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
              else yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ22 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction33(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction33(strm, yyNO_MATCH)
      (* end case *))
fun yyQ3 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #";"
              then yyQ37(strm', lastMatch)
            else if inp < #";"
              then if inp = #"$"
                  then yyQ22(strm', lastMatch)
                else if inp < #"$"
                  then if inp = #"\^N"
                      then yyQ22(strm', lastMatch)
                    else if inp < #"\^N"
                      then if inp = #"\n"
                          then yyQ24(strm', lastMatch)
                        else if inp < #"\n"
                          then if inp <= #"\a"
                              then yyQ22(strm', lastMatch)
                              else yyQ23(strm', lastMatch)
                        else if inp = #"\r"
                          then yyQ25(strm', lastMatch)
                          else yyQ22(strm', lastMatch)
                    else if inp = #"!"
                      then yyQ26(strm', lastMatch)
                    else if inp < #"!"
                      then if inp = #" "
                          then yyQ23(strm', lastMatch)
                          else yyQ22(strm', lastMatch)
                    else if inp = #"\""
                      then yyQ27(strm', lastMatch)
                      else yyQ28(strm', lastMatch)
                else if inp = #"*"
                  then yyQ29(strm', lastMatch)
                else if inp < #"*"
                  then if inp = #"'"
                      then yyQ31(strm', lastMatch)
                    else if inp < #"'"
                      then if inp = #"%"
                          then yyQ29(strm', lastMatch)
                          else yyQ30(strm', lastMatch)
                    else if inp = #"("
                      then yyQ32(strm', lastMatch)
                      else yyQ33(strm', lastMatch)
                else if inp = #"-"
                  then yyQ35(strm', lastMatch)
                else if inp < #"-"
                  then if inp = #","
                      then yyQ34(strm', lastMatch)
                      else yyQ29(strm', lastMatch)
                else if inp = #":"
                  then yyQ36(strm', lastMatch)
                  else yyQ29(strm', lastMatch)
            else if inp = #"\\"
              then yyQ29(strm', lastMatch)
            else if inp < #"\\"
              then if inp = #"E"
                  then yyQ40(strm', lastMatch)
                else if inp < #"E"
                  then if inp = #">"
                      then yyQ29(strm', lastMatch)
                    else if inp < #">"
                      then if inp = #"<"
                          then yyQ29(strm', lastMatch)
                          else yyQ38(strm', lastMatch)
                    else if inp = #"?"
                      then yyQ39(strm', lastMatch)
                      else yyQ29(strm', lastMatch)
                else if inp = #"T"
                  then yyQ29(strm', lastMatch)
                else if inp < #"T"
                  then if inp = #"S"
                      then yyQ41(strm', lastMatch)
                      else yyQ29(strm', lastMatch)
                else if inp = #"["
                  then yyQ42(strm', lastMatch)
                  else yyQ29(strm', lastMatch)
            else if inp = #"{"
              then yyQ45(strm', lastMatch)
            else if inp < #"{"
              then if inp = #"`"
                  then yyQ44(strm', lastMatch)
                else if inp < #"`"
                  then if inp = #"]"
                      then yyQ43(strm', lastMatch)
                      else yyQ29(strm', lastMatch)
                  else yyQ29(strm', lastMatch)
            else if inp = #"~"
              then yyQ48(strm', lastMatch)
            else if inp < #"~"
              then if inp = #"|"
                  then yyQ46(strm', lastMatch)
                  else yyQ47(strm', lastMatch)
              else yyQ22(strm', lastMatch)
      (* end case *))
fun yyQ2 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ20 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ21 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyQ20(strm', yyMATCH(strm, yyAction40, yyNO_MATCH))
              else yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ19 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction41(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction41(strm, yyNO_MATCH)
      (* end case *))
fun yyQ1 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\v"
              then yyQ19(strm', lastMatch)
            else if inp < #"\v"
              then if inp = #"\n"
                  then yyQ20(strm', lastMatch)
                  else yyQ19(strm', lastMatch)
            else if inp = #"\r"
              then yyQ21(strm', lastMatch)
              else yyQ19(strm', lastMatch)
      (* end case *))
fun yyQ11 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ17 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"k"
              then yyQ11(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ16 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"n"
              then yyQ17(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ15 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ16(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ14 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"l"
              then yyQ15(strm', yyMATCH(strm, yyAction36, yyNO_MATCH))
              else yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ13 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"@"
              then yyQ11(strm', lastMatch)
            else if inp < #"@"
              then if inp = #"/"
                  then yyQ11(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"]"
              then yyQ11(strm', lastMatch)
            else if inp < #"]"
              then if inp = #"\\"
                  then yystuck(lastMatch)
                  else yyQ11(strm', lastMatch)
            else if inp <= #"_"
              then yyQ11(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ18 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ11(strm', yyMATCH(strm, yyAction36, yyNO_MATCH))
            else if inp < #"0"
              then yyAction36(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ11(strm', yyMATCH(strm, yyAction36, yyNO_MATCH))
              else yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ12 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ18(strm', yyMATCH(strm, yyAction36, yyNO_MATCH))
            else if inp < #"0"
              then yyAction36(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ18(strm', yyMATCH(strm, yyAction36, yyNO_MATCH))
              else yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ10 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction39(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"c"
              then yyAction39(strm, yyNO_MATCH)
            else if inp < #"c"
              then if inp = #"\\"
                  then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                else if inp < #"\\"
                  then if inp = #"#"
                      then yyAction39(strm, yyNO_MATCH)
                    else if inp < #"#"
                      then if inp = #"\""
                          then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                          else yyAction39(strm, yyNO_MATCH)
                    else if inp = #"0"
                      then yyQ12(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction39(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ12(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                      else yyAction39(strm, yyNO_MATCH)
                else if inp = #"_"
                  then yyAction39(strm, yyNO_MATCH)
                else if inp < #"_"
                  then if inp = #"]"
                      then yyAction39(strm, yyNO_MATCH)
                      else yyQ13(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                else if inp = #"a"
                  then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                else if inp = #"b"
                  then yyQ14(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                  else yyAction39(strm, yyNO_MATCH)
            else if inp = #"r"
              then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
            else if inp < #"r"
              then if inp = #"g"
                  then yyAction39(strm, yyNO_MATCH)
                else if inp < #"g"
                  then if inp = #"f"
                      then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                      else yyAction39(strm, yyNO_MATCH)
                else if inp = #"n"
                  then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
                  else yyAction39(strm, yyNO_MATCH)
            else if inp = #"u"
              then yyAction39(strm, yyNO_MATCH)
            else if inp < #"u"
              then if inp = #"s"
                  then yyAction39(strm, yyNO_MATCH)
                  else yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
            else if inp = #"v"
              then yyQ11(strm', yyMATCH(strm, yyAction39, yyNO_MATCH))
              else yyAction39(strm, yyNO_MATCH)
      (* end case *))
fun yyQ9 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction34(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction34(strm, yyNO_MATCH)
      (* end case *))
fun yyQ8 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction35(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction35(strm, yyNO_MATCH)
      (* end case *))
fun yyQ7 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction37(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction37(strm, yyNO_MATCH)
      (* end case *))
fun yyQ5 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ6 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyQ5(strm', yyMATCH(strm, yyAction38, yyNO_MATCH))
              else yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ4 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction39(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction39(strm, yyNO_MATCH)
      (* end case *))
fun yyQ0 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"!"
              then yyQ8(strm', lastMatch)
            else if inp < #"!"
              then if inp = #"\r"
                  then yyQ6(strm', lastMatch)
                else if inp < #"\r"
                  then if inp = #"\n"
                      then yyQ5(strm', lastMatch)
                      else yyQ4(strm', lastMatch)
                else if inp = #" "
                  then yyQ7(strm', lastMatch)
                  else yyQ4(strm', lastMatch)
            else if inp = #"\\"
              then yyQ10(strm', lastMatch)
            else if inp < #"\\"
              then if inp = #"\""
                  then yyQ9(strm', lastMatch)
                  else yyQ8(strm', lastMatch)
            else if inp <= #"\127"
              then yyQ8(strm', lastMatch)
              else yyQ4(strm', lastMatch)
      (* end case *))
in
  (case (!(yyss))
   of STRING => yyQ0(!(yystrm), yyNO_MATCH)
    | EOL_COMMENT => yyQ1(!(yystrm), yyNO_MATCH)
    | tates => yyQ2(!(yystrm), yyNO_MATCH)
    | INITIAL => yyQ3(!(yystrm), yyNO_MATCH)
  (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
