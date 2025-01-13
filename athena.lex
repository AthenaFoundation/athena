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
%%
%header (functor AthenaLexFun(structure Tokens:Athena_TOKENS));
%states STRING EOL_COMMENT;
alpha = [A-Za-z];
digit = [0-9];
alpha_num = {alpha} | {digit}; 
printable_minus_backslash = [\033-\091] | [\093-\127];
init_ide_char =   \037 | \038 | [\042-\043] | [\045-\057] | [\060-\062] | [\064-\090] 
               | \092 | \094 | \095 | [\097-\122] | \124;

init_ide_char_no_dot =   \037 | \038 | [\042-\043] | \045 | [\047-\057] | [\060-\062] | [\064-\090] 
                       | \092 | \094 | \095 | [\097-\122] | \124;
back_slash = \092;
back_quote = \096;
string_quote = \034;
blank = \032;
escape_character = \092 | \097 | \098 | \110 | \114 | \102 | \116 | \118 | \034;
control_character = \094;
quote_character = \039;
colon_character = \058;
dot_character = \046;
control_letter = [\065-\090] | \064 | \091 | \093 | \047 | \094 | \095;
internal_ide_char = \033 | [\035-\039] | [\042-\043] | [\045-\057] | [\060-\092] | \094 | [\095-\122] | \124;
internal_ide_char_allowing_colon = \033 | [\035-\039] | [\042-\043] | [\045-\058] | [\060-\092] | \094 | [\095-\122] | \124;
internal_ide_char_no_dot = \033 | [\035-\039] | [\042-\043] | \045 | [\047-\057] | [\060-\092] | \094 | [\095-\122] | \124;
ide_char =  ' | _ | - | \094 | \035 | \038 | \063 | \042 | {alpha_num};
identifier = {init_ide_char}{internal_ide_char}*;
identifier_with_no_dots = {init_ide_char_no_dot}{internal_ide_char_no_dot}*;
identifier_with_dot_double_colon = {init_ide_char}{internal_ide_char}*{dot_character}{colon_character}{colon_character};
meta_identifier = {quote_character}{identifier};
non_neg_integer = {digit}+;
blank_kwd = \098\108\097\110\107;
one_two_or_three_digits = {digit} | {digit}{digit} | {digit}{digit}{digit};
escape_seq = {back_slash}{one_two_or_three_digits} | {back_slash}{escape_character} |
             {back_slash}{control_character}{control_letter} |
             {back_slash}{blank_kwd};
character1 = {back_quote}{printable_minus_backslash};
character2 = {back_quote}{escape_seq};
non_neg_number = {non_neg_integer} | {non_neg_integer}.{non_neg_integer};
number = {non_neg_number} | -{non_neg_number};
object_type_var = #{identifier};
type_var = ##{identifier};
white_space = [\ \t\b];
printable_and_non_paren = [\033-\039] | [\042-\127];
cr="\013";
nl="\010";
eol=({cr}{nl}|{nl}|{cr});
%%
<INITIAL>{white_space}+ => (incPos(size(yytext));continue());
<INITIAL>{eol} => (incLines();continue());
<INITIAL>"\"" => (incPos(1);begin_string_pos := (!lines,!pos);
                 open_string := true;temp_string := "";
                  YYBEGIN STRING; continue());
<INITIAL>"STOP" => (incPos(4);resetLines();Tokens.EOF(currentPos(),dxCurrentPos(3)));
<INITIAL>"|{" => (incPos(2);Tokens.MAP_BEGIN(currentPos(),dxCurrentPos(1)));
<INITIAL>"}|" => (incPos(2);Tokens.MAP_END(currentPos(),dxCurrentPos(1)));
<INITIAL>";;" => (incPos(2);Tokens.EOF(currentPos(),dxCurrentPos(1)));
<INITIAL>"EOF" => (incPos(3);resetLines();Tokens.EOF(currentPos(),dxCurrentPos(2)));
<INITIAL>"END_LOAD" => (incPos(8);Tokens.EOF(currentPos(),dxCurrentPos(7)));
<INITIAL>"(" => (incPos(1);Tokens.LPAREN(currentPos(),dxCurrentPos(0)));
<INITIAL>")" => (incPos(1);Tokens.RPAREN(currentPos(),dxCurrentPos(0)));
<INITIAL>"[" => (incPos(1);Tokens.LEFT_BRACKET(currentPos(),dxCurrentPos(0)));
<INITIAL>"]" => (incPos(1);Tokens.RIGHT_BRACKET(currentPos(),dxCurrentPos(0)));
<INITIAL>"{" => (incPos(1);Tokens.LEFT_CURLY_BRACE(currentPos(),dxCurrentPos(0)));
<INITIAL>"}" => (incPos(1);Tokens.RIGHT_CURLY_BRACE(currentPos(),dxCurrentPos(0)));
<INITIAL>"&&" => (incPos(2);Tokens.LOGICAL_AND(currentPos(),dxCurrentPos(1)));
<INITIAL>{identifier_with_dot_double_colon} => (let val res = doId(yytext,dxCurrentPos(1))
                          in
                             (incPos(size(yytext));res) 
                          end);
<INITIAL>"::" => (incPos(2);Tokens.ID("::",currentPos(),dxCurrentPos(0)));
<INITIAL>":" => (incPos(1);Tokens.COLON(currentPos(),dxCurrentPos(0)));
<INITIAL>"||" => (let val res = Tokens.LOGICAL_OR(currentPos(),dxCurrentPos(1))
                     in (incPos(1);res) end);
<INITIAL>":=" => (let val res = Tokens.ASGN(currentPos(),dxCurrentPos(1))
                  in (incPos(2);res) end);
<INITIAL>"=>" => (let val res = Tokens.ARROW(currentPos(),dxCurrentPos(1))
                  in (incPos(2);res) end);
<INITIAL>"->" => (let val res = Tokens.FUN_ARROW(currentPos(),dxCurrentPos(1))
                  in (incPos(2);res) end);
<INITIAL>"?" => (incPos(1);Tokens.QMARK(currentPos(),dxCurrentPos(0)));
<INITIAL>";" => (incPos(1);Tokens.SEMI_COLON(currentPos(),dxCurrentPos(0)));
<INITIAL>"!" => (incPos(1);Tokens.EXCL_MARK(currentPos(),dxCurrentPos(0)));
<INITIAL>"'" => (incPos(1);Tokens.QUOTE_SYMBOL(currentPos(),dxCurrentPos(0)));
<INITIAL>"~" => (incPos(1);Tokens.ID("~",currentPos(),dxCurrentPos(0)));
<INITIAL>"," => (incPos(1);Tokens.COMMA(currentPos(),dxCurrentPos(0)));
<INITIAL>{identifier} => (let val res = doId(yytext,dxCurrentPos(1))
                          in
                             (incPos(size(yytext));res) 
                          end);
<INITIAL>{character1} => (incPos(1);
                          let val res = Tokens.CHARACTER(ord(hd(tl(explode(yytext)))),
                                                         currentPos(),dxCurrentPos(1))
                              val _ = incPos(1) 
                          in res 
                          end);
<INITIAL>{character2}=> (let val code = getEscChar(tl(explode(yytext)))
                             val res = Tokens.CHARACTER(code,dxCurrentPos(1),
                                                        dxCurrentPos(size(yytext)))
                             val _ = incPos(size(yytext)) in res end);
<INITIAL>"#" => (incPos(1);YYBEGIN EOL_COMMENT; continue());
<INITIAL>. => (incPos(size(yytext));
               if ord(hd(explode(yytext))) = 96 then 
                  error("Illegal character constant: "^yytext,SOME(currentPosWithFileInfo()))
               else error("Illegal character found and ignored: "^yytext,SOME(currentPosWithFileInfo()));
               continue());
<STRING>{string_quote} => (YYBEGIN INITIAL; 
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
                           end);
<STRING>{printable_minus_backslash} => 
      (code_string := !code_string^yytext;
       incPos(size(yytext));
       char_code_list := ord(hd(explode(yytext)))::(!char_code_list);
       continue());
<STRING>{escape_seq} => 
      (code_string := !code_string^yytext;
       incPos(size(yytext));
       char_code_list := getEscChar(explode(yytext))::(!char_code_list);
       continue());
<STRING>{blank} =>
      (code_string := !code_string^yytext;
       incPos(1);
       char_code_list := 32::(!char_code_list);
       continue());
<STRING>{eol} =>  (code_string := !code_string^yytext; 
                incLines(); 
                continue());
<STRING>. => (incPos(size(yytext));
              error("Illegal character found inside string constant: "^yytext,
                    SOME(currentPosWithFileInfo()));
              continue());
<EOL_COMMENT>{eol} => (incLines();YYBEGIN INITIAL;continue());
<EOL_COMMENT>. => (incPos(size(yytext));continue());



