(*======================================================================

Some basic/generic utility functions. 

=======================================================================*)

signature BASIC = 
sig 
    val != : ''a * ''a -> bool
    val listEq: 'a list * 'a list * ('a * 'a ->bool)  -> bool
    val readFileLines: string -> string list
    val writeLinesToFile: string list * string -> unit
    val replaceFile: string * string -> unit
    val isDir: string -> bool 
    val tokenize: string * char list -> string list 
    val replaceSubstring: string * string * string -> string 
    val listDirFilesRecursively: string -> string list    
    val readAllDirFiles: string -> string list 				    
    val countLines: string -> int 
    val allEqual: ''a list -> bool 
    val bool2Str : bool -> string
    val isMember : ''a * ''a list -> bool
    val isMemberEq : 'a * 'a list * ('a * 'a -> bool)  ->bool
    val subsetEq: ('a list * 'a list * ('a * 'a -> bool)) -> bool
    val listDiff: ('a list * 'a list * ('a * 'a -> bool)) -> 'a list 
    val listUnion: ('a list * 'a list * ('a * 'a -> bool)) -> 'a list 
    val removeDuplicatesEq: 'a list * ('a * 'a -> bool) -> 'a list
    val removeStringDuplicates: string list -> string list
    val hasDuplicates: 'a list * ('a * 'a -> bool) -> bool 
    val inc: int ref -> unit
    val incAndReturn: int ref -> int 
    val returnAndInc: int ref -> int 
    val dec: int ref -> unit
    val writeStringToCharArray: string * CharArray.array * int -> int
    val readLine: unit -> string
    val printable: char -> bool
    val promptAndReadLine: string -> string
    val stripLast: string -> string
    val allButLast: 'a list -> 'a list 
    val allButLastAndLast: 'a list -> 'a list * 'a 
    val writeString: string * char Array.array * int -> int 
    val remove : ''a * ''a list -> ''a list
    val removeAll : ''a list * ''a list -> ''a list
    val removeAllEq : 'a list * 'a list * ('a * 'a -> bool) -> 'a list
    val removeEq : 'a * 'a list * ('a * 'a ->bool) -> 'a list
    val removeAndCheckMemEq : 'a * 'a list * ('a * 'a ->bool) -> ('a list * bool)
    val zip : 'a list * 'b list -> ('a * 'b) list
    val strictZip : 'a list * 'b list -> ('a * 'b) list
    val unZip: ('a * 'b) list -> 'a list * 'b list 
    val filter: 'a list * ('a -> bool) -> 'a list
    val filterOut: 'a list * ('a -> bool) -> 'a list
    val prefix: ''a list * ''a list -> bool 
    val prefixEq: 'a list * 'a list * ('a * 'a ->bool) -> bool 
    val nonEmptyCommonprefixEq: 'a list * 'a list * ('a * 'a ->bool) -> bool 
    val suffix: ''a list * ''a list ->bool 
    val nth: 'a list * int -> 'a
    val pow: int * int -> int 
    val exists: 'a list * ('a -> bool) -> bool
    val constructiveExists: 'a list * ('a -> bool) -> 'a option
    val take: 'a list * int -> 'a list 
    val findInList: 'a list * ('a -> bool) -> 'a option
    val findInListCont: ('a list * ('a -> bool) * ('a -> 'b) * (unit -> 'b)) -> 'b 
    val findAndSplit: 'a list * ('a -> bool) * ('a * 'a -> bool) -> ('a option * 'a list)
    val countAll: 'a list * ('a -> bool) -> int 
    val forall: 'a list * ('a -> bool) ->bool
    val removeListChunk: 'a list * int * int -> ('a list * 'a list * 'a list)
    val id: ('a -> 'a) 
    val flatten: 'a list list -> 'a list
    val doubleMap:  ('b -> 'c) * ('a -> 'b) * 'a list -> 'c list
    val mapSelect:  ('a -> 'b) * 'a list * ('b -> bool) -> 'b list 
    val mapTry:  ('a -> 'b) * 'a list -> 'b list 
    val mapWithIndex:  ((('a * int) -> 'b) * 'a list) -> 'b list
    val appWithIndex: (('a * int) -> unit) * ('a list) -> unit 
    val firstNumbersFast: int * int -> int list 
    val concatStrings: string list -> string
    val maxLst: int list -> int 
    val printList: 'a list * ('a -> string) -> unit
    val printListStrCommas: 'a list * ('a -> string) -> string 
    val printListStr: 'a list * ('a -> string) * string -> string 
    val printSExpList: 'a list * ('a -> string) -> unit
    val printSExpListStr: 'a list * ('a -> string) -> string 
    val printLnList: 'a list * ('a -> string) -> unit
    val printLnListStr: 'a list * ('a -> string) -> string
    val continue: unit -> unit 
    val spaces: int -> string 
    val isPrintable: char -> bool
    val isAlpha: char -> bool
    val isDigit: char -> bool
    val isAlphaNum: char -> bool
    val isWhiteSpace: char -> bool
    val isThereLineThatStartsWith: TextIO.instream * string -> bool * int
    val findAndSkipLine: TextIO.instream * string -> char list
    val skipWhiteSpace: char list -> char list 
    val skipAll: 'a list * ('a -> bool) -> 'a list
    val skipAllAndReturnCount: 'a list * ('a -> bool) -> int 
    val skipUntil: 'a list * ('a -> bool) -> ('a list * 'a list)    
    val skipUntilRev: 'a list * ('a -> bool) -> ('a list * 'a list)
    val skipUntilWithExtendedPred: 'a list * ('a -> bool) * ('a list -> bool) -> ('a list * 'a list)
    val firstPast: string * (char -> bool) -> int
    val toLower: string -> string
    val toUpper: string -> string 
    val nrev: 'a list -> 'a list
    val hashChar: char * Word.word -> Word.word
    val hashString: string -> Word.word
    val hashInt: int -> Word.word
    val hashList: 'a list * Word.word * ('a -> string) -> Word.word
    val hashPair: int * int -> Word.word 
    val hashTwoWords: Word.word * Word.word -> Word.word
    val hashWordList: 'a list * ('a -> Word.word) -> Word.word
    val hashIntList: int list -> Word.word
    val hashAccum: string * Word.word * int -> Word.word * int 
    val hashAccumInt: int * Word.word * int -> Word.word * int 
    val varRenamer: string -> string
    val fsymRenamer: string -> string
    val arrayToList: 'a array -> 'a list
    val findInArray: (('a -> bool) * 'a array) -> ((int * 'a) option)
    val makeTailList: 'a array * int -> 'a list 
    val listReplace: 'a list * int * 'a -> 'a list 
    val repeat: int -> (int -> 'a) -> unit
    val timeIt: (unit -> unit) -> Real.real 
    val timeOut: ('a -> 'b) * int -> (('a -> ('b option)))
    val decomposeList: ('a list * ('a -> bool)) -> ('a list * 'a * 'a list) option
    val decomposeNth: 'a list * int -> ('a option * 'a list)
    val takeAndSplit: 'a list * int -> 'a list * 'a list 
    exception Never
    val never: unit -> unit 
    exception FailLst of string list
    exception Fail of string
    val fail: string -> 'a
    val failLst: string list -> 'a
    val fromI2N: int * int -> int list;
    val removeFromSortedList: 'a * 'a list * (('a * 'a) -> order) -> 'a list    
    val insertIntoSortedList: 'a * 'a list * (('a * 'a) -> order) -> 'a list 
    val removeAndInsertInSortedList: 'a * 'a * 'a list * ('a * 'a -> order) -> 'a list
    val findInSorted: 'a * 'a list * (('a * 'a) -> order) -> bool
    val mergeSort: 'a list * ('a * 'a -> bool) -> 'a list
    val mergeSortBuiltIn: 'a list * ('a * 'a -> bool) -> 'a list
    val mergeSortBuiltInComp: 'a list * ('a * 'a -> bool) -> 'a list
    val merge: 'a list * 'a list * ('a * 'a -> bool) -> 'a list
    val isSorted: 'a list * ('a * 'a -> bool) -> bool
    val newline: string
    val lparen: string
    val rparen: string
    val lbrack: string
    val rbrack: string
    val lbrace: string
    val rbrace: string
    val blank: string
    val comma: string
    val period: string
    val colon: string
    val new_line: string    
    val string_quote: string
    val semi_colon: string
    val foldr : ('a * 'b -> 'b) * 'b * 'a list -> 'b    
    val mark: string -> unit 
    val copies: string * int -> string
    val failMsgsToStr: string list -> string 
    val oneLine: string -> bool
    val boolToString: bool -> string
    val first: 'a list -> 'a
    val second: 'a list -> 'a
    val third: 'a list -> 'a
    val countParens: string -> {lparens:int,rparens:int}
    val stringContains: string * (char -> bool) -> bool 
    val getBalancedLine: TextIO.instream -> string 
    val lexOrder: 'a list * 'a list * ('a * 'a -> order) -> order
    val escape: string -> string 
    val downcaseChar: char -> char
    val downcaseString: string -> string
end
