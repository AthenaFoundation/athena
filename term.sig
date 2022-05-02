(*======================================================================

A generic signature for terms, parameterized over variables and function symbols.

=======================================================================*)

signature TERM = 

sig

   type variable

   type fsymbol

   datatype label = varLabel of variable | fsymLabel of fsymbol | noLabel;

   type term 

   type 'a tagged_term

   exception Subterm

   val getLabel: term * int list -> label

   val makeTaggedVar: variable * 'a -> 'a tagged_term

   val makeTaggedConstant: fsymbol * 'a -> 'a tagged_term

   val makeTaggedApp: fsymbol * 'a * ('a tagged_term list) -> 'a tagged_term 

   val isTaggedConstant: 'a tagged_term -> (fsymbol * 'a) option

   val isTaggedApp: 'a tagged_term -> (fsymbol * 'a * (('a tagged_term) list)) option

   val isTaggedVar: 'a tagged_term -> (variable * 'a) option

   val getTopTag: 'a tagged_term -> 'a

   val getTag: 'a tagged_term * int list -> 'a 

   val getNthTaggedSubterm: 'a tagged_term * int list -> 'a tagged_term


   val stripTags: 'a tagged_term ->term

   val varEq: variable * variable -> bool  (* Equality predicate on variables *)

   val fsymEq: fsymbol * fsymbol -> bool   (* Equality predicate on function symbols *)

   val termEq: term * term -> bool         (* Equality predicate on terms *)

   val getDom: term -> int list list;

   val getVDom: term -> int list list;

   val getFDom: term -> int list list;

   val makeVar: variable -> term

   val makeConstant: fsymbol -> term

   val makeApp: fsymbol * term list -> term

   val isVar: term -> variable option

   val isConstant: term -> fsymbol option

   val isApp: term -> (fsymbol * term list) option

   val isGround: term -> bool

   val varOccursIn: variable * term -> bool

   val fsymOccursIn: fsymbol * term -> bool

   val fsymOccursInTagged: fsymbol * 'a tagged_term -> bool

   val transform: (fsymbol -> fsymbol) -> 'a tagged_term -> 'a tagged_term

   val isLegal: term * (fsymbol -> int option) * (variable -> bool) -> bool

   val areLegal: term list * (fsymbol -> int option) * (variable -> bool) -> bool

   val isTaggedLegal: 'a tagged_term * (fsymbol -> int option) * (variable -> bool) -> 'a option

   val areTaggedLegal: 'a tagged_term list * (fsymbol -> int option) * (variable -> bool) 
                       -> 'a option

   val getVars: term -> variable list

   val getVarsLst: term list -> variable list

   val getNthSubterm: term * int list -> term

   val replace: variable * term * term -> term

(* The call replace(v,t1,t2) replaces every occurence of the   *)
(* variable v in t2 by the term t1. Thus it should be read as  *)
(*  "replace v by t1 in t2".                                   *)

   val replaceSubterm: term * int list * term -> term

(* The call replaceSubterm(t,pos,new_part) returns the term obtained *)
(* from t by replacing the subterm rooted at pos by new_part         *)
(* The Subterm exception is raised if pos is not in Dom(t).          *)

   type sub

   val empty_sub: sub

   val incSub: sub * (variable * term) -> sub

   val extendSub: sub * (variable * term) list -> sub

   val makeSub: (variable * term) list -> sub

   val inSupp: variable * sub -> bool

   val applySub: sub * term -> term

   val applySubLst: sub * term list -> term list

   val composeSubs: sub * sub -> sub
 
   val match: term * term -> sub option

   exception UniFailure;

   val unify: term * term -> sub option 

   val height: term -> int 

   val toPrettyString: int * term * (variable -> string) -> string 
   val toString: term * (variable -> string) -> string 
   val toStringDefault: term  -> string 

   val taggedTermToString: 'a tagged_term -> string 

   val unifyLst: term list * term list -> sub option 

   val unifyEx: term * term -> sub

   val unifyExLst: term list * term list -> sub

   val getOccurences: term * term -> int list list

(* The call getOccurences(t1,t2) returns a list of all and only   *)
(* those positions in Dom(t2) such that t1 occurs in t2 at those  *)
(* positions.                                                     *)

end;
